//! Buchberger's algorithm and the Ideal abstraction.
//!
//! Implementation notes (designed to match CoCoA's strategy from the start):
//!
//! * **One-at-a-time S-pair processing** (D1) — pop the single lowest-sugar pair per iteration.
//! * **`(sugar, lcm_deg, age)` ordering** for the priority queue.
//! * **Non-strict basis deactivation** (D3) — when adding a new element, deactivate
//!   any existing element whose leading monomial is divisible (not strictly) by the new one.
//! * **End-only inter-reduction** (D5) — perform a single inter-reduction pass after
//!   the main loop terminates.
//! * **No restart heuristic** (D6) — never restart.
//! * **DivMask** acceleration for fast divisibility rejection.
//! * **Sugar degree** with running updates during reduction (GMNR style).
//! * **Gebauer-Möller M-criterion + product criterion** for S-pair pruning at
//!   pair-generation time (CoCoA `myGMInsert`, `myBuildNewPairs`).

use std::sync::Arc;

use crate::timeout::CancelToken;
use crate::SolverError;

use super::divmask::DivMask;
use super::field::FieldElem;
#[cfg(test)]
use super::field::PrimeField;
use super::monomial::{Monomial, MonomialOrder};
use super::polynomial::{PolyRing, Polynomial};
use super::spair::SPair;

/// Configuration for `groebner_basis`.
#[derive(Clone)]
pub struct BuchbergerConfig {
    pub order: MonomialOrder,
    pub cancel_token: Option<CancelToken>,
    /// Stop early if the basis contains a nonzero constant (i.e. the ideal is the whole ring).
    pub abort_on_trivial: bool,
}

impl Default for BuchbergerConfig {
    fn default() -> Self {
        BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: true,
        }
    }
}

/// A computed Groebner basis.
#[derive(Clone, Debug)]
pub struct GBasis {
    pub basis: Vec<Polynomial>,
    pub order: MonomialOrder,
}

/// Observer hook for tracking the polynomial dependency DAG (used by the UNSAT-core tracer).
pub trait BuchbergerObserver {
    /// Called immediately before [`on_initial_basis`] to report the indices
    /// of basis elements that were potentially used as reducers when the
    /// new generator was reduced into normal form. Observers that wish to
    /// over-approximate dependencies can union the deps of these reducers
    /// into the new entry.
    fn on_initial_reducers(&mut self, _reducer_indices: &[usize]) {}
    fn on_initial_basis(&mut self, _idx: usize, _poly: &Polynomial) {}
    fn on_new_poly(&mut self, _idx: usize, _poly: &Polynomial, _from_pair: (usize, usize)) {}
    fn on_inter_reduce(&mut self, _old_idx: usize, _new_idx: usize) {}
}

/// No-op observer.
pub struct NoObserver;
impl BuchbergerObserver for NoObserver {}

/// Internal basis element.
#[derive(Clone, Debug)]
struct BasisElement {
    poly: Polynomial,
    lt: Monomial,
    #[allow(dead_code)] // reserved for future Gebauer-Möller chain criterion
    lt_divmask: DivMask,
    /// Lazily deactivated when superseded by a smaller-LT element.
    active: bool,
    /// Sugar degree at the time this element was added.
    sugar: u32,
}

// ─────────────────────────── Public entry points ───────────────────────────

/// Compute a Groebner basis of `generators` from scratch.
pub fn groebner_basis(
    generators: Vec<Polynomial>,
    ring: &Arc<PolyRing>,
    config: &BuchbergerConfig,
) -> Result<GBasis, SolverError> {
    let mut state = BuchbergerState::new(ring.clone(), config.clone());
    let mut obs = NoObserver;
    state.add_generators(generators, &mut obs)?;
    state.run(&mut obs)?;
    let basis = state.finalize_basis();
    Ok(GBasis { basis, order: ring.order })
}

/// Run Buchberger with an observer (for UNSAT-core tracing).
pub fn groebner_basis_observed<O: BuchbergerObserver>(
    generators: Vec<Polynomial>,
    ring: &Arc<PolyRing>,
    config: &BuchbergerConfig,
    observer: &mut O,
) -> Result<GBasis, SolverError> {
    let mut state = BuchbergerState::new(ring.clone(), config.clone());
    state.add_generators(generators, observer)?;
    state.run(observer)?;
    let basis = state.finalize_basis();
    Ok(GBasis { basis, order: ring.order })
}

/// Extend an existing GB with new generators (re-run Buchberger from the existing basis).
pub fn groebner_basis_incremental(
    existing: GBasis,
    new_generators: Vec<Polynomial>,
    ring: &Arc<PolyRing>,
    config: &BuchbergerConfig,
) -> Result<GBasis, SolverError> {
    let mut all = existing.basis;
    all.extend(new_generators);
    groebner_basis(all, ring, config)
}

/// Inter-reduce a basis (make every element's tail reduced w.r.t. all others; make monic).
pub fn interreduce(mut basis: Vec<Polynomial>, ring: &Arc<PolyRing>) -> Vec<Polynomial> {
    // Drop zeros and constants > 0 collapse to {1}.
    basis.retain(|p| !p.is_zero());
    // If any constant is present, the ideal is the whole ring.
    if basis.iter().any(|p| p.is_constant()) {
        return vec![Polynomial::constant(ring.field.one(), ring)];
    }
    // Make monic.
    for p in basis.iter_mut() {
        *p = p.make_monic(ring);
    }
    // Sort by leading monomial (descending) for deterministic output.
    basis.sort_by(|a, b| {
        let la = a.leading_monomial(ring).unwrap();
        let lb = b.leading_monomial(ring).unwrap();
        lb.cmp_with_order(&la, ring.order)
    });
    // Drop any element whose LT is divisible by another's LT.
    let mut keep = vec![true; basis.len()];
    for i in 0..basis.len() {
        if !keep[i] { continue; }
        let li = basis[i].leading_monomial(ring).unwrap();
        for j in 0..basis.len() {
            if i == j || !keep[j] { continue; }
            let lj = basis[j].leading_monomial(ring).unwrap();
            // Drop j if li strictly divides lj (and both are different)
            if li.divides(&lj) && li != lj {
                keep[j] = false;
            }
        }
    }
    let mut filtered: Vec<Polynomial> = basis
        .into_iter()
        .zip(keep.iter())
        .filter_map(|(p, &k)| if k { Some(p) } else { None })
        .collect();
    // Tail reduction: reduce each polynomial by the others until stable.
    //
    // Performance note: previously this allocated a fresh `Vec<Polynomial>`
    // of all "other" basis elements on every i (an `O(n²)` clone-storm per
    // pass). We now use `reduce_by_refs` with a `Vec<&Polynomial>` that
    // skips index `i` — zero polynomial clones for the divisor list.
    let mut changed = true;
    let max_passes = filtered.len().max(2) * 2;
    let mut pass = 0;
    while changed && pass < max_passes {
        changed = false;
        pass += 1;
        for i in 0..filtered.len() {
            let others: Vec<&Polynomial> = filtered.iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, p)| p)
                .collect();
            let red = filtered[i].reduce_by_refs(&others, ring);
            if !poly_eq(&red, &filtered[i]) {
                filtered[i] = if !red.is_zero() {
                    red.make_monic(ring)
                } else {
                    Polynomial::zero()
                };
                changed = true;
            }
        }
        filtered.retain(|p| !p.is_zero());
    }
    filtered
}

fn poly_eq(a: &Polynomial, b: &Polynomial) -> bool {
    if a.num_terms() != b.num_terms() { return false; }
    if a.is_zero() && b.is_zero() { return true; }
    // Compare via term iteration (terms are in canonical descending order).
    // We don't have a ring here; leverage internal equality via debug repr would be ugly.
    // Use Polynomial's clone+sub trick? We do have a comparator: build via raw compare
    // using PartialEq on (coeffs, exponents, total_degs). Add a private accessor.
    a.struct_eq(b)
}

// Add a structural equality helper to Polynomial via a free function (uses `pub(crate)` accessors).
impl Polynomial {
    pub(crate) fn struct_eq(&self, other: &Polynomial) -> bool {
        // We compare canonical fields. Both polynomials must have equal lengths and same data.
        // Field elements compare via PartialEq (canonical BigUint).
        self.num_terms() == other.num_terms()
            && self.public_exponents() == other.public_exponents()
            && self.public_coeffs() == other.public_coeffs()
    }
}

// ──────────────────── S-pair queue helpers (GM, merge) ────────────────────

/// Gebauer-Möller M-criterion insertion (CoCoA `myGMInsert`,
/// TmpGReductor.C:448-482).
///
/// In the M-criterion a pair with a *smaller* lcm dominates pairs with
/// larger lcms — `lcm(LT_a, LT_b)` dividing `lcm(LT_c, LT_d)` means the
/// (a,b) pair makes (c,d) redundant. So:
///   * If `LCM(existing) | LCM(P)`: existing dominates P, P is dropped.
///     Special case (LCMs equal): if existing is non-coprime and P is
///     coprime, replace existing with P. Coprime pairs get dropped by the
///     product criterion downstream, so swapping a non-coprime owner for a
///     coprime one for the same lcm eliminates the work entirely
///     (CoCoA TmpGReductor.C:464-468).
///   * Else if `LCM(P) | LCM(existing)`: P dominates existing, erase
///     existing.
///
/// On exit the list is left in arbitrary order; callers sort it before
/// merging.
fn gm_insert(list: &mut Vec<SPair>, pair: SPair) {
    let mut to_insert = Some(pair);
    let mut dominated = false;
    let mut idx = 0;
    while idx < list.len() {
        let p_ref = match &to_insert {
            Some(p) => p,
            None => break,
        };
        let existing = &list[idx];
        // Existing dominates P iff LCM(existing) divides LCM(P).
        let existing_dominates =
            existing.lcm_divmask.divides_consistent_with(p_ref.lcm_divmask)
                && existing.lcm.divides(&p_ref.lcm);
        if existing_dominates {
            let same_lcm = p_ref.lcm == existing.lcm;
            if same_lcm && !existing.is_coprime && p_ref.is_coprime {
                list[idx] = to_insert.take().unwrap();
            }
            dominated = true;
            break;
        }
        // Otherwise check if P strictly dominates existing.
        let p_dominates =
            p_ref.lcm_divmask.divides_consistent_with(existing.lcm_divmask)
                && p_ref.lcm.divides(&existing.lcm);
        if p_dominates {
            // P strictly dominates (equality was handled above). Erase
            // existing without advancing idx — swap_remove brings a
            // not-yet-checked element into position idx.
            list.swap_remove(idx);
            continue;
        }
        idx += 1;
    }
    if !dominated {
        if let Some(p) = to_insert {
            list.push(p);
        }
    }
}

/// Merge `incoming` (sorted descending) into `dst` (also sorted descending),
/// preserving descending order. O(n + m).
fn merge_sorted_descending(dst: &mut Vec<SPair>, incoming: Vec<SPair>) {
    if incoming.is_empty() {
        return;
    }
    if dst.is_empty() {
        *dst = incoming;
        return;
    }
    let mut out: Vec<SPair> = Vec::with_capacity(dst.len() + incoming.len());
    let old = std::mem::take(dst);
    let mut a = old.into_iter().peekable();
    let mut b = incoming.into_iter().peekable();
    loop {
        match (a.peek(), b.peek()) {
            (Some(x), Some(y)) => {
                // descending: take the larger first
                if x.cmp(y) == std::cmp::Ordering::Greater {
                    out.push(a.next().unwrap());
                } else {
                    out.push(b.next().unwrap());
                }
            }
            (Some(_), None) => {
                out.extend(a);
                break;
            }
            (None, Some(_)) => {
                out.extend(b);
                break;
            }
            (None, None) => break,
        }
    }
    *dst = out;
}

// ────────────────────────────── Buchberger ─────────────────────────────────

struct BuchbergerState {
    ring: Arc<PolyRing>,
    cfg: BuchbergerConfig,
    basis: Vec<BasisElement>,
    /// Pending S-pairs sorted in **descending** `ordering_key` order so
    /// `Vec::pop()` returns the smallest pair (lowest sugar, then lcm_deg,
    /// then age). Held as a sorted vector — not a heap — because the GM
    /// M-criterion needs to walk and mutate the list during pair insertion
    /// (CoCoA's `GPairList`).
    open: Vec<SPair>,
    age_counter: u64,
    generation: u32,
    /// True once a constant (nonzero) has entered the basis.
    trivial: bool,
}

impl BuchbergerState {
    fn new(ring: Arc<PolyRing>, cfg: BuchbergerConfig) -> Self {
        BuchbergerState {
            ring,
            cfg,
            basis: Vec::new(),
            open: Vec::new(),
            age_counter: 0,
            generation: 0,
            trivial: false,
        }
    }

    fn check_cancel(&self) -> Result<(), SolverError> {
        if let Some(t) = &self.cfg.cancel_token {
            if t.is_cancelled() {
                return Err(SolverError::Timeout);
            }
        }
        Ok(())
    }

    fn add_generators<O: BuchbergerObserver>(
        &mut self,
        generators: Vec<Polynomial>,
        observer: &mut O,
    ) -> Result<(), SolverError> {
        for g in generators {
            self.check_cancel()?;
            if g.is_zero() { continue; }
            // Reduce the new generator by the current basis BEFORE adding.
            // Use ref-based reduce to avoid cloning every active polynomial.
            let active_refs: Vec<&Polynomial> = self.basis.iter()
                .filter(|e| e.active)
                .map(|e| &e.poly)
                .collect();
            let active_idxs = self.active_indices();
            let mut g_red = g.reduce_by_refs(&active_refs, &self.ring);
            if g_red.is_zero() { continue; }
            g_red = g_red.make_monic(&self.ring);
            if g_red.is_constant() {
                // We've found a unit — the ideal is the whole ring.
                self.trivial = true;
                let idx = self.basis.len();
                let lt = g_red.leading_monomial(&self.ring).unwrap();
                let lt_divmask = self.ring.divmask.compute(&lt);
                let sugar = lt.total_degree();
                observer.on_initial_reducers(&active_idxs);
                observer.on_initial_basis(idx, &g_red);
                self.basis.push(BasisElement {
                    poly: g_red,
                    lt,
                    lt_divmask,
                    active: true,
                    sugar,
                });
                if self.cfg.abort_on_trivial {
                    return Ok(());
                }
                continue;
            }
            let idx = self.basis.len();
            let lt = g_red.leading_monomial(&self.ring).unwrap();
            let lt_divmask = self.ring.divmask.compute(&lt);
            let sugar = lt.total_degree();
            observer.on_initial_reducers(&active_idxs);
            observer.on_initial_basis(idx, &g_red);
            // Generate S-pairs against all earlier ACTIVE elements BEFORE
            // deactivation, so we don't lose pairs that involve elements about
            // to become inactive (D3: non-strict deactivation).
            self.generate_pairs_against(idx, &lt, sugar);
            // Non-strict deactivation: deactivate older elements whose LT is divisible by lt.
            for k in 0..idx {
                if self.basis[k].active && lt.divides(&self.basis[k].lt) {
                    self.basis[k].active = false;
                }
            }
            self.basis.push(BasisElement { poly: g_red, lt, lt_divmask, active: true, sugar });
        }
        Ok(())
    }

    fn generate_pairs_against(&mut self, new_idx: usize, new_lt: &Monomial, new_sugar: u32) {
        // NOTE: We do NOT skip deactivated basis elements here. Non-strict
        // deactivation means a deactivated element's leading term still
        // contributes S-pair obligations: pending pairs against it must
        // remain in the queue (handled at pop time), and *new* pairs
        // generated when adding later elements are required for the GM
        // criterion to be sound.
        //
        // Algorithm (mirrors CoCoA `myBuildNewPairs` / `myGMInsert` in
        // TmpGReductor.C):
        //   1. Build pairs (k, new) for every existing basis element, including
        //      coprime pairs — the M-criterion uses them as dominators.
        //   2. Apply GM M-criterion via `gm_insert` so a new pair is dropped
        //      if any existing pair's LCM divides it (and vice versa).
        //   3. After all pairs are GM-inserted, drop coprime pairs (Buchberger
        //      product criterion: their S-poly reduces to zero by construction).
        //   4. Merge the surviving sorted-descending into `self.open`.
        let mut new_pairs: Vec<SPair> = Vec::with_capacity(new_idx);
        for k in 0..new_idx {
            let basis_k_lt = &self.basis[k].lt;
            let lcm = new_lt.lcm(basis_k_lt);
            let lcm_divmask = self.ring.divmask.compute(&lcm);
            let lcm_deg = lcm.total_degree();
            let is_coprime = new_lt.is_coprime(basis_k_lt);
            // Sugar = max(sugar(new) + (lcm - new_lt), sugar(k) + (lcm - k_lt))
            let s_new = new_sugar + (lcm_deg - new_lt.total_degree());
            let s_k = self.basis[k].sugar + (lcm_deg - basis_k_lt.total_degree());
            let sugar = s_new.max(s_k);
            self.age_counter += 1;
            let pair = SPair {
                i: k,
                j: new_idx,
                sugar,
                lcm,
                lcm_divmask,
                lcm_deg,
                age: self.age_counter,
                generation: self.generation,
                is_coprime,
            };
            gm_insert(&mut new_pairs, pair);
        }
        // Coprime criterion: drop coprime pairs now that GM is done with them.
        new_pairs.retain(|p| !p.is_coprime);
        // Merge into self.open while keeping descending sort (so pop_back
        // returns the smallest pair). new_pairs is currently in arbitrary
        // order from `gm_insert`; sort it once, then merge.
        new_pairs.sort_by(|a, b| b.cmp(a));
        merge_sorted_descending(&mut self.open, new_pairs);
    }

    fn active_polys(&self) -> Vec<Polynomial> {
        self.basis
            .iter()
            .filter(|e| e.active)
            .map(|e| e.poly.clone())
            .collect()
    }

    fn active_poly_refs(&self) -> Vec<&Polynomial> {
        self.basis
            .iter()
            .filter(|e| e.active)
            .map(|e| &e.poly)
            .collect()
    }

    /// In-place tail-reduce all active basis elements.
    ///
    /// For each active element `i`, computes the normal form of `basis[i].poly`
    /// modulo all OTHER active elements and replaces the body in place.
    /// Because `reduce_by_refs` only modifies tail terms (the leading term is
    /// always the divisor of itself among the other-set when monic, so it
    /// stays put), `basis[i].lt` and `basis[i].lt_divmask` remain valid.
    ///
    /// If a polynomial reduces to zero, it is deactivated (and all bookkeeping
    /// invariants — including `Checkpoint::active_snapshot` — remain stable
    /// because we never resize `self.basis`).
    ///
    /// This is the periodic "interreduce-during-incremental-GB" hook:
    /// without it, the basis grows monotonically across `add_generators`
    /// calls because D3 only deactivates strictly dominated elements but
    /// does not shrink tail-redundancy in surviving polynomials, which
    /// makes every subsequent `reduce_by_refs` quadratically more expensive.
    fn tail_reduce_active(&mut self) {
        // Snapshot the active indices and clone their polys ONCE into a
        // workspace. We then reduce each workspace[i] by &workspace[j] for
        // j ≠ i with `reduce_by_refs`. Repeating to a fixed point isn't
        // necessary because tail reduction is monotone (each pass strictly
        // shrinks tails or leaves them unchanged).
        let active_idx: Vec<usize> = self.basis.iter()
            .enumerate()
            .filter(|(_, e)| e.active)
            .map(|(i, _)| i)
            .collect();
        if active_idx.len() < 2 {
            return;
        }
        // Workspace = active polys, in active_idx order.
        let mut workspace: Vec<Polynomial> = active_idx.iter()
            .map(|&i| self.basis[i].poly.clone())
            .collect();

        // For each i, build refs from workspace skipping i. Note we skip
        // ALREADY-zero entries to avoid wasted work.
        for i in 0..workspace.len() {
            let others: Vec<&Polynomial> = workspace.iter()
                .enumerate()
                .filter(|(j, p)| *j != i && !p.is_zero())
                .map(|(_, p)| p)
                .collect();
            if others.is_empty() {
                continue;
            }
            let red = workspace[i].reduce_by_refs(&others, &self.ring);
            workspace[i] = red;
        }

        // Write back into self.basis. Preserve `lt`/`lt_divmask`/`sugar`
        // for non-zero results. For zero results, deactivate.
        for (slot, poly) in active_idx.iter().zip(workspace.into_iter()) {
            if poly.is_zero() {
                self.basis[*slot].active = false;
            } else {
                // Make monic so the seed is a reduced GB.
                let monic = poly.make_monic(&self.ring);
                self.basis[*slot].poly = monic;
                // lt/lt_divmask unchanged: tail reduction preserves leading term.
            }
        }
    }

    /// Indices (into `self.basis`) of currently-active basis elements.
    /// Stable order matches `active_polys()`.
    fn active_indices(&self) -> Vec<usize> {
        self.basis
            .iter()
            .enumerate()
            .filter(|(_, e)| e.active)
            .map(|(i, _)| i)
            .collect()
    }

    fn run<O: BuchbergerObserver>(&mut self, observer: &mut O) -> Result<(), SolverError> {
        if self.trivial && self.cfg.abort_on_trivial { return Ok(()); }
        // Periodic in-loop tail-reduction throttle: after every
        // INTERREDUCE_EVERY new basis additions, run `tail_reduce_active`.
        // This keeps the active basis "thin" so subsequent S-pair reductions
        // in `reduce_by_refs` don't grow quadratically.
        const INTERREDUCE_EVERY: usize = 32;
        let mut adds_since_interreduce: usize = 0;
        // self.open is sorted descending — `pop()` returns the smallest pair
        // (lowest sugar, then lcm_deg, then age).
        while let Some(pair) = self.open.pop() {
            self.check_cancel()?;

            // Skip pairs from earlier generations (incremental support).
            if pair.generation < self.generation { continue; }
            // Non-strict deactivation (D3): we still process pending S-pairs
            // even if one of the basis elements was later deactivated.
            // Product criterion + GM M-criterion are now applied at pair
            // generation time (see `generate_pairs_against` /
            // `gm_insert`), so coprime/dominated pairs never reach this loop.
            // Chain criterion (Buchberger's 2nd) is still NOT applied here:
            // a previous attempt produced incomplete GBs (it only checked
            // `lt(k) | lcm(i,j)` without verifying the substitute pairs were
            // discharged). Re-introducing a sound version would require
            // CoCoA's `BCriterion` (TmpGReductor.C:`myApplyBCriterion`) and
            // is left for a future plan.

            // Build the S-polynomial: (lcm/LT_i) * f_i - (lcm/LT_j) * f_j
            let bi = &self.basis[pair.i];
            let bj = &self.basis[pair.j];
            let mul_i = pair.lcm.div(&bi.lt);
            let mul_j = pair.lcm.div(&bj.lt);
            let lc_i = bi.poly.leading_coefficient().unwrap();
            let lc_j = bj.poly.leading_coefficient().unwrap();
            // Scale fj by (lc_i / lc_j) so leading coefficients cancel.
            let scale_j = self.ring.field.div(lc_i, lc_j).unwrap();
            let term_i = self.ring.field.one();
            let part_i = bi.poly.mul_term(mul_i.exponents(), &term_i, &self.ring);
            let part_j = bj.poly.mul_term(mul_j.exponents(), &scale_j, &self.ring);
            let s_poly = part_i.sub(&part_j, &self.ring);

            // Reduce against the current ACTIVE basis (one-at-a-time).
            // Use ref-based reduce to avoid cloning every active polynomial
            // for each S-pair — this was the dominant per-call cost on
            // dense-ideal benchmarks (e.g. chunkedadd1) under the profiler.
            let active_refs: Vec<&Polynomial> = self.basis.iter()
                .filter(|e| e.active)
                .map(|e| &e.poly)
                .collect();
            let mut nf = s_poly.reduce_by_refs(&active_refs, &self.ring);
            if nf.is_zero() { continue; }

            nf = nf.make_monic(&self.ring);

            let new_idx = self.basis.len();
            let lt = nf.leading_monomial(&self.ring).unwrap();
            let lt_divmask = self.ring.divmask.compute(&lt);
            let sugar = pair.sugar.max(lt.total_degree());
            observer.on_new_poly(new_idx, &nf, (pair.i, pair.j));

            // Trivial-ideal short-circuit.
            if nf.is_constant() {
                self.trivial = true;
                self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar });
                if self.cfg.abort_on_trivial { return Ok(()); }
                continue;
            }

            // Non-strict deactivation.
            // Generate new pairs FIRST, so we don't drop pairs against
            // elements about to be deactivated.
            self.generate_pairs_against(new_idx, &lt, sugar);
            for k in 0..new_idx {
                if self.basis[k].active && lt.divides(&self.basis[k].lt) {
                    self.basis[k].active = false;
                }
            }
            self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar });
            adds_since_interreduce += 1;

            // Periodic in-loop tail reduction. Only when the observer is the
            // no-op kind (we can't easily detect this generically; instead,
            // we make tail_reduce_active itself harmless to the observer
            // because it only modifies tails, not LTs/indices). Skip when
            // already trivial.
            if adds_since_interreduce >= INTERREDUCE_EVERY && !self.trivial {
                self.tail_reduce_active();
                adds_since_interreduce = 0;
            }
        }
        Ok(())
    }

    fn finalize_basis(self) -> Vec<Polynomial> {
        // Take active polynomials and inter-reduce once.
        let active: Vec<Polynomial> = self
            .basis
            .into_iter()
            .filter(|e| e.active)
            .map(|e| e.poly)
            .collect();
        // If there's a constant, the basis is just {1}.
        if active.iter().any(|p| p.is_constant()) {
            return vec![Polynomial::constant(self.ring.field.one(), &self.ring)];
        }
        interreduce(active, &self.ring)
    }
}

// ──────────────────────────── Incremental GB ────────────────────────────────
//
// Provides push/pop semantics. Each `push` records the basis length and the
// S-pair queue contents; `pop` truncates the basis and restores the queue.

#[derive(Clone, Debug)]
struct Checkpoint {
    basis_len: usize,
    /// Snapshot of `active` flags for the elements that existed at push time,
    /// so we can fully restore them on `pop` (covers any deactivations that
    /// happened between push and pop).
    active_snapshot: Vec<bool>,
    /// Generation at this level — bumped on `pop`.
    generation: u32,
    /// Snapshot of the open S-pair queue (sorted descending, same convention
    /// as `BuchbergerState::open`). Simple but correct; could be replaced
    /// with generation tagging in a future plan.
    saved_open: Vec<SPair>,
    age_counter: u64,
    trivial: bool,
}

pub struct IncrementalGB {
    state: BuchbergerState,
    trail: Vec<Checkpoint>,
}

impl IncrementalGB {
    pub fn new(ring: Arc<PolyRing>, cfg: BuchbergerConfig) -> Self {
        IncrementalGB {
            state: BuchbergerState::new(ring, cfg),
            trail: Vec::new(),
        }
    }

    pub fn ring(&self) -> &Arc<PolyRing> { &self.state.ring }

    pub fn add_generators(&mut self, polys: Vec<Polynomial>) -> Result<bool, SolverError> {
        let mut obs = NoObserver;
        self.state.add_generators(polys, &mut obs)?;
        self.state.run(&mut obs)?;
        // Tail-reduce the active basis to prevent monotonic growth across
        // successive `add_generators` calls (a hot path under profiling).
        if !self.state.trivial {
            self.state.tail_reduce_active();
        }
        Ok(self.state.trivial)
    }

    /// Observed variant of `add_generators`: the supplied observer
    /// receives `on_initial_basis` / `on_new_poly` / `on_inter_reduce`
    /// callbacks during the GB extension.  Used by `GbTracer` for
    /// UNSAT-core extraction.
    pub fn add_generators_observed<O: BuchbergerObserver>(
        &mut self,
        polys: Vec<Polynomial>,
        observer: &mut O,
    ) -> Result<bool, SolverError> {
        self.state.add_generators(polys, observer)?;
        self.state.run(observer)?;
        // NOTE: do NOT tail-reduce here. The observer/tracer relies on
        // basis-element identity for UNSAT-core extraction; rewriting
        // polynomial bodies underneath it would invalidate its tracking.
        Ok(self.state.trivial)
    }

    /// Save a checkpoint for backtracking. Cost: O(basis_len + open_len)
    /// (clones the S-pair vector — already sorted, no extra ordering work).
    pub fn push(&mut self) {
        let active_snapshot: Vec<bool> = self.state.basis.iter().map(|e| e.active).collect();
        self.trail.push(Checkpoint {
            basis_len: self.state.basis.len(),
            active_snapshot,
            generation: self.state.generation,
            saved_open: self.state.open.clone(),
            age_counter: self.state.age_counter,
            trivial: self.state.trivial,
        });
        self.state.generation = self.state.generation.wrapping_add(1);
    }

    pub fn pop(&mut self) {
        if let Some(cp) = self.trail.pop() {
            // Truncate basis.
            self.state.basis.truncate(cp.basis_len);
            // Restore active flags from the snapshot.
            for (idx, was_active) in cp.active_snapshot.into_iter().enumerate() {
                if idx < self.state.basis.len() {
                    self.state.basis[idx].active = was_active;
                }
            }
            // Restore S-pair queue (already sorted descending).
            self.state.open = cp.saved_open;
            self.state.age_counter = cp.age_counter;
            self.state.generation = cp.generation;
            self.state.trivial = cp.trivial;
        }
    }

    pub fn basis(&self) -> Vec<Polynomial> {
        self.state.active_polys()
    }

    pub fn reduce(&self, p: &Polynomial) -> Polynomial {
        let refs = self.state.active_poly_refs();
        p.reduce_by_refs(&refs, &self.state.ring)
    }

    pub fn is_trivial(&self) -> bool {
        self.state.trivial
    }

    pub fn decision_level(&self) -> usize {
        self.trail.len()
    }
}

// ─────────────────────────────── Ideal ──────────────────────────────────────

/// A high-level wrapper around a Groebner basis.
///
/// Provides ideal containment, reduction, zero-dimensionality testing, and
/// minimal-polynomial computation by Gaussian elimination on normal forms.
#[derive(Clone, Debug)]
pub struct Ideal {
    pub ring: Arc<PolyRing>,
    pub basis: Vec<Polynomial>,
}

impl Ideal {
    pub fn new(ring: Arc<PolyRing>, basis: Vec<Polynomial>) -> Self {
        Ideal { ring, basis }
    }

    pub fn from_generators(
        ring: Arc<PolyRing>,
        generators: Vec<Polynomial>,
        cfg: &BuchbergerConfig,
    ) -> Result<Self, SolverError> {
        let gb = groebner_basis(generators, &ring, cfg)?;
        Ok(Ideal { ring, basis: gb.basis })
    }

    pub fn reduce(&self, p: &Polynomial) -> Polynomial {
        p.reduce_by(&self.basis, &self.ring)
    }

    pub fn contains(&self, p: &Polynomial) -> bool {
        self.reduce(p).is_zero()
    }

    pub fn is_whole_ring(&self) -> bool {
        self.basis.iter().any(|p| p.is_constant() && !p.is_zero())
    }

    /// Zero-dimensional iff every variable has a pure-power leading monomial in the GB.
    pub fn is_zero_dim(&self) -> bool {
        if self.basis.is_empty() { return false; }
        let n = self.ring.n_vars;
        let mut pure_var = vec![false; n];
        for p in &self.basis {
            if let Some(lt) = p.leading_term(&self.ring) {
                let exps = lt.exponents();
                let nonzero: Vec<usize> = (0..n).filter(|&v| exps[v] > 0).collect();
                if nonzero.len() == 1 {
                    pure_var[nonzero[0]] = true;
                }
            }
        }
        pure_var.iter().all(|&b| b)
    }

    pub fn normalize(&self, p: &Polynomial) -> Polynomial {
        if p.is_zero() { return Polynomial::zero(); }
        p.make_monic(&self.ring)
    }

    /// Compute the minimal polynomial of `x_var` modulo the ideal.
    ///
    /// Returns the coefficient vector `[c_0, c_1, ..., c_d]` (with `c_d = 1`).
    /// Returns `None` if the ideal is not zero-dimensional or the search hits the cap.
    pub fn min_poly(&self, var_idx: usize) -> Option<Vec<FieldElem>> {
        self.min_poly_cancel(var_idx, &CancelToken::none())
    }

    pub fn min_poly_cancel(
        &self,
        var_idx: usize,
        cancel: &CancelToken,
    ) -> Option<Vec<FieldElem>> {
        let ring = &self.ring;
        let f = &ring.field;
        if self.is_whole_ring() { return Some(vec![f.one()]); }
        if !self.is_zero_dim() { return None; }

        let one_poly = Polynomial::constant(f.one(), ring);
        let x_poly = Polynomial::variable(var_idx, ring);
        let one_nf = self.reduce(&one_poly);
        let mut powers: Vec<Polynomial> = vec![one_nf];

        const MIN_POLY_DEG_CAP: usize = 4096;

        // Echelon form: each row is (normal_form, dependency vector).
        let mut nfs: Vec<Polynomial> = Vec::new();
        let mut deps: Vec<Vec<FieldElem>> = Vec::new();
        let mut pivot_monos: Vec<Monomial> = Vec::new();

        for d in 0..=MIN_POLY_DEG_CAP {
            if cancel.is_cancelled() { return None; }
            let nf = if d == 0 {
                powers[0].clone()
            } else {
                let prev = powers[d - 1].clone();
                let next = prev.mul(&x_poly, ring);
                self.reduce(&next)
            };
            if d > 0 {
                powers.push(nf.clone());
            }

            // Build a row: (nf, e_d).
            let mut row_poly = nf.clone();
            let mut row_dep: Vec<FieldElem> = vec![f.zero(); d + 1];
            row_dep[d] = f.one();

            // Reduce row against existing echelon rows.
            for (i, nf_i) in nfs.iter().enumerate() {
                let lm_i = &pivot_monos[i];
                let coeff_at_lm = poly_coefficient_at(&row_poly, lm_i, ring);
                if !f.is_zero(&coeff_at_lm) {
                    let lc_i = poly_coefficient_at(nf_i, lm_i, ring);
                    debug_assert!(!f.is_zero(&lc_i));
                    let factor = f.div(&coeff_at_lm, &lc_i).unwrap();
                    let neg_factor = f.neg(&factor);
                    let scaled = nf_i.scale(&neg_factor, ring);
                    row_poly = row_poly.add(&scaled, ring);
                    let dep_i = &deps[i];
                    debug_assert!(dep_i.len() <= row_dep.len(),
                        "echelon row dep length exceeds current row_dep");
                    for k in 0..dep_i.len() {
                        let prod = f.mul(&factor, &dep_i[k]);
                        f.sub_assign(&mut row_dep[k], &prod);
                    }
                }
            }

            if row_poly.is_zero() {
                // Found a dependency!
                let mut top = row_dep.len();
                while top > 0 && f.is_zero(&row_dep[top - 1]) { top -= 1; }
                if top == 0 { return Some(vec![f.one()]); }
                let lead = row_dep[top - 1].clone();
                let mut coeffs: Vec<FieldElem> = Vec::with_capacity(top);
                for k in 0..top {
                    coeffs.push(f.div(&row_dep[k], &lead).unwrap());
                }
                return Some(coeffs);
            }

            // Add to echelon: pivot is the leading monomial of the (reduced) row.
            if let Some(lm) = row_poly.leading_monomial(ring) {
                pivot_monos.push(lm);
                nfs.push(row_poly);
                deps.push(row_dep);
            }
        }
        None
    }
}

// Look up the coefficient at a specific monomial within a polynomial.
fn poly_coefficient_at(p: &Polynomial, mon: &Monomial, ring: &PolyRing) -> FieldElem {
    let n = ring.n_vars;
    let target_deg = mon.total_degree();
    let target_exps = mon.exponents();
    let num = p.num_terms();
    let exps = p.raw_exponents();
    let coeffs = p.raw_coeffs();
    let degs = p.raw_total_degs();
    let mut lo = 0usize;
    let mut hi = num;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let mid_exps = &exps[mid * n..(mid + 1) * n];
        let mid_deg = degs[mid];
        let cmp = Polynomial::cmp_term_at(mid_exps, mid_deg, target_exps, target_deg, ring.order);
        match cmp {
            std::cmp::Ordering::Equal => return coeffs[mid].clone(),
            std::cmp::Ordering::Greater => lo = mid + 1,
            std::cmp::Ordering::Less => hi = mid,
        }
    }
    ring.field.zero()
}

// Add accessor helpers on Polynomial for the structural-equality routine above.
impl Polynomial {
    pub(crate) fn public_exponents(&self) -> &[u16] { self.raw_exponents() }
    pub(crate) fn public_coeffs(&self) -> &[FieldElem] { self.raw_coeffs() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn ring(n_vars: usize) -> Arc<PolyRing> {
        let f = PrimeField::new(BigUint::from(101u32));
        let names: Vec<String> = (0..n_vars).map(|i| format!("x{}", i)).collect();
        PolyRing::new(f, names, MonomialOrder::DegRevLex)
    }

    fn const_p(ring: &Arc<PolyRing>, v: u64) -> Polynomial {
        Polynomial::constant(ring.field.from_u64(v), ring)
    }

    #[test]
    fn gb_unit_ideal() {
        let r = ring(2);
        // {1} generates the whole ring.
        let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
        let gb = groebner_basis(vec![const_p(&r, 1)], &r, &cfg).unwrap();
        assert_eq!(gb.basis.len(), 1);
        assert!(gb.basis[0].is_constant());
    }

    #[test]
    fn gb_simple_two_gen() {
        let r = ring(2);
        let f = &r.field;
        // I = (x^2 - y, x*y - 1) in DegRevLex.
        let p1 = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 1]), f.from_i64(-1)),
            ],
            &r,
        );
        let p2 = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 1]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0]), f.from_i64(-1)),
            ],
            &r,
        );
        let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
        let gb = groebner_basis(vec![p1, p2], &r, &cfg).unwrap();
        // Sanity: GB should be nonempty and zero-dimensional (two equations in two unknowns).
        assert!(!gb.basis.is_empty());
        let ideal = Ideal { ring: r.clone(), basis: gb.basis };
        assert!(ideal.is_zero_dim());
        // x^3 - 1 should be in the ideal: x^2 = y, so x^3 = x*y = 1, hence x^3 - 1 = 0.
        let test = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![3, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0]), f.from_i64(-1)),
            ],
            &r,
        );
        assert!(ideal.contains(&test));
    }

    #[test]
    fn min_poly_simple() {
        let r = ring(1);
        let f = &r.field;
        // I = (x^2 - 2) over GF(101). Then min_poly(x) = x^2 - 2 (monic).
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0]), f.from_i64(-2)),
            ],
            &r,
        );
        let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
        let gb = groebner_basis(vec![p], &r, &cfg).unwrap();
        let ideal = Ideal { ring: r.clone(), basis: gb.basis };
        assert!(ideal.is_zero_dim());
        let mp = ideal.min_poly(0).expect("zero-dim min_poly should exist");
        // Expect [-2, 0, 1]
        assert_eq!(mp.len(), 3);
        assert_eq!(mp[0], f.from_i64(-2));
        assert!(f.is_zero(&mp[1]));
        assert!(f.is_one(&mp[2]));
    }

    #[test]
    fn incremental_push_pop() {
        let r = ring(2);
        let f = &r.field;
        let p1 = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0]), f.from_i64(-1)),
            ],
            &r,
        );
        let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
        let mut igb = IncrementalGB::new(r.clone(), cfg);
        igb.add_generators(vec![p1]).unwrap();
        let basis_pre = igb.basis().len();
        igb.push();
        // Add a strong constraint that makes the system inconsistent: x = 2 AND x^2 = 1
        let xeq2 = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0]), f.from_i64(-2)),
            ],
            &r,
        );
        let trivial = igb.add_generators(vec![xeq2]).unwrap();
        // x=2 + x^2=1  => 4=1 => 3=0 in GF(101) => not trivial. Use x=2 + x^2-2:
        // x^2 - 2 - (x - 2)(x + 2) = -2 + 4 = 2 mod ideal but already x=2 implies x^2 = 4.
        // Actually with x^2 = 1 and x = 2: 4 = 1 (false in chars 101). So GB = {1}.
        assert!(trivial);
        igb.pop();
        // After pop, we should be back to the previous state.
        assert_eq!(igb.basis().len(), basis_pre);
        assert!(!igb.is_trivial());
    }

    fn mk_pair(lcm_exps: Vec<u16>, age: u64, is_coprime: bool, ring: &PolyRing) -> SPair {
        let lcm = Monomial::from_exponents(lcm_exps);
        let lcm_divmask = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        SPair {
            i: 0,
            j: 0,
            sugar: lcm_deg,
            lcm,
            lcm_divmask,
            lcm_deg,
            age,
            generation: 0,
            is_coprime,
        }
    }

    #[test]
    fn gm_insert_smaller_lcm_dominates_larger() {
        // (x*y) dominates (x*y*z) since x*y | x*y*z.
        let r = ring(3);
        let mut list: Vec<SPair> = Vec::new();
        gm_insert(&mut list, mk_pair(vec![1, 1, 0], 1, false, &r));
        // Inserting (x*y*z) — should be dominated and dropped.
        gm_insert(&mut list, mk_pair(vec![1, 1, 1], 2, false, &r));
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].lcm.exponents(), &[1, 1, 0]);
    }

    #[test]
    fn gm_insert_larger_lcm_evicted_by_smaller() {
        // Insert (x*y*z) first, then (x*y) — the smaller dominates and evicts.
        let r = ring(3);
        let mut list: Vec<SPair> = Vec::new();
        gm_insert(&mut list, mk_pair(vec![1, 1, 1], 1, false, &r));
        gm_insert(&mut list, mk_pair(vec![1, 1, 0], 2, false, &r));
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].lcm.exponents(), &[1, 1, 0]);
    }

    #[test]
    fn gm_insert_unrelated_lcms_both_kept() {
        // (x*y) and (y*z) are incomparable — both should remain.
        let r = ring(3);
        let mut list: Vec<SPair> = Vec::new();
        gm_insert(&mut list, mk_pair(vec![1, 1, 0], 1, false, &r));
        gm_insert(&mut list, mk_pair(vec![0, 1, 1], 2, false, &r));
        assert_eq!(list.len(), 2);
    }

    #[test]
    fn gm_insert_equal_lcm_prefers_coprime() {
        // Equal LCMs: existing non-coprime, P coprime → existing replaced by P.
        let r = ring(3);
        let mut list: Vec<SPair> = Vec::new();
        gm_insert(&mut list, mk_pair(vec![1, 1, 0], 1, false, &r));
        gm_insert(&mut list, mk_pair(vec![1, 1, 0], 2, true, &r));
        assert_eq!(list.len(), 1);
        // The coprime pair (age=2) should now occupy the slot.
        assert_eq!(list[0].age, 2);
        assert!(list[0].is_coprime);
    }

    #[test]
    fn gm_insert_equal_lcm_keeps_existing_otherwise() {
        // Equal LCMs but coprime conditions don't trigger replacement → P dropped.
        let r = ring(3);
        let mut list: Vec<SPair> = Vec::new();
        gm_insert(&mut list, mk_pair(vec![1, 1, 0], 1, true, &r));
        gm_insert(&mut list, mk_pair(vec![1, 1, 0], 2, false, &r));
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].age, 1);
    }
}
