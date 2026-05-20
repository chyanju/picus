//! Buchberger's algorithm and the [`Ideal`] abstraction.
//!
//! Implementation notes:
//!
//! * One-at-a-time S-pair processing: the lowest-sugar pair is popped
//!   per iteration.
//! * Priority-queue ordering on `(sugar, lcm_deg, age)`.
//! * Non-strict basis deactivation: when adding a new element,
//!   deactivate any existing element whose leading monomial is
//!   divisible (not strictly) by the new one.
//! * End-only inter-reduction: a single pass after the main loop
//!   terminates.
//! * No restart heuristic.
//! * `DivMask`-accelerated divisibility rejection.
//! * Sugar degree with running updates during reduction.
//! * Gebauer-Möller M-criterion and product criterion applied at
//!   pair-generation time; B-criterion applied at basis-add time.

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
    /// Dispatch the inner loop to F4-lite (degree-batched matrix
    /// reduction) instead of one-S-pair-at-a-time geobucket reduction.
    /// Default: enabled iff `PICUS_USE_F4=1` is set in the environment.
    pub use_f4: bool,
}

impl Default for BuchbergerConfig {
    fn default() -> Self {
        BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: true,
            use_f4: use_f4_default(),
        }
    }
}

/// F4-lite default toggle. Returns `true` iff `PICUS_USE_F4=1` is set
/// in the environment. Used by all default `BuchbergerConfig`
/// construction sites so the F4 path is consistently enabled or
/// disabled across the solver.
pub fn use_f4_default() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var_os("PICUS_USE_F4").is_some())
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

/// Internal basis element. Visible to sibling submodules
/// (`spair_criteria`, `incremental`) so they can index into the
/// `BuchbergerState::basis` slice.
#[derive(Clone, Debug)]
pub(super) struct BasisElement {
    pub(super) poly: Polynomial,
    pub(super) lt: Monomial,
    #[allow(dead_code)] // reserved for future Gebauer-Möller chain criterion
    pub(super) lt_divmask: DivMask,
    /// Lazily deactivated when superseded by a smaller-LT element.
    pub(super) active: bool,
    /// Sugar degree at the time this element was added.
    pub(super) sugar: u32,
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
    {
        let _t = crate::profile::ScopedTimer::new("buchberger::add_generators");
        state.add_generators(generators, &mut obs)?;
    }
    {
        let _t = crate::profile::ScopedTimer::new("buchberger::run");
        state.run(&mut obs)?;
    }
    let _t = crate::profile::ScopedTimer::new("buchberger::finalize_basis");
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
pub fn interreduce(basis: Vec<Polynomial>, ring: &Arc<PolyRing>) -> Vec<Polynomial> {
    interreduce_with_cancel(basis, ring, None)
}

/// Inter-reduce with cooperative cancellation. Returns the partially-reduced
/// basis (still valid generators, just not yet inter-reduced) on cancel.
pub fn interreduce_with_cancel(
    mut basis: Vec<Polynomial>,
    ring: &Arc<PolyRing>,
    cancel: Option<&crate::timeout::CancelToken>,
) -> Vec<Polynomial> {
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
    // Single-pass tail reduction. After divisible-LT pruning above,
    // every surviving element's leading term is incomparable to every
    // other's, so reducing each element's tail by the others cannot
    // re-introduce monomials that some other element's LT divides —
    // one pass suffices.
    let n = filtered.len();
    for i in 0..n {
        // Cancel check between elements. On cancel, the partially
        // inter-reduced basis is returned; it is still a valid
        // generator set for the same ideal.
        if let Some(c) = cancel {
            if c.is_cancelled() { break; }
        }
        let mut others: Vec<&Polynomial> = Vec::with_capacity(n.saturating_sub(1));
        for (j, p) in filtered.iter().enumerate() {
            if j != i && !p.is_zero() {
                others.push(p);
            }
        }
        if others.is_empty() {
            continue;
        }
        let red = match cancel {
            Some(c) => filtered[i].reduce_by_refs_cancel(&others, ring, c),
            None => filtered[i].reduce_by_refs(&others, ring),
        };
        filtered[i] = if red.is_zero() {
            Polynomial::zero()
        } else {
            red.make_monic(ring)
        };
    }
    filtered.retain(|p| !p.is_zero());
    filtered
}

mod spair_criteria;
use spair_criteria::{b_criterion_kill, gm_insert, merge_sorted_descending};

// ────────────────────────────── Buchberger ─────────────────────────────────

/// Per-run engine counters. Filled unconditionally during a GB run;
/// printed to stderr at the end of [`BuchbergerState::run`] only when
/// the `PICUS_GB_STATS` environment variable is set.
#[derive(Clone, Debug, Default)]
pub struct GbEngineStats {
    pub pairs_generated: u64,
    pub pairs_killed_coprime: u64,
    pub pairs_killed_gm: u64,
    pub pairs_killed_b: u64,
    pub reductions_total: u64,
    pub reductions_useful: u64,
    pub reductions_useless: u64,
    pub interreduces_run: u64,
}

pub(super) struct BuchbergerState {
    pub(super) ring: Arc<PolyRing>,
    pub(super) cfg: BuchbergerConfig,
    pub(super) basis: Vec<BasisElement>,
    /// Pending S-pairs sorted in **descending** `ordering_key` order so
    /// `Vec::pop()` returns the smallest pair (lowest sugar, then lcm_deg,
    /// then age). Held as a sorted vector — not a heap — because the GM
    /// M-criterion needs to walk and mutate the list during pair insertion.
    pub(super) open: Vec<SPair>,
    pub(super) age_counter: u64,
    pub(super) generation: u32,
    /// True once a constant (nonzero) has entered the basis.
    pub(super) trivial: bool,
    /// GB-engine counters; written unconditionally, printed only on
    /// `PICUS_GB_STATS=1`.
    stats: GbEngineStats,
    /// Set when every initial generator shares the same total degree.
    /// Enables periodic in-loop tail-reduction. Set by
    /// [`Self::add_generators`] based on input shape.
    input_is_homog: bool,
}

impl BuchbergerState {
    pub(super) fn new(ring: Arc<PolyRing>, cfg: BuchbergerConfig) -> Self {
        BuchbergerState {
            ring,
            cfg,
            basis: Vec::new(),
            open: Vec::new(),
            age_counter: 0,
            generation: 0,
            trivial: false,
            stats: GbEngineStats::default(),
            input_is_homog: false,
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

    /// Seed the Buchberger state with polynomials that are already a
    /// reduced GB under [`Self.ring`]'s monomial order. Bypasses S-pair
    /// generation: an already-reduced GB has no open obligations among
    /// its own elements, so the pairs `add_generators` would generate
    /// against the seed are guaranteed to reduce to zero.
    ///
    /// Caller responsibility: the input must already be a reduced GB
    /// in `self.ring.order`. No validation is performed.
    pub(super) fn seed_with_reduced_basis(&mut self, basis: Vec<Polynomial>) {
        for poly in basis {
            if poly.is_zero() {
                continue;
            }
            let lt = match poly.leading_monomial(&self.ring) {
                Some(lt) => lt,
                None => continue,
            };
            let lt_divmask = self.ring.divmask.compute(&lt);
            let sugar = lt.total_degree();
            // Apply the same non-strict-deactivation rule that
            // `add_generators` does, so the seeded basis matches what
            // sequential `add_generators` would have produced.
            let new_idx = self.basis.len();
            for k in 0..new_idx {
                if self.basis[k].active && lt.divides(&self.basis[k].lt) {
                    self.basis[k].active = false;
                }
            }
            self.basis.push(BasisElement {
                poly,
                lt,
                lt_divmask,
                active: true,
                sugar,
            });
        }
    }

    pub(super) fn add_generators<O: BuchbergerObserver>(
        &mut self,
        generators: Vec<Polynomial>,
        observer: &mut O,
    ) -> Result<(), SolverError> {
        // Detect homogeneous input. If every generator's terms all
        // share the same total degree, the input is homogeneous, and
        // the main loop enables periodic in-loop tail-reduction.
        if self.basis.is_empty() {
            self.input_is_homog = generators.iter()
                .filter(|p| !p.is_zero())
                .all(|p| {
                    if p.num_terms() <= 1 { return true; }
                    let d0 = p.term(0, &self.ring).total_degree();
                    (1..p.num_terms()).all(|i| p.term(i, &self.ring).total_degree() == d0)
                });
        }
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
            let mut g_red = match &self.cfg.cancel_token {
                Some(c) => g.reduce_by_refs_cancel(&active_refs, &self.ring, c),
                None => g.reduce_by_refs(&active_refs, &self.ring),
            };
            if let Some(c) = &self.cfg.cancel_token {
                if c.is_cancelled() {
                    return Err(SolverError::Timeout);
                }
            }
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
        // Algorithm:
        //   1. For each active earlier basis element `k < new_idx`,
        //      build pair `(k, new)`. Inactive `k` are skipped: under
        //      non-strict deactivation, some active `m < k` satisfies
        //      `LT_m | LT_k`, so `(m, new)` is generated and
        //      GM-dominates `(k, new)`.
        //   2. Apply the M-criterion via `gm_insert`: drop a new pair
        //      if any other new pair's LCM divides it (with the
        //      equal-LCM coprime-replacement rule).
        //   3. After GM-insertion, drop coprime pairs (Buchberger
        //      product criterion: their S-poly reduces to zero).
        //   4. Apply the B-criterion to the existing open queue using
        //      the new polynomial's leading term.
        //   5. Sort surviving new_pairs descending and merge into
        //      `self.open`.
        let mut new_pairs: Vec<SPair> = Vec::with_capacity(new_idx);
        let mut pairs_built: u64 = 0;
        for k in 0..new_idx {
            if !self.basis[k].active {
                continue;
            }
            pairs_built += 1;
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
        self.stats.pairs_generated += pairs_built;
        let after_gm = new_pairs.len() as u64;
        self.stats.pairs_killed_gm += pairs_built.saturating_sub(after_gm);
        // Coprime criterion: drop coprime pairs now that GM is done with them.
        new_pairs.retain(|p| !p.is_coprime);
        let after_coprime = new_pairs.len() as u64;
        self.stats.pairs_killed_coprime += after_gm.saturating_sub(after_coprime);
        // B-criterion: prune the existing open queue using the new
        // polynomial's leading term. Runs after `new_pairs` has been
        // built and filtered.
        let new_lt_divmask = self.ring.divmask.compute(new_lt);
        let open_before_b = self.open.len() as u64;
        b_criterion_kill(&mut self.open, new_lt, new_lt_divmask, &self.basis);
        let open_after_b = self.open.len() as u64;
        self.stats.pairs_killed_b += open_before_b.saturating_sub(open_after_b);
        // Merge into self.open while keeping descending sort (so pop_back
        // returns the smallest pair). new_pairs is currently in arbitrary
        // order from `gm_insert`; sort it once, then merge.
        new_pairs.sort_by(|a, b| b.cmp(a));
        merge_sorted_descending(&mut self.open, new_pairs);
    }

    pub(super) fn active_polys(&self) -> Vec<Polynomial> {
        self.basis
            .iter()
            .filter(|e| e.active)
            .map(|e| e.poly.clone())
            .collect()
    }

    pub(super) fn active_poly_refs(&self) -> Vec<&Polynomial> {
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
    pub(super) fn tail_reduce_active(&mut self) {
        // Snapshot the active indices and clone their polys ONCE into a
        // workspace. We then reduce each workspace[i] by &workspace[j] for
        // j ≠ i with `reduce_by_refs`. Repeating to a fixed point isn't
        // necessary because tail reduction is monotone (each pass strictly
        // shrinks tails or leaves them unchanged).
        self.stats.interreduces_run += 1;
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

    pub(super) fn run<O: BuchbergerObserver>(&mut self, observer: &mut O) -> Result<(), SolverError> {
        if self.cfg.use_f4 {
            return self.run_f4(observer);
        }
        if self.trivial && self.cfg.abort_on_trivial { return Ok(()); }
        // Granular per-phase timing inside the main loop.
        let stats_on = crate::profile::gb_stats_enabled();
        let mut t_spoly_ns: u64 = 0;
        let mut t_reduce_ns: u64 = 0;
        let mut t_genpairs_ns: u64 = 0;
        let initial_open_size = self.open.len();
        let run_start = std::time::Instant::now();
        // self.open is sorted descending — `pop()` returns the smallest pair
        // (lowest sugar, then lcm_deg, then age).
        while let Some(pair) = self.open.pop() {
            if let Err(e) = self.check_cancel() {
                if stats_on {
                    let s = &self.stats;
                    let total_ns = run_start.elapsed().as_nanos() as u64;
                    let active_count = self.basis.iter().filter(|e| e.active).count();
                    eprintln!(
                        "[picus-gb-stats CANCELLED] pairs={} cop={} gm={} b={} red={} useful={} useless={} initial_open={} remaining_open={} basis_size={} active={} time_run_ms={:.2} time_spoly_ms={:.2} time_reduce_ms={:.2} time_genpairs_ms={:.2}",
                        s.pairs_generated, s.pairs_killed_coprime, s.pairs_killed_gm, s.pairs_killed_b,
                        s.reductions_total, s.reductions_useful, s.reductions_useless,
                        initial_open_size, self.open.len(), self.basis.len(), active_count,
                        total_ns as f64 / 1e6,
                        t_spoly_ns as f64 / 1e6,
                        t_reduce_ns as f64 / 1e6,
                        t_genpairs_ns as f64 / 1e6,
                    );
                }
                return Err(e);
            }

            // Skip pairs from earlier generations (incremental support).
            if pair.generation < self.generation { continue; }
            // Non-strict deactivation: pending S-pairs are processed
            // even if one of their basis elements has since been
            // deactivated. The product and GM M-criteria are applied at
            // pair-generation time, so coprime and dominated pairs do
            // not reach this loop.

            let t_spoly_start = if stats_on { Some(std::time::Instant::now()) } else { None };
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
            if let Some(t0) = t_spoly_start {
                t_spoly_ns += t0.elapsed().as_nanos() as u64;
            }

            // Reduce against the current active basis. Reference-based
            // reduction avoids cloning every active polynomial for each
            // S-pair; the cancel-aware variant bounds the cost of a
            // single dense reduction so the caller's timeout is
            // honoured.
            let t_red_start = if stats_on { Some(std::time::Instant::now()) } else { None };
            let active_refs: Vec<&Polynomial> = self.basis.iter()
                .filter(|e| e.active)
                .map(|e| &e.poly)
                .collect();
            let mut nf = match &self.cfg.cancel_token {
                Some(c) => s_poly.reduce_by_refs_cancel(&active_refs, &self.ring, c),
                None => s_poly.reduce_by_refs(&active_refs, &self.ring),
            };
            if let Some(t0) = t_red_start {
                t_reduce_ns += t0.elapsed().as_nanos() as u64;
            }
            if let Some(c) = &self.cfg.cancel_token {
                if c.is_cancelled() {
                    if stats_on {
                        let s = &self.stats;
                        let total_ns = run_start.elapsed().as_nanos() as u64;
                        let active_count = self.basis.iter().filter(|e| e.active).count();
                        eprintln!(
                            "[picus-gb-stats CANCELLED-MIDLOOP] pairs={} cop={} gm={} b={} red={} useful={} useless={} initial_open={} remaining_open={} basis_size={} active={} time_run_ms={:.2} time_spoly_ms={:.2} time_reduce_ms={:.2} time_genpairs_ms={:.2}",
                            s.pairs_generated, s.pairs_killed_coprime, s.pairs_killed_gm, s.pairs_killed_b,
                            s.reductions_total, s.reductions_useful, s.reductions_useless,
                            initial_open_size, self.open.len(), self.basis.len(), active_count,
                            total_ns as f64 / 1e6,
                            t_spoly_ns as f64 / 1e6,
                            t_reduce_ns as f64 / 1e6,
                            t_genpairs_ns as f64 / 1e6,
                        );
                    }
                    return Err(SolverError::Timeout);
                }
            }
            self.stats.reductions_total += 1;
            if nf.is_zero() {
                self.stats.reductions_useless += 1;
                continue;
            }
            self.stats.reductions_useful += 1;

            nf = nf.make_monic(&self.ring);

            let new_idx = self.basis.len();
            let lt = nf.leading_monomial(&self.ring).unwrap();
            let lt_divmask = self.ring.divmask.compute(&lt);
            // Sugar update. The pair sugar (computed at pair generation)
            // is already an upper bound on the new polynomial's sugar —
            // it equals
            // `max(deg(lcm/LT_i) + sugar(f_i), deg(lcm/LT_j) + sugar(f_j))`,
            // and reduction is degree-non-increasing on the leading
            // term.
            debug_assert!(
                lt.total_degree() <= pair.sugar,
                "sugar invariant violated: LT total_degree {} > pair.sugar {}",
                lt.total_degree(), pair.sugar
            );
            let sugar = pair.sugar;
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
            let t_genpairs_start = if stats_on { Some(std::time::Instant::now()) } else { None };
            self.generate_pairs_against(new_idx, &lt, sugar);
            if let Some(t0) = t_genpairs_start {
                t_genpairs_ns += t0.elapsed().as_nanos() as u64;
            }
            for k in 0..new_idx {
                if self.basis[k].active && lt.divides(&self.basis[k].lt) {
                    self.basis[k].active = false;
                }
            }
            self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar });
            // Periodic in-loop tail-reduction, gated on homogeneous
            // input. Tail-reduction mid-loop preserves the gradedness
            // invariant that sugar-degree pair selection relies on; for
            // non-homogeneous input it would distort selection order
            // and slow the search, so it is disabled there.
            if self.input_is_homog && self.stats.reductions_useful > 0
                && self.stats.reductions_useful % 32 == 0
            {
                self.tail_reduce_active();
            }
        }
        // Optional GB-engine telemetry: only emit when the user opts in
        // via `PICUS_GB_STATS=1`. Mirrors the existing `PICUS_PROFILE`
        // pattern; default-build behavior is unchanged.
        if std::env::var_os("PICUS_GB_STATS").is_some() {
            let s = &self.stats;
            let total_ns = run_start.elapsed().as_nanos() as u64;
            let active_count = self.basis.iter().filter(|e| e.active).count();
            eprintln!(
                "[picus-gb-stats] pairs={} cop={} gm={} b={} red={} useful={} useless={} interreduces={} basis_size={} active={} initial_open={} time_run_ms={:.2} time_spoly_ms={:.2} time_reduce_ms={:.2} time_genpairs_ms={:.2}",
                s.pairs_generated,
                s.pairs_killed_coprime,
                s.pairs_killed_gm,
                s.pairs_killed_b,
                s.reductions_total,
                s.reductions_useful,
                s.reductions_useless,
                s.interreduces_run,
                self.basis.len(),
                active_count,
                initial_open_size,
                total_ns as f64 / 1e6,
                t_spoly_ns as f64 / 1e6,
                t_reduce_ns as f64 / 1e6,
                t_genpairs_ns as f64 / 1e6,
            );
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

    /// Per-pair S-poly construction + geobucket reduction. Extracted
    /// from `run()` so `run_f4` can fall back to it for size-1
    /// batches (where F4's matrix amortization wins zero and the
    /// safety-net reduction is pure overhead).
    fn process_pair_geobucket<O: BuchbergerObserver>(
        &mut self,
        pair: SPair,
        observer: &mut O,
    ) -> Result<(), SolverError> {
        let bi = &self.basis[pair.i];
        let bj = &self.basis[pair.j];
        let mul_i = pair.lcm.div(&bi.lt);
        let mul_j = pair.lcm.div(&bj.lt);
        let lc_i = bi.poly.leading_coefficient().unwrap();
        let lc_j = bj.poly.leading_coefficient().unwrap();
        let scale_j = self.ring.field.div(lc_i, lc_j).unwrap();
        let term_i = self.ring.field.one();
        let part_i = bi.poly.mul_term(mul_i.exponents(), &term_i, &self.ring);
        let part_j = bj.poly.mul_term(mul_j.exponents(), &scale_j, &self.ring);
        let s_poly = part_i.sub(&part_j, &self.ring);
        let active_refs: Vec<&Polynomial> = self.basis.iter()
            .filter(|e| e.active)
            .map(|e| &e.poly)
            .collect();
        let mut nf = match &self.cfg.cancel_token {
            Some(c) => s_poly.reduce_by_refs_cancel(&active_refs, &self.ring, c),
            None => s_poly.reduce_by_refs(&active_refs, &self.ring),
        };
        if let Some(c) = &self.cfg.cancel_token {
            if c.is_cancelled() {
                return Err(SolverError::Timeout);
            }
        }
        self.stats.reductions_total += 1;
        if nf.is_zero() {
            self.stats.reductions_useless += 1;
            return Ok(());
        }
        self.stats.reductions_useful += 1;
        nf = nf.make_monic(&self.ring);

        let new_idx = self.basis.len();
        let lt = nf.leading_monomial(&self.ring).unwrap();
        let lt_divmask = self.ring.divmask.compute(&lt);
        debug_assert!(
            lt.total_degree() <= pair.sugar,
            "sugar invariant violated: LT total_degree {} > pair.sugar {}",
            lt.total_degree(), pair.sugar
        );
        let sugar = pair.sugar;
        observer.on_new_poly(new_idx, &nf, (pair.i, pair.j));

        if nf.is_constant() {
            self.trivial = true;
            self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar });
            if self.cfg.abort_on_trivial { return Ok(()); }
            return Ok(());
        }

        self.generate_pairs_against(new_idx, &lt, sugar);
        for k in 0..new_idx {
            if self.basis[k].active && lt.divides(&self.basis[k].lt) {
                self.basis[k].active = false;
            }
        }
        self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar });
        Ok(())
    }

    /// F4-lite main loop. Pops a batch of same-sugar S-pairs and
    /// reduces them simultaneously via [`f4::process_batch`], then
    /// integrates each new generator (generating cross-pairs against
    /// the existing basis exactly as the per-pair path does).
    fn run_f4<O: BuchbergerObserver>(&mut self, observer: &mut O) -> Result<(), SolverError> {
        if self.trivial && self.cfg.abort_on_trivial {
            return Ok(());
        }
        let stats_on = crate::profile::gb_stats_enabled();
        let run_start = std::time::Instant::now();
        let initial_open_size = self.open.len();

        loop {
            self.check_cancel()?;
            // self.open is sorted descending; pop returns smallest
            // sugar first. Pop a batch with the SAME smallest sugar.
            let lowest_sugar = match self.open.last() {
                Some(p) => p.sugar,
                None => break,
            };
            let mut batch: Vec<SPair> = Vec::new();
            while let Some(top) = self.open.last() {
                if top.sugar > lowest_sugar {
                    break;
                }
                let pair = self.open.pop().unwrap();
                if pair.generation < self.generation {
                    continue;
                }
                batch.push(pair);
            }
            if batch.is_empty() {
                continue;
            }

            // F4 amortises reducer construction across a sugar batch
            // but pays the matrix-build overhead each time. For a
            // single-pair batch the matrix is strictly more expensive
            // than direct per-pair reduction, so fall back.
            if batch.len() < 2 {
                for pair in batch {
                    self.process_pair_geobucket(pair, observer)?;
                }
                continue;
            }

            // Build F4BasisRef array (same indexing as self.basis).
            let basis_refs: Vec<super::f4::F4BasisRef> = self
                .basis
                .iter()
                .map(|e| super::f4::F4BasisRef {
                    poly: &e.poly,
                    lt: &e.lt,
                    active: e.active,
                })
                .collect();

            let batch_refs: Vec<&SPair> = batch.iter().collect();
            let new_polys = super::f4::process_batch(
                &batch_refs,
                &basis_refs,
                &self.ring,
                self.cfg.cancel_token.as_ref(),
            );

            self.check_cancel()?;

            // Stats: each batch entry counts as one reduction. Useful
            // = produced a new generator; useless = produced nothing.
            self.stats.reductions_total += batch.len() as u64;
            self.stats.reductions_useful += new_polys.len() as u64;
            if batch.len() >= new_polys.len() {
                self.stats.reductions_useless += (batch.len() - new_polys.len()) as u64;
            }

            // Integrate each new poly as a basis element. Mirror the
            // run() path's integration step exactly. F4 already monic-
            // normalized each output and the matrix echelon ensures
            // each residue's LT is not divisible by any active basis
            // LT (provided symbolic preprocessing closed under
            // reducibility — which it does by BFS over reducer tails).
            let batch_sugar = lowest_sugar;
            for poly in new_polys {
                self.check_cancel()?;
                if poly.is_zero() {
                    continue;
                }
                let lt = match poly.leading_monomial(&self.ring) {
                    Some(l) => l,
                    None => continue,
                };
                let lt_divmask = self.ring.divmask.compute(&lt);
                debug_assert!(
                    lt.total_degree() <= batch_sugar,
                    "F4 sugar invariant violated: LT deg {} > batch_sugar {}",
                    lt.total_degree(),
                    batch_sugar
                );
                let sugar = batch_sugar;
                let new_idx = self.basis.len();
                // Use sentinel from-pair indices (0, 0) — F4 batches don't
                // map back to a specific pair; tracer paths don't run on
                // F4 anyway.
                observer.on_new_poly(new_idx, &poly, (0, 0));

                if poly.is_constant() {
                    self.trivial = true;
                    self.basis.push(BasisElement {
                        poly,
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

                self.generate_pairs_against(new_idx, &lt, sugar);
                for k in 0..new_idx {
                    if self.basis[k].active && lt.divides(&self.basis[k].lt) {
                        self.basis[k].active = false;
                    }
                }
                self.basis.push(BasisElement {
                    poly,
                    lt,
                    lt_divmask,
                    active: true,
                    sugar,
                });
            }
        }

        if stats_on {
            let s = &self.stats;
            let total_ns = run_start.elapsed().as_nanos() as u64;
            let active_count = self.basis.iter().filter(|e| e.active).count();
            eprintln!(
                "[picus-gb-stats F4] pairs={} cop={} gm={} b={} red={} useful={} useless={} initial_open={} basis_size={} active={} time_run_ms={:.2}",
                s.pairs_generated,
                s.pairs_killed_coprime,
                s.pairs_killed_gm,
                s.pairs_killed_b,
                s.reductions_total,
                s.reductions_useful,
                s.reductions_useless,
                initial_open_size,
                self.basis.len(),
                active_count,
                total_ns as f64 / 1e6,
            );
        }
        Ok(())
    }
}

mod incremental;
pub use incremental::IncrementalGB;

// ─── Polynomial coefficient lookup ─────────────────────────────────────────

/// Look up the coefficient at a specific monomial within a polynomial,
/// using binary search over the polynomial's descending term order.
/// Used by `crate::ideal::Ideal::min_poly_cancel`'s Gaussian elimination.
pub(crate) fn poly_coefficient_at(p: &Polynomial, mon: &Monomial, ring: &PolyRing) -> FieldElem {
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

    fn mk_basis_elem(lt_exps: Vec<u16>, ring: &PolyRing) -> BasisElement {
        let lt = Monomial::from_exponents(lt_exps);
        let lt_divmask = ring.divmask.compute(&lt);
        BasisElement {
            poly: Polynomial::zero(),
            lt,
            lt_divmask,
            active: true,
            sugar: 0,
        }
    }

    fn mk_pair_ij(
        i: usize,
        j: usize,
        basis: &[BasisElement],
        ring: &PolyRing,
        age: u64,
    ) -> SPair {
        let lcm = basis[i].lt.lcm(&basis[j].lt);
        let lcm_divmask = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        SPair {
            i,
            j,
            sugar: lcm_deg,
            lcm,
            lcm_divmask,
            lcm_deg,
            age,
            generation: 0,
            is_coprime: basis[i].lt.is_coprime(&basis[j].lt),
        }
    }

    #[test]
    fn b_criterion_kills_when_all_three_conditions_hold() {
        // basis = [x^2, y^2]; pair (0,1) has lcm = x^2*y^2.
        // new_lt = x*y. Conditions:
        //   1. x*y | x^2*y^2: yes.
        //   2. lcm(y^2, x*y) = x*y^2 ≠ x^2*y^2: holds.
        //   3. lcm(x^2, x*y) = x^2*y ≠ x^2*y^2: holds.
        // → killed.
        let r = ring(3);
        let basis = vec![
            mk_basis_elem(vec![2, 0, 0], &r),
            mk_basis_elem(vec![0, 2, 0], &r),
        ];
        let mut pairs = vec![mk_pair_ij(0, 1, &basis, &r, 1)];
        let new_lt = Monomial::from_exponents(vec![1, 1, 0]);
        let new_lt_dm = r.divmask.compute(&new_lt);
        b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
        assert!(pairs.is_empty(), "pair should have been killed");
    }

    #[test]
    fn b_criterion_keeps_when_new_lt_does_not_divide_lcm() {
        // basis = [x^2, y^2]; lcm = x^2*y^2; new_lt = z (no shared variable).
        // Condition 1 fails: z does not divide x^2*y^2 → keep.
        let r = ring(3);
        let basis = vec![
            mk_basis_elem(vec![2, 0, 0], &r),
            mk_basis_elem(vec![0, 2, 0], &r),
        ];
        let mut pairs = vec![mk_pair_ij(0, 1, &basis, &r, 1)];
        let new_lt = Monomial::from_exponents(vec![0, 0, 1]);
        let new_lt_dm = r.divmask.compute(&new_lt);
        b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
        assert_eq!(pairs.len(), 1, "pair should be kept (cond 1 fails)");
    }

    #[test]
    fn b_criterion_keeps_when_lcm_lt_j_new_equals_lcm() {
        // basis = [x, y]; lcm = x*y; new_lt = x.
        //   1. x | x*y: yes.
        //   2. lcm(LT_j, new_lt) = lcm(y, x) = x*y = pair.lcm → cond 2 fails.
        // → keep.
        let r = ring(3);
        let basis = vec![
            mk_basis_elem(vec![1, 0, 0], &r),
            mk_basis_elem(vec![0, 1, 0], &r),
        ];
        let mut pairs = vec![mk_pair_ij(0, 1, &basis, &r, 1)];
        let new_lt = Monomial::from_exponents(vec![1, 0, 0]);
        let new_lt_dm = r.divmask.compute(&new_lt);
        b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
        assert_eq!(pairs.len(), 1, "pair should be kept (cond 2 fails)");
    }

    #[test]
    fn b_criterion_keeps_when_lcm_lt_i_new_equals_lcm() {
        // basis = [x, y]; lcm = x*y; new_lt = y.
        //   1. y | x*y: yes.
        //   2. lcm(LT_j, new_lt) = lcm(y, y) = y ≠ x*y → cond 2 holds.
        //   3. lcm(LT_i, new_lt) = lcm(x, y) = x*y → cond 3 fails.
        // → keep.
        let r = ring(3);
        let basis = vec![
            mk_basis_elem(vec![1, 0, 0], &r),
            mk_basis_elem(vec![0, 1, 0], &r),
        ];
        let mut pairs = vec![mk_pair_ij(0, 1, &basis, &r, 1)];
        let new_lt = Monomial::from_exponents(vec![0, 1, 0]);
        let new_lt_dm = r.divmask.compute(&new_lt);
        b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
        assert_eq!(pairs.len(), 1, "pair should be kept (cond 3 fails)");
    }

    #[test]
    fn b_criterion_empty_queue_is_noop() {
        let r = ring(3);
        let basis: Vec<BasisElement> = Vec::new();
        let mut pairs: Vec<SPair> = Vec::new();
        let new_lt = Monomial::from_exponents(vec![1, 1, 0]);
        let new_lt_dm = r.divmask.compute(&new_lt);
        b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
        assert!(pairs.is_empty());
    }
}
