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
use crate::EngineError;
use crate::metric;

use super::divmask::DivMask;
use super::field::FieldElem;
#[cfg(test)]
use super::field::PrimeField;
use super::monomial::{Monomial, MonomialOrder};
use super::polynomial::{PolyRing, DensePoly, ReducerIndex};
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
    /// Default: the `use_f4` config value (compiled default `false`).
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

/// F4-lite default toggle. Reads
/// [`crate::config::RuntimeConfig::use_f4`]. Used by all default
/// `BuchbergerConfig` construction sites so the F4 path is consistently
/// enabled or disabled across the solver.
pub fn use_f4_default() -> bool {
    crate::config::with(|c| c.use_f4)
}

/// A computed Groebner basis.
#[derive(Clone, Debug)]
pub struct GBasis {
    pub basis: Vec<DensePoly>,
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
    fn on_initial_basis(&mut self, _idx: usize, _poly: &DensePoly) {}
    /// Called immediately before [`on_new_poly`] to report the
    /// active-basis indices that contributed to reducing the
    /// S-polynomial to its normal form. Observers must fold these
    /// reducers' deps into the new entry; the two pair parents alone
    /// under-approximate the dependency set.
    fn on_pair_reducers(&mut self, _reducer_indices: &[usize]) {}
    fn on_new_poly(&mut self, _idx: usize, _poly: &DensePoly, _from_pair: (usize, usize)) {}
    /// True if the engine should track inter-reduction reducer dependencies
    /// and report them via [`on_inter_reduce`]. Off by default — the extra
    /// counted reduction in `tail_reduce_active` costs a little, so only
    /// observers that consume precise inter-reduce deps opt in.
    fn wants_inter_reduce_deps(&self) -> bool { false }
    /// Reports that basis element `affected` (a basis position) was
    /// tail-reduced using the elements at the given `reducer` basis
    /// positions. Observers fold the reducers' deps into `affected`'s.
    fn on_inter_reduce(&mut self, _affected: usize, _reducers: &[usize]) {}
}

/// No-op observer.
pub struct NoObserver;
impl BuchbergerObserver for NoObserver {}

/// Internal basis element. Visible to the `incremental` submodule and
/// the `spair_criteria::LeadingTerms` impl so they can index into the
/// `BuchbergerState::basis` slice.
#[derive(Clone, Debug)]
pub(super) struct BasisElement {
    pub(super) poly: DensePoly,
    pub(super) lt: Monomial,
    /// Divisibility fingerprint of `lt`. Read by `run_f4` when
    /// constructing `F4BasisRef`; the F4 symbolic-preprocessing
    /// path uses it as a constant-time prefilter before the
    /// O(n_vars) `Monomial::divides` check.
    pub(super) lt_divmask: DivMask,
    /// Lazily deactivated when superseded by a smaller-LT element.
    pub(super) active: bool,
    /// Sugar degree at the time this element was added.
    pub(super) sugar: u32,
    /// Cumulative reducer-usage count. Incremented each time this
    /// element is selected as the divisor in a `reduce_by_refs_geobucket`
    /// iteration. Used to bias the divisor scan order toward
    /// frequently-selected reducers (cache locality).
    pub(super) use_count: u64,
}

// ─────────────────────────── Public entry points ───────────────────────────

/// Compute a Groebner basis of `generators` from scratch.
pub fn groebner_basis(
    generators: Vec<DensePoly>,
    ring: &Arc<PolyRing>,
    config: &BuchbergerConfig,
) -> Result<GBasis, EngineError> {
    let mut state = BuchbergerState::new(ring.clone(), config.clone());
    let mut obs = NoObserver;
    state.add_generators(generators, &mut obs)?;
    state.run(&mut obs)?;
    let basis = state.finalize_basis();
    Ok(GBasis { basis, order: ring.order })
}

/// Run Buchberger with an observer (for UNSAT-core tracing).
pub fn groebner_basis_observed<O: BuchbergerObserver>(
    generators: Vec<DensePoly>,
    ring: &Arc<PolyRing>,
    config: &BuchbergerConfig,
    observer: &mut O,
) -> Result<GBasis, EngineError> {
    let mut state = BuchbergerState::new(ring.clone(), config.clone());
    state.add_generators(generators, observer)?;
    state.run(observer)?;
    let basis = state.finalize_basis();
    Ok(GBasis { basis, order: ring.order })
}

/// Extend an existing GB with new generators (re-run Buchberger from the existing basis).
pub fn groebner_basis_incremental(
    existing: GBasis,
    new_generators: Vec<DensePoly>,
    ring: &Arc<PolyRing>,
    config: &BuchbergerConfig,
) -> Result<GBasis, EngineError> {
    let mut all = existing.basis;
    all.extend(new_generators);
    groebner_basis(all, ring, config)
}

/// Inter-reduce a basis (make every element's tail reduced w.r.t. all others; make monic).
pub fn interreduce(basis: Vec<DensePoly>, ring: &Arc<PolyRing>) -> Vec<DensePoly> {
    interreduce_with_cancel(basis, ring, None)
}

/// Inter-reduce with cooperative cancellation. Returns the partially-reduced
/// basis (still valid generators, just not yet inter-reduced) on cancel.
pub fn interreduce_with_cancel(
    mut basis: Vec<DensePoly>,
    ring: &Arc<PolyRing>,
    cancel: Option<&crate::timeout::CancelToken>,
) -> Vec<DensePoly> {
    // Drop zeros and constants > 0 collapse to {1}.
    basis.retain(|p| !p.is_zero());
    // If any constant is present, the ideal is the whole ring.
    if basis.iter().any(|p| p.is_constant()) {
        return vec![DensePoly::constant(ring.field.one(), ring)];
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
            // Drop j if li divides lj. On equal leading monomials keep the
            // lowest index (`j > i`), so duplicate-LT elements — which
            // dehomogenization can produce, e.g. `h²·m` and `h·m` both
            // collapsing to `m` — are de-duplicated rather than both kept.
            if li.divides(&lj) && (li != lj || j > i) {
                keep[j] = false;
            }
        }
    }
    let mut filtered: Vec<DensePoly> = basis
        .into_iter()
        .zip(keep.iter())
        .filter_map(|(p, &k)| if k { Some(p) } else { None })
        .collect();
    // Single-pass tail reduction. After the pruning above no surviving
    // element's leading term divides another's (equal LTs are
    // de-duplicated too), so reducing each element's tail by the others
    // cannot re-introduce a monomial that another element's LT divides —
    // one pass suffices.
    let n = filtered.len();
    for i in 0..n {
        // Cancel check between elements. On cancel, the partially
        // inter-reduced basis is returned; it is still a valid
        // generator set for the same ideal.
        if let Some(c) = cancel {
            if c.is_cancelled() { break; }
        }
        let mut others: Vec<&DensePoly> = Vec::with_capacity(n.saturating_sub(1));
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
            DensePoly::zero()
        } else {
            red.make_monic(ring)
        };
    }
    filtered.retain(|p| !p.is_zero());
    filtered
}

use crate::ff::spair_criteria::{b_criterion_kill, gm_insert, merge_sorted_descending};

impl crate::ff::spair_criteria::LeadingTerms for Vec<BasisElement> {
    type Mono = Monomial;
    fn lt_at(&self, idx: usize) -> &Monomial {
        &self[idx].lt
    }
}

// ────────────────────────────── Buchberger ─────────────────────────────────

/// Per-run profiling counters. Pure telemetry: no field is read by
/// engine logic. Written only through gb-stats-gated `metric::scope!`
/// blocks, so when `gb_stats` is off they stay zero at no cost. Printed
/// to stderr at the end of [`BuchbergerState::run`] when enabled (CLI
/// `--gb-stats`); also readable by tests that enable `gb_stats`.
/// The interreduce schedule's useful-reduction count lives in the
/// separate logic field [`BuchbergerState::useful_reductions`] so that
/// disabling profiling cannot perturb the schedule.
#[derive(Clone, Debug, Default)]
pub struct GbProfileCounters {
    pub pairs_generated: u64,
    pub pairs_killed_coprime: u64,
    pub pairs_killed_gm: u64,
    pub pairs_killed_b: u64,
    pub reductions_total: u64,
    pub reductions_useful: u64,
    pub reductions_useless: u64,
    pub interreduces_run: u64,
    // F4-path counters; written by `BuchbergerState::run_f4`.
    pub f4_batches: u64,
    pub f4_pair_total: u64,
    pub f4_fallback_pairs: u64,
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
    /// Running count of useful (non-zero) reductions. Pure engine logic:
    /// drives the periodic interreduce schedule in [`Self::run`]. Held
    /// separate from [`GbProfileCounters`] so profiling can be turned off
    /// without altering the schedule. Numerically equal to
    /// `profile.reductions_useful` when profiling is on; distinct field
    /// because the schedule must not depend on profiling state.
    useful_reductions: u64,
    /// Per-run profiling counters. Written only through gb-stats-gated
    /// `metric::scope!`, so disabling `gb_stats` makes them a no-op.
    profile: GbProfileCounters,
    /// Set when every initial generator shares the same total degree.
    /// Enables periodic in-loop tail-reduction. Set by
    /// [`Self::add_generators`] based on input shape.
    input_is_homog: bool,
    /// Cached divisor index for the reducer, paired with the active-basis
    /// index list it was built for. Reused across S-pair reductions whose
    /// active set is unchanged; a mismatch forces a rebuild. Populated only
    /// when `config.reducer_index_cache` is on and the active basis reaches
    /// `ReducerIndex::SORT_THRESHOLD`.
    red_index: Option<(Vec<usize>, ReducerIndex)>,
}

/// Minimum active-basis size for use-count-based reductor reordering to
/// kick in. Below this threshold the per-call O(N log N) sort outweighs
/// the divisor-scan locality gain.
const USE_COUNT_SORT_THRESHOLD: usize = 32;

/// Minimum batch size that triggers the F4 matrix path inside
/// [`BuchbergerState::run_f4`]. Smaller batches route to the
/// per-pair geobucket path: the fixed per-batch matrix-construction
/// cost (monomial collection, column index, sparse-row encoding,
/// echelon, plus ~`basis/2` `mul_term` reducer-row constructions in
/// symbolic preprocessing) exceeds the amortisation gain below
/// this threshold.
///
/// Calibrated against `bench_f4_vs_per_pair_large` and
/// `bench_f4_non_cyclic_workloads`. `12` keeps cyclic-6 (avg 35)
/// and dense-N (10/20/30) on the F4 path, lets cyclic-5 (avg ~12)
/// straddle, and routes Katsura-4 (avg 8.3) and the diffuse-4vars
/// case to per-pair. Lower values regress Katsura-4 and diffuse-4
/// 2–3×; higher values regress cyclic-5.
const F4_MIN_BATCH: usize = 12;

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
            useful_reductions: 0,
            profile: GbProfileCounters::default(),
            input_is_homog: false,
            red_index: None,
        }
    }

    fn check_cancel(&self) -> Result<(), EngineError> {
        if let Some(t) = &self.cfg.cancel_token {
            if t.is_cancelled() {
                return Err(EngineError::Timeout);
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
    pub(super) fn seed_with_reduced_basis(&mut self, basis: Vec<DensePoly>) {
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
            self.deactivate_superseded(new_idx, &lt);
            self.basis.push(BasisElement {
                poly,
                lt,
                lt_divmask,
                active: true,
                sugar,
                use_count: 0,
            });
        }
    }

    #[metric("buchberger::add_generators")]
    pub(super) fn add_generators<O: BuchbergerObserver>(
        &mut self,
        generators: Vec<DensePoly>,
        observer: &mut O,
    ) -> Result<(), EngineError> {
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
            // At or above `USE_COUNT_SORT_THRESHOLD` the active list is
            // sorted by `use_count` descending; the inner stable LT-degree
            // sort in `reduce_by_refs_geobucket` preserves this order for
            // equal-degree ties.
            let mut active_idxs = self.active_indices();
            if active_idxs.len() >= USE_COUNT_SORT_THRESHOLD {
                active_idxs.sort_by(|&a, &b| {
                    self.basis[b].use_count.cmp(&self.basis[a].use_count)
                });
            }
            let mut use_counts = vec![0u64; active_idxs.len()];
            let mut g_red = {
                let active_refs: Vec<&DensePoly> = active_idxs
                    .iter()
                    .map(|&i| &self.basis[i].poly)
                    .collect();
                match &self.cfg.cancel_token {
                    Some(c) => g.reduce_by_refs_counted_cancel(
                        &active_refs, &self.ring, c, &mut use_counts,
                    ),
                    None => g.reduce_by_refs_counted(
                        &active_refs, &self.ring, &mut use_counts,
                    ),
                }
            };
            for (slot, &basis_i) in active_idxs.iter().enumerate() {
                self.basis[basis_i].use_count = self.basis[basis_i]
                    .use_count
                    .saturating_add(use_counts[slot]);
            }
            if let Some(c) = &self.cfg.cancel_token {
                if c.is_cancelled() {
                    return Err(EngineError::Timeout);
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
                    use_count: 0,
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
            // to become inactive (non-strict deactivation).
            self.generate_pairs_against(idx, &lt, sugar);
            // Non-strict deactivation: deactivate older elements whose LT is divisible by lt.
            self.deactivate_superseded(idx, &lt);
            self.basis.push(BasisElement { poly: g_red, lt, lt_divmask, active: true, sugar, use_count: 0 });
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
        //   2. Drop coprime pairs immediately (Buchberger product
        //      criterion: their S-poly reduces to zero via the
        //      generators). Coprime pairs do not enter `gm_insert`, so
        //      the same-LCM coprime-replacement rule does not fire;
        //      any non-coprime pair with the same LCM remains in the
        //      queue and reduces normally.
        //   3. Apply the M-criterion via `gm_insert` to the surviving
        //      non-coprime pairs.
        //   4. Apply the B-criterion to the existing open queue using
        //      the new polynomial's leading term.
        //   5. Sort surviving new_pairs descending and merge into
        //      `self.open`.
        let mut new_pairs: Vec<SPair> = Vec::with_capacity(new_idx);
        metric::def!(pairs_built);
        metric::def!(coprime_skipped);
        for k in 0..new_idx {
            if !self.basis[k].active {
                continue;
            }
            metric::bump!(pairs_built);
            let basis_k_lt = &self.basis[k].lt;
            if new_lt.is_coprime(basis_k_lt) {
                metric::bump!(coprime_skipped);
                continue;
            }
            let lcm = new_lt.lcm(basis_k_lt);
            let lcm_divmask = self.ring.divmask.compute(&lcm);
            let lcm_deg = lcm.total_degree();
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
                is_coprime: false,
            };
            gm_insert(&mut new_pairs, pair);
        }
        metric::scope! {
            self.profile.pairs_generated += pairs_built;
            self.profile.pairs_killed_coprime += coprime_skipped;
            let after_gm = new_pairs.len() as u64;
            let non_coprime = pairs_built.saturating_sub(coprime_skipped);
            self.profile.pairs_killed_gm += non_coprime.saturating_sub(after_gm);
        }
        // B-criterion: prune the existing open queue using the new
        // polynomial's leading term. Runs after `new_pairs` has been
        // built and filtered.
        let new_lt_divmask = self.ring.divmask.compute(new_lt);
        metric::def!(open_before_b = self.open.len() as u64);
        b_criterion_kill(&mut self.open, new_lt, new_lt_divmask, &self.basis);
        metric::scope! {
            self.profile.pairs_killed_b += open_before_b.saturating_sub(self.open.len() as u64);
        }
        // Merge into self.open while keeping descending sort (so pop_back
        // returns the smallest pair). new_pairs is currently in arbitrary
        // order from `gm_insert`; sort it once, then merge.
        new_pairs.sort_by(|a, b| b.cmp(a));
        merge_sorted_descending(&mut self.open, new_pairs);
    }

    /// Build the S-polynomial of `pair`:
    /// `(lcm/LT_i)·f_i − (lc_i/lc_j)·(lcm/LT_j)·f_j`, scaled so the two
    /// leading terms cancel.
    fn build_spoly(&self, pair: &SPair) -> DensePoly {
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
        part_i.sub(&part_j, &self.ring)
    }

    /// Non-strict deactivation: deactivate every active element in
    /// `0..upto` whose leading monomial is divisible by `lt`. Run after
    /// `generate_pairs_against`, so pairs involving an element about to be
    /// deactivated are still generated.
    fn deactivate_superseded(&mut self, upto: usize, lt: &Monomial) {
        for k in 0..upto {
            if self.basis[k].active && lt.divides(&self.basis[k].lt) {
                self.basis[k].active = false;
            }
        }
    }

    pub(super) fn active_polys(&self) -> Vec<DensePoly> {
        self.basis
            .iter()
            .filter(|e| e.active)
            .map(|e| e.poly.clone())
            .collect()
    }

    pub(super) fn active_poly_refs(&self) -> Vec<&DensePoly> {
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
    /// because `self.basis` is never resized).
    pub(super) fn tail_reduce_active(&mut self, track: bool) -> Vec<(usize, Vec<usize>)> {
        // Snapshot the active indices and clone their polys ONCE into a
        // workspace. We then reduce each workspace[i] by &workspace[j] for
        // j ≠ i with `reduce_by_refs`. Repeating to a fixed point isn't
        // necessary because tail reduction is monotone (each pass strictly
        // shrinks tails or leaves them unchanged).
        //
        // When `track`, a counted reduction records which other elements
        // actually reduced each one; the returned `(affected, reducers)`
        // pairs (basis positions) let the UNSAT-core tracer fold the
        // reducers' dependencies into the reduced element.
        metric::scope! { self.profile.interreduces_run += 1; }
        let active_idx: Vec<usize> = self.basis.iter()
            .enumerate()
            .filter(|(_, e)| e.active)
            .map(|(i, _)| i)
            .collect();
        let mut log: Vec<(usize, Vec<usize>)> = Vec::new();
        if active_idx.len() < 2 {
            return log;
        }
        // Workspace = active polys, in active_idx order.
        let mut workspace: Vec<DensePoly> = active_idx.iter()
            .map(|&i| self.basis[i].poly.clone())
            .collect();

        // For each i, build refs from workspace skipping i. Skip
        // already-zero entries to avoid wasted work. Each dense
        // reduction can be O(seconds) on a fat basis, so the cancel
        // token is consulted before each reduce; a cancelled request
        // returns immediately rather than completing the loop.
        let cancel_owned;
        let cancel: &crate::timeout::CancelToken = match self.cfg.cancel_token.as_ref() {
            Some(c) => c,
            None => {
                cancel_owned = crate::timeout::CancelToken::none();
                &cancel_owned
            }
        };
        for i in 0..workspace.len() {
            if cancel.is_cancelled() {
                return log;
            }
            // Other active elements (skip self / already-zero), keeping
            // their basis positions parallel for the reducer log.
            let mut others: Vec<&DensePoly> = Vec::new();
            let mut other_pos: Vec<usize> = Vec::new();
            for (j, p) in workspace.iter().enumerate() {
                if j != i && !p.is_zero() {
                    others.push(p);
                    other_pos.push(active_idx[j]);
                }
            }
            if others.is_empty() {
                continue;
            }
            let red = if track {
                let mut use_counts = vec![0u64; others.len()];
                let r = workspace[i].reduce_by_refs_counted_cancel(
                    &others, &self.ring, cancel, &mut use_counts,
                );
                let reducers: Vec<usize> = (0..other_pos.len())
                    .filter(|&k| use_counts[k] > 0)
                    .map(|k| other_pos[k])
                    .collect();
                if !reducers.is_empty() {
                    log.push((active_idx[i], reducers));
                }
                r
            } else {
                workspace[i].reduce_by_refs_cancel(&others, &self.ring, cancel)
            };
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
        log
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

    /// Reduce `s_poly` against the current active basis, returning the
    /// normal form, the active-basis index list used (reduction order), and
    /// the per-divisor use counts (parallel to that list).
    ///
    /// When `config.reducer_index_cache` is on and the active basis reaches
    /// `ReducerIndex::SORT_THRESHOLD`, the divisor index is cached in
    /// `self.red_index` and reused while the active set is unchanged (the
    /// active list stays in basis order there — the lookup is order-tolerant
    /// on a GB-shaped set). Otherwise the per-call borrowing reducer is used
    /// unchanged, keeping its `use_count`-ordered scan.
    fn reduce_spoly_against_active(
        &mut self,
        s_poly: &DensePoly,
    ) -> (DensePoly, Vec<usize>, Vec<u64>) {
        let cancel = self.cfg.cancel_token.clone();
        let mut active_idxs: Vec<usize> = (0..self.basis.len())
            .filter(|&i| self.basis[i].active)
            .collect();
        let mut use_counts = vec![0u64; active_idxs.len()];

        let use_cache = crate::config::with(|c| c.reducer_index_cache)
            && active_idxs.len() >= ReducerIndex::SORT_THRESHOLD;

        if !use_cache {
            if active_idxs.len() >= USE_COUNT_SORT_THRESHOLD {
                active_idxs.sort_by(|&a, &b| {
                    self.basis[b].use_count.cmp(&self.basis[a].use_count)
                });
            }
            let active_refs: Vec<&DensePoly> =
                active_idxs.iter().map(|&i| &self.basis[i].poly).collect();
            let active_dms: Vec<DivMask> =
                active_idxs.iter().map(|&i| self.basis[i].lt_divmask).collect();
            let nf = match cancel.as_ref() {
                Some(c) => s_poly.reduce_by_refs_counted_cancel_dms(
                    &active_refs, &self.ring, c, &mut use_counts, &active_dms,
                ),
                None => s_poly.reduce_by_refs_counted_dms(
                    &active_refs, &self.ring, &mut use_counts, &active_dms,
                ),
            };
            return (nf, active_idxs, use_counts);
        }

        // Cached path: reuse the index iff it was built for this exact active
        // set; otherwise rebuild and cache it.
        let mut cached = self.red_index.take();
        let reuse = matches!(&cached, Some((idxs, _)) if *idxs == active_idxs);
        if !reuse {
            let active_refs: Vec<&DensePoly> =
                active_idxs.iter().map(|&i| &self.basis[i].poly).collect();
            let active_dms: Vec<DivMask> =
                active_idxs.iter().map(|&i| self.basis[i].lt_divmask).collect();
            let index = ReducerIndex::build(&active_refs, &self.ring, Some(&active_dms));
            cached = Some((active_idxs.clone(), index));
        }
        let active_refs: Vec<&DensePoly> =
            active_idxs.iter().map(|&i| &self.basis[i].poly).collect();
        let index = &cached.as_ref().unwrap().1;
        #[cfg(debug_assertions)]
        debug_assert!(
            index.matches_active(&active_refs, &self.ring),
            "cached ReducerIndex is stale: active leading terms changed \
             without an active-set change"
        );
        let nf = s_poly.reduce_by_refs_geobucket_indexed(
            index, &active_refs, &self.ring, cancel.as_ref(), Some(&mut use_counts),
        );
        drop(active_refs);
        self.red_index = cached;
        (nf, active_idxs, use_counts)
    }

    #[metric("buchberger::run")]
    pub(super) fn run<O: BuchbergerObserver>(&mut self, observer: &mut O) -> Result<(), EngineError> {
        if self.cfg.use_f4 {
            return self.run_f4(observer);
        }
        if self.trivial && self.cfg.abort_on_trivial { return Ok(()); }
        // Granular per-phase timing for the gb-stats dump (profiling locals).
        metric::def!(t_spoly_ns);
        metric::def!(t_reduce_ns);
        metric::def!(t_genpairs_ns);
        metric::def!(initial_open_size = self.open.len() as u64);
        metric::stopwatch!(run_start);
        // self.open is sorted descending — `pop()` returns the smallest pair
        // (lowest sugar, then lcm_deg, then age).
        while let Some(pair) = self.open.pop() {
            if let Err(e) = self.check_cancel() {
                metric::scope! {
                    let s = &self.profile;
                    let total_ms = run_start.map(|t| t.elapsed().as_secs_f64() * 1000.0).unwrap_or(0.0);
                    let active_count = self.basis.iter().filter(|e| e.active).count();
                    eprintln!(
                        "[picus-gb-stats CANCELLED] pairs={} cop={} gm={} b={} red={} useful={} useless={} initial_open={} remaining_open={} basis_size={} active={} time_run_ms={:.2} time_spoly_ms={:.2} time_reduce_ms={:.2} time_genpairs_ms={:.2}",
                        s.pairs_generated, s.pairs_killed_coprime, s.pairs_killed_gm, s.pairs_killed_b,
                        s.reductions_total, s.reductions_useful, s.reductions_useless,
                        initial_open_size, self.open.len(), self.basis.len(), active_count,
                        total_ms,
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

            let s_poly = {
                metric::timer_local!(t_spoly_ns);
                self.build_spoly(&pair)
            };

            // Reduce against the current active basis. Reference-based
            // reduction avoids cloning every active polynomial for each
            // S-pair; the cancel-aware variant bounds the cost of a
            // single dense reduction so the caller's timeout is
            // honoured. Above `USE_COUNT_SORT_THRESHOLD`, divisors are
            // tried in `use_count` descending order; the inner stable
            // sort by LT degree preserves this for equal-degree ties.
            // Reduce against the active basis. With `reducer_index_cache` on
            // this reuses a cached divisor index across reductions whose
            // active set is unchanged (see `reduce_spoly_against_active`).
            let (mut nf, active_idxs, use_counts) = {
                metric::timer_local!(t_reduce_ns);
                let (nf_reduced, active_idxs, use_counts) =
                    self.reduce_spoly_against_active(&s_poly);
                for (slot, &basis_i) in active_idxs.iter().enumerate() {
                    self.basis[basis_i].use_count = self.basis[basis_i]
                        .use_count
                        .saturating_add(use_counts[slot]);
                }
                (nf_reduced, active_idxs, use_counts)
            };
            if let Some(c) = &self.cfg.cancel_token {
                if c.is_cancelled() {
                    metric::scope! {
                        let s = &self.profile;
                        let total_ms = run_start.map(|t| t.elapsed().as_secs_f64() * 1000.0).unwrap_or(0.0);
                        let active_count = self.basis.iter().filter(|e| e.active).count();
                        eprintln!(
                            "[picus-gb-stats CANCELLED-MIDLOOP] pairs={} cop={} gm={} b={} red={} useful={} useless={} initial_open={} remaining_open={} basis_size={} active={} time_run_ms={:.2} time_spoly_ms={:.2} time_reduce_ms={:.2} time_genpairs_ms={:.2}",
                            s.pairs_generated, s.pairs_killed_coprime, s.pairs_killed_gm, s.pairs_killed_b,
                            s.reductions_total, s.reductions_useful, s.reductions_useless,
                            initial_open_size, self.open.len(), self.basis.len(), active_count,
                            total_ms,
                            t_spoly_ns as f64 / 1e6,
                            t_reduce_ns as f64 / 1e6,
                            t_genpairs_ns as f64 / 1e6,
                        );
                    }
                    return Err(EngineError::Timeout);
                }
            }
            if nf.is_zero() {
                metric::scope! {
                    self.profile.reductions_total += 1;
                    self.profile.reductions_useless += 1;
                }
                continue;
            }
            self.useful_reductions += 1;
            metric::scope! {
                self.profile.reductions_total += 1;
                self.profile.reductions_useful += 1;
            }

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
            let pair_reducers: Vec<usize> = active_idxs
                .iter()
                .zip(use_counts.iter())
                .filter(|&(_, &c)| c > 0)
                .map(|(&i, _)| i)
                .collect();
            observer.on_pair_reducers(&pair_reducers);
            observer.on_new_poly(new_idx, &nf, (pair.i, pair.j));

            // Trivial-ideal short-circuit.
            if nf.is_constant() {
                self.trivial = true;
                self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar, use_count: 0 });
                if self.cfg.abort_on_trivial { return Ok(()); }
                continue;
            }

            // Non-strict deactivation.
            // Generate new pairs FIRST, so we don't drop pairs against
            // elements about to be deactivated.
            {
                metric::timer_local!(t_genpairs_ns);
                self.generate_pairs_against(new_idx, &lt, sugar);
            }
            self.deactivate_superseded(new_idx, &lt);
            self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar, use_count: 0 });
            // Periodic in-loop tail-reduction. Tail-reduction preserves
            // the gradedness invariant exactly for homogeneous input;
            // for non-homogeneous input it can perturb sugar-degree
            // pair selection, so it runs less often there.
            let interreduce_period: u64 = if self.input_is_homog { 32 } else { 128 };
            if self.useful_reductions > 0
                && self.useful_reductions % interreduce_period == 0
            {
                let track = observer.wants_inter_reduce_deps();
                let log = self.tail_reduce_active(track);
                for (affected, reducers) in &log {
                    observer.on_inter_reduce(*affected, reducers);
                }
            }
        }
        // Optional GB-engine telemetry: emitted only when gb-stats is on.
        metric::scope! {
            let s = &self.profile;
            let total_ms = run_start.map(|t| t.elapsed().as_secs_f64() * 1000.0).unwrap_or(0.0);
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
                total_ms,
                t_spoly_ns as f64 / 1e6,
                t_reduce_ns as f64 / 1e6,
                t_genpairs_ns as f64 / 1e6,
            );
        }
        Ok(())
    }

    #[metric("buchberger::finalize_basis")]
    fn finalize_basis(self) -> Vec<DensePoly> {
        // Take active polynomials and inter-reduce once.
        let active: Vec<DensePoly> = self
            .basis
            .into_iter()
            .filter(|e| e.active)
            .map(|e| e.poly)
            .collect();
        // If there's a constant, the basis is just {1}.
        if active.iter().any(|p| p.is_constant()) {
            return vec![DensePoly::constant(self.ring.field.one(), &self.ring)];
        }
        interreduce(active, &self.ring)
    }

    /// Per-pair S-poly construction + geobucket reduction. Shared
    /// with `run()` so `run_f4` can fall back to it for batches
    /// below [`F4_MIN_BATCH`], where the matrix-build overhead
    /// outweighs the amortization gain.
    fn process_pair_geobucket<O: BuchbergerObserver>(
        &mut self,
        pair: SPair,
        observer: &mut O,
    ) -> Result<(), EngineError> {
        let s_poly = self.build_spoly(&pair);
        let mut active_idxs: Vec<usize> = (0..self.basis.len())
            .filter(|&i| self.basis[i].active)
            .collect();
        if active_idxs.len() >= USE_COUNT_SORT_THRESHOLD {
            active_idxs.sort_by(|&a, &b| {
                self.basis[b].use_count.cmp(&self.basis[a].use_count)
            });
        }
        let mut use_counts = vec![0u64; active_idxs.len()];
        let mut nf = {
            let active_refs: Vec<&DensePoly> = active_idxs
                .iter()
                .map(|&i| &self.basis[i].poly)
                .collect();
            let active_dms: Vec<_> = active_idxs
                .iter()
                .map(|&i| self.basis[i].lt_divmask)
                .collect();
            match &self.cfg.cancel_token {
                Some(c) => s_poly.reduce_by_refs_counted_cancel_dms(
                    &active_refs, &self.ring, c, &mut use_counts, &active_dms,
                ),
                None => s_poly.reduce_by_refs_counted_dms(
                    &active_refs, &self.ring, &mut use_counts, &active_dms,
                ),
            }
        };
        for (slot, &basis_i) in active_idxs.iter().enumerate() {
            self.basis[basis_i].use_count = self.basis[basis_i]
                .use_count
                .saturating_add(use_counts[slot]);
        }
        if let Some(c) = &self.cfg.cancel_token {
            if c.is_cancelled() {
                return Err(EngineError::Timeout);
            }
        }
        if nf.is_zero() {
            metric::scope! {
                self.profile.reductions_total += 1;
                self.profile.reductions_useless += 1;
            }
            return Ok(());
        }
        self.useful_reductions += 1;
        metric::scope! {
            self.profile.reductions_total += 1;
            self.profile.reductions_useful += 1;
        }
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
        let pair_reducers: Vec<usize> = active_idxs
            .iter()
            .zip(use_counts.iter())
            .filter(|&(_, &c)| c > 0)
            .map(|(&i, _)| i)
            .collect();
        observer.on_pair_reducers(&pair_reducers);
        observer.on_new_poly(new_idx, &nf, (pair.i, pair.j));

        if nf.is_constant() {
            self.trivial = true;
            self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar, use_count: 0 });
            if self.cfg.abort_on_trivial { return Ok(()); }
            return Ok(());
        }

        self.generate_pairs_against(new_idx, &lt, sugar);
        self.deactivate_superseded(new_idx, &lt);
        self.basis.push(BasisElement { poly: nf, lt, lt_divmask, active: true, sugar, use_count: 0 });
        Ok(())
    }

    /// F4-lite main loop. Pops a batch of same-sugar S-pairs and
    /// reduces them simultaneously via [`f4::process_batch`], then
    /// integrates each new generator (generating cross-pairs against
    /// the existing basis exactly as the per-pair path does).
    fn run_f4<O: BuchbergerObserver>(&mut self, observer: &mut O) -> Result<(), EngineError> {
        if self.trivial && self.cfg.abort_on_trivial {
            return Ok(());
        }
        metric::stopwatch!(run_start);
        metric::def!(initial_open_size = self.open.len() as u64);

        // Per-run reducer cache: monomials whose reducer-row was
        // computed in an earlier batch are reused when the cached
        // basis element is still active. See [`super::f4::F4Workspace`].
        let mut f4_workspace = super::f4::F4Workspace::new();
        // F4 counters accumulate on `self.profile`; readable from tests via
        // `IncrementalGB::engine_stats()`. Snapshot the entry values so the
        // trailing `[picus-gb-stats F4]` dump emits per-run deltas.
        metric::def!(f4_batches_entry = self.profile.f4_batches);
        metric::def!(f4_pair_total_entry = self.profile.f4_pair_total);
        metric::def!(f4_fallback_pairs_entry = self.profile.f4_fallback_pairs);

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
            // but pays the matrix-build overhead each time. Below
            // [`F4_MIN_BATCH`] pairs the fixed cost (build the
            // column index, encode rows, run echelon) exceeds the
            // gain over direct per-pair geobucket reduction, so fall
            // back to the single-pair path. The threshold is
            // calibrated against `bench_f4_vs_per_pair_large`:
            // cyclic-4 produces 3 batches of size ≤ 3 with no cache
            // reuse, so `F4_MIN_BATCH` leaves all of them on the
            // per-pair path while keeping cyclic-5 / cyclic-6
            // batches (avg 10–30 pairs) in the F4 path.
            if batch.len() < F4_MIN_BATCH {
                metric::scope! { self.profile.f4_fallback_pairs += batch.len() as u64; }
                for pair in batch {
                    self.process_pair_geobucket(pair, observer)?;
                }
                continue;
            }
            metric::scope! {
                self.profile.f4_batches += 1;
                self.profile.f4_pair_total += batch.len() as u64;
            }

            // Build F4BasisRef array (same indexing as self.basis).
            // `lt_divmask` is the precomputed divisibility fingerprint
            // that lets `symbolic_preprocess` short-circuit most
            // divisibility checks in O(1) instead of O(n_vars).
            let basis_refs: Vec<super::f4::F4BasisRef> = self
                .basis
                .iter()
                .map(|e| super::f4::F4BasisRef {
                    poly: &e.poly,
                    lt: &e.lt,
                    lt_divmask: e.lt_divmask,
                    active: e.active,
                })
                .collect();

            let batch_refs: Vec<&SPair> = batch.iter().collect();
            // When `f4_sparse_reducer_cache` is OFF, hand a fresh
            // workspace per batch so cross-batch reducer reuse is
            // disabled (the dense reducer cache still amortises within
            // a single batch via the same scratch allocators); when
            // ON, the workspace declared at `run_f4` entry carries the
            // cache across batches.
            let new_polys = if picus_core::config::with(|c| c.f4_sparse_reducer_cache) {
                super::f4::process_batch_with_workspace(
                    &batch_refs,
                    &basis_refs,
                    &self.ring,
                    self.cfg.cancel_token.as_ref(),
                    &mut f4_workspace,
                )
            } else {
                super::f4::process_batch(
                    &batch_refs,
                    &basis_refs,
                    &self.ring,
                    self.cfg.cancel_token.as_ref(),
                )
            };

            self.check_cancel()?;

            // Stats: each batch entry counts as one reduction. Useful
            // = produced a new generator; useless = produced nothing.
            self.useful_reductions += new_polys.len() as u64;
            metric::scope! {
                self.profile.reductions_total += batch.len() as u64;
                self.profile.reductions_useful += new_polys.len() as u64;
                if batch.len() >= new_polys.len() {
                    self.profile.reductions_useless += (batch.len() - new_polys.len()) as u64;
                }
            }

            // Integrate each new generator. F4 monic-normalises every
            // output and the matrix echelon guarantees the residue's
            // LT is not divisible by any active basis LT (symbolic
            // preprocessing is closed under reducibility).
            //
            // Provenance routing: each [`F4Output`] names the input
            // pairs and reducer basis indices whose rows linearly
            // combined into this generator. The observer contract
            // takes a single `from_pair: (usize, usize)` plus a
            // separate `on_pair_reducers(&[basis_idx])`. The first
            // contributing pair anchors `from_pair`; every other
            // contributing pair's `i` / `j` plus all reducer basis
            // indices feed `on_pair_reducers`. `GbTracer` unions
            // both sides into the new entry's deps.
            let batch_sugar = lowest_sugar;
            for output in new_polys {
                self.check_cancel()?;
                let super::f4::F4Output { poly, from_pairs, from_reducers } = output;
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
                let (from_pair, mut reducer_deps) = match from_pairs.first() {
                    Some(&pi) if pi < batch.len() => {
                        let mut extras: Vec<usize> = Vec::new();
                        for &other_pi in from_pairs.iter().skip(1) {
                            if other_pi < batch.len() {
                                extras.push(batch[other_pi].i);
                                extras.push(batch[other_pi].j);
                            }
                        }
                        ((batch[pi].i, batch[pi].j), extras)
                    }
                    _ => ((0, 0), Vec::new()),
                };
                reducer_deps.extend(from_reducers.into_iter());
                observer.on_pair_reducers(&reducer_deps);
                observer.on_new_poly(new_idx, &poly, from_pair);

                if poly.is_constant() {
                    self.trivial = true;
                    self.basis.push(BasisElement {
                        poly,
                        lt,
                        lt_divmask,
                        active: true,
                        sugar,
                        use_count: 0,
                    });
                    if self.cfg.abort_on_trivial {
                        return Ok(());
                    }
                    continue;
                }

                self.generate_pairs_against(new_idx, &lt, sugar);
                self.deactivate_superseded(new_idx, &lt);
                self.basis.push(BasisElement {
                    poly,
                    lt,
                    lt_divmask,
                    active: true,
                    sugar,
                    use_count: 0,
                });
            }
        }

        metric::scope! {
            let s = &self.profile;
            let total_ms = run_start.map(|t| t.elapsed().as_secs_f64() * 1000.0).unwrap_or(0.0);
            let active_count = self.basis.iter().filter(|e| e.active).count();
            // Per-run deltas; the stats struct accumulates across all
            // `run_f4` invocations on the same `BuchbergerState`.
            let f4_batches_delta = self.profile.f4_batches - f4_batches_entry;
            let f4_pair_total_delta = self.profile.f4_pair_total - f4_pair_total_entry;
            let f4_fallback_delta = self.profile.f4_fallback_pairs - f4_fallback_pairs_entry;
            let avg_batch = if f4_batches_delta > 0 {
                f4_pair_total_delta as f64 / f4_batches_delta as f64
            } else {
                0.0
            };
            let ws = f4_workspace.stats;
            eprintln!(
                "[picus-gb-stats F4] pairs={} cop={} gm={} b={} red={} useful={} useless={} initial_open={} basis_size={} active={} f4_batches={} f4_pair_total={} avg_batch={:.2} fallback_pairs={} cache_hits={} cache_misses={} cache_stale={} time_run_ms={:.2}",
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
                f4_batches_delta,
                f4_pair_total_delta,
                avg_batch,
                f4_fallback_delta,
                ws.reducer_hits,
                ws.reducer_misses,
                ws.reducer_stale,
                total_ms,
            );
        }
        Ok(())
    }
}

mod incremental;
pub use incremental::IncrementalGB;

// ─── DensePoly coefficient lookup ─────────────────────────────────────────

/// Look up the coefficient at a specific monomial within a polynomial,
/// using binary search over the polynomial's descending term order.
/// Used by `crate::gb::ideal::Ideal::min_poly_cancel`'s Gaussian elimination.
pub(crate) fn poly_coefficient_at(p: &DensePoly, mon: &Monomial, ring: &PolyRing) -> FieldElem {
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
        let cmp = DensePoly::cmp_term_at(mid_exps, mid_deg, target_exps, target_deg, ring.order);
        match cmp {
            std::cmp::Ordering::Equal => return coeffs[mid].clone(),
            std::cmp::Ordering::Greater => lo = mid + 1,
            std::cmp::Ordering::Less => hi = mid,
        }
    }
    ring.field.zero()
}


#[cfg(test)]
mod tests;
