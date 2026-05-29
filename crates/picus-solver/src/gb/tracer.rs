//! UNSAT core tracing via Buchberger observer hooks.
//!
//! Hooks into the [`BuchbergerObserver`] callbacks to build a polynomial
//! dependency DAG, then BFS-traces from a target basis element back to
//! the original input polynomials responsible for it.
//!
//! Each basis element maintains the set of original input indices it
//! transitively depends on. When the GB is trivial (contains a
//! constant), the dependency set of that constant is the UNSAT core.

use std::collections::BTreeSet;

use crate::ff::buchberger::BuchbergerObserver;
use crate::ff::polynomial::DensePoly;

/// DensePoly dependency tracker for a Buchberger computation.
///
/// After the computation finishes, call [`GbTracer::unsat_core_for`] to
/// extract the input indices responsible for any particular basis
/// element (typically the constant `1` in an UNSAT scenario).
pub struct GbTracer {
    /// Number of original input generators (before inter-reduce).
    n_inputs: usize,
    /// For each basis element (indexed sequentially as they are added by
    /// Buchberger), the set of original input indices it depends on.
    deps: Vec<BTreeSet<usize>>,
    /// Count of `on_initial_basis` events seen so far. Each such event
    /// corresponds to one original input being introduced into the
    /// computation, in order. This is the input-index assigned to the
    /// next initial-basis element.
    input_count: usize,
    /// Reducer-basis indices reported by the most recent
    /// `on_initial_reducers` call. Consumed (and cleared) by the very
    /// next `on_initial_basis` event so the new entry's deps include
    /// everything its reducers transitively depend on. This is sound
    /// over-approximation when Buchberger's `add_generators` reduces the
    /// new generator before recording it as an initial basis element.
    pending_reducers: Vec<usize>,
    /// Reducer-basis indices reported by the most recent
    /// `on_pair_reducers` call. Consumed (and cleared) by the next
    /// `on_new_poly` event so the new S-pair-derived entry's deps
    /// include the reducers that participated in NF computation.
    pending_pair_reducers: Vec<usize>,
}

impl GbTracer {
    /// Create a new tracer for a system with `n_inputs` original
    /// generator polynomials.
    pub fn new(n_inputs: usize) -> Self {
        GbTracer {
            n_inputs,
            deps: Vec::new(),
            input_count: 0,
            pending_reducers: Vec::new(),
            pending_pair_reducers: Vec::new(),
        }
    }

    /// Return the UNSAT core for the element at `basis_idx`:
    /// the sorted input indices that this element transitively depends on.
    ///
    /// Returns a trivial core (all inputs) if `basis_idx` is out of range.
    pub fn unsat_core_for(&self, basis_idx: usize) -> Vec<usize> {
        match self.deps.get(basis_idx) {
            Some(set) => set.iter().copied().collect(),
            None => (0..self.n_inputs).collect(),
        }
    }

    /// Total number of basis elements tracked (initial + derived).
    pub fn basis_count(&self) -> usize {
        self.deps.len()
    }
}

impl BuchbergerObserver for GbTracer {
    fn on_initial_reducers(&mut self, reducer_indices: &[usize]) {
        // Cache the reducer set; the very next `on_initial_basis` will
        // consume it to over-approximate the new entry's deps.
        self.pending_reducers.clear();
        self.pending_reducers.extend_from_slice(reducer_indices);
    }

    fn on_initial_basis(&mut self, _idx: usize, _poly: &DensePoly) {
        // Each `on_initial_basis` event corresponds to introducing one
        // original input poly. We assign it the next input index in
        // sequence (`input_count`), independent of how many derived
        // polynomials may have been pushed to `deps` by prior S-pair work.
        let i = self.input_count;
        let mut s = BTreeSet::new();
        if i < self.n_inputs {
            s.insert(i);
        } else {
            // Out-of-range: conservatively depend on all inputs.
            for k in 0..self.n_inputs {
                s.insert(k);
            }
        }
        // Sound over-approximation: the new entry equals
        //   g_red = g - sum(q_i * b_i)
        // where each b_i is an active reducer at call time. Any input
        // those reducers depend on transitively appears in `g_red`'s deps.
        for &r_idx in &self.pending_reducers {
            if let Some(set) = self.deps.get(r_idx) {
                s.extend(set.iter().copied());
            }
        }
        self.pending_reducers.clear();
        self.deps.push(s);
        self.input_count += 1;
    }

    fn on_pair_reducers(&mut self, reducer_indices: &[usize]) {
        self.pending_pair_reducers.clear();
        self.pending_pair_reducers.extend_from_slice(reducer_indices);
    }

    fn on_new_poly(&mut self, _idx: usize, _poly: &DensePoly, from_pair: (usize, usize)) {
        // New basis element depends on the union of its parents' deps
        // plus the deps of any reducer that participated in the NF
        // computation (reported by the preceding `on_pair_reducers`).
        let (i, j) = from_pair;
        let mut combined = BTreeSet::new();
        if i < self.deps.len() {
            combined.extend(self.deps[i].iter().copied());
        } else {
            combined.extend(0..self.n_inputs);
        }
        if j < self.deps.len() {
            combined.extend(self.deps[j].iter().copied());
        } else {
            combined.extend(0..self.n_inputs);
        }
        for &r_idx in &self.pending_pair_reducers {
            if let Some(set) = self.deps.get(r_idx) {
                combined.extend(set.iter().copied());
            }
        }
        self.pending_pair_reducers.clear();
        self.deps.push(combined);
    }

    fn wants_inter_reduce_deps(&self) -> bool {
        crate::config::with(|c| c.track_inter_reduce_deps)
    }

    fn on_inter_reduce(&mut self, affected: usize, reducers: &[usize]) {
        // `affected` (a basis position == this tracer's deps index, since
        // every basis element is reported in order via on_initial_basis /
        // on_new_poly) was tail-reduced by `reducers`. Its reduced form is
        // a combination of itself and those reducers, so it now transitively
        // depends on every input the reducers depend on — fold them in. This
        // is the precise inter-reduce accounting (gated on
        // `track_inter_reduce_deps`): without it the element kept only its
        // pre-reduction deps, which can under-approximate the UNSAT core.
        if affected >= self.deps.len() {
            return;
        }
        let mut extra: BTreeSet<usize> = BTreeSet::new();
        for &r in reducers {
            if let Some(set) = self.deps.get(r) {
                extra.extend(set.iter().copied());
            }
        }
        self.deps[affected].extend(extra);
    }
}

#[cfg(test)]
#[path = "tracer_tests.rs"]
mod tests;
