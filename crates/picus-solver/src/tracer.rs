//! UNSAT core tracing via Buchberger observer hooks.
//!
//! Mirrors cvc5's `Tracer` class (`theory/ff/core.cpp`), which hooks into
//! Buchberger callbacks to build a polynomial dependency DAG and then
//! BFS-traces from a target basis element back to the input
//! polynomials responsible for it.
//!
//! Implements [`ff::BuchbergerObserver`]: the in-tree Buchberger observer
//! trait.  Each basis element maintains the set of *original input*
//! indices it transitively depends on.  When the GB is trivial (contains
//! a constant), reading the dependency set of that constant yields the
//! UNSAT core.

use std::collections::BTreeSet;

use crate::ff::buchberger::BuchbergerObserver;
use crate::ff::polynomial::{PolyRing, Polynomial};

/// Tracks polynomial derivation history during a Buchberger computation.
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
    /// next initial-basis element (and the value reported by
    /// `next_input_idx`).
    input_count: usize,
    /// Reducer-basis indices reported by the most recent
    /// `on_initial_reducers` call. Consumed (and cleared) by the very
    /// next `on_initial_basis` event so the new entry's deps include
    /// everything its reducers transitively depend on. This is sound
    /// over-approximation when Buchberger's `add_generators` reduces the
    /// new generator before recording it as an initial basis element.
    pending_reducers: Vec<usize>,
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
        }
    }

    /// After GB computation, retrieve the set of original input indices
    /// that basis element `basis_idx` depends on.
    pub fn deps_of(&self, basis_idx: usize) -> Option<&BTreeSet<usize>> {
        self.deps.get(basis_idx)
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

    /// Save the current state so we can later truncate back. The returned
    /// opaque value pairs `deps.len()` (low 32 bits) with `input_count`
    /// (high 32 bits) so a single integer round-trips through `restore`.
    /// Used in lockstep with `IncrementalGB::push`.
    pub fn checkpoint(&self) -> usize {
        // Pack: high 32 bits = input_count, low 32 bits = deps.len().
        // Both fit easily for any realistic split-DFS run (n_vars < 2^16).
        debug_assert!(self.deps.len() < (1usize << 32));
        debug_assert!(self.input_count < (1usize << 32));
        (self.input_count << 32) | self.deps.len()
    }

    /// Truncate `deps` and reset `input_count` back to a previously-saved
    /// state. Used in lockstep with `IncrementalGB::pop` to undo any
    /// `on_*` events that occurred after the matching `checkpoint()`.
    pub fn restore(&mut self, saved: usize) {
        let saved_deps_len = saved & 0xFFFF_FFFF;
        let saved_input_count = saved >> 32;
        if saved_deps_len <= self.deps.len() {
            self.deps.truncate(saved_deps_len);
        }
        if saved_input_count <= self.input_count {
            self.input_count = saved_input_count;
        }
    }

    /// Logical input index assigned to the *next* call to `on_initial_basis`.
    /// Useful for callers that need to remember "this frame's `assign_poly`
    /// was input index N" before calling `add_generators_observed`.
    pub fn next_input_idx(&self) -> usize {
        self.input_count
    }

    /// Find the union of dependency sets across all *constant* basis
    /// elements.  Returns `None` if no constant is present.
    pub fn unsat_core_for_trivial(
        &self,
        basis: &[Polynomial],
        ring: &PolyRing,
    ) -> Option<Vec<usize>> {
        let mut combined: BTreeSet<usize> = BTreeSet::new();
        let mut found = false;
        for (idx, p) in basis.iter().enumerate() {
            if !p.is_zero() && p.is_constant(ring) {
                found = true;
                if let Some(set) = self.deps.get(idx) {
                    combined.extend(set.iter().copied());
                }
            }
        }
        if found {
            Some(combined.into_iter().collect())
        } else {
            None
        }
    }
}

impl BuchbergerObserver for GbTracer {
    fn on_initial_reducers(&mut self, reducer_indices: &[usize]) {
        // Cache the reducer set; the very next `on_initial_basis` will
        // consume it to over-approximate the new entry's deps.
        self.pending_reducers.clear();
        self.pending_reducers.extend_from_slice(reducer_indices);
    }

    fn on_initial_basis(&mut self, _idx: usize, _poly: &Polynomial) {
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

    fn on_new_poly(&mut self, _idx: usize, _poly: &Polynomial, from_pair: (usize, usize)) {
        // New basis element depends on the union of its parents' deps.
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
        self.deps.push(combined);
    }

    fn on_inter_reduce(&mut self, old_idx: usize, new_idx: usize) {
        // Inter-reduce replaces basis[old_idx] with a new reduced form
        // (recorded under new_idx by Buchberger).  The new form depends
        // on at least everything the old one did.  Without observing the
        // exact reducers used we under-approximate by carrying the old
        // deps forward; this is sufficient for trivial-core extraction
        // because the trivial element's parents are tracked precisely
        // via on_new_poly.
        let combined = if old_idx < self.deps.len() {
            self.deps[old_idx].clone()
        } else {
            (0..self.n_inputs).collect()
        };
        // Pad deps so deps[new_idx] is well-defined.
        while self.deps.len() <= new_idx {
            self.deps.push(BTreeSet::new());
        }
        self.deps[new_idx] = combined;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tracer_initial_one_input_per_call() {
        let mut tracer = GbTracer::new(5);
        // Simulate add_generators calling on_initial_basis 3 times.
        let p = Polynomial::zero();
        for _ in 0..3 {
            tracer.on_initial_basis(0, &p);
        }
        assert_eq!(tracer.basis_count(), 3);
        assert_eq!(tracer.unsat_core_for(0), vec![0]);
        assert_eq!(tracer.unsat_core_for(1), vec![1]);
        assert_eq!(tracer.unsat_core_for(2), vec![2]);
    }

    #[test]
    fn test_tracer_derived_narrows_core() {
        let mut tracer = GbTracer::new(4);
        let p = Polynomial::zero();
        for _ in 0..4 {
            tracer.on_initial_basis(0, &p);
        }
        // S-pair from (0, 1) → derived element at index 4
        tracer.on_new_poly(4, &p, (0, 1));
        assert_eq!(tracer.unsat_core_for(4), vec![0, 1]);
        // S-pair from (2, 4) → derived element at index 5
        tracer.on_new_poly(5, &p, (2, 4));
        assert_eq!(tracer.unsat_core_for(5), vec![0, 1, 2]);
        // Input 3 is NOT in the core.
    }

    #[test]
    fn test_tracer_out_of_range_returns_trivial_core() {
        let tracer = GbTracer::new(3);
        assert!(tracer.deps_of(999).is_none());
        assert_eq!(tracer.unsat_core_for(999), vec![0, 1, 2]);
    }
}
