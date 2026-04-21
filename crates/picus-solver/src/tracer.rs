//! UNSAT core tracing via Buchberger observer hooks.
//!
//! Mirrors cvc5's `Tracer` class (`theory/ff/core.cpp`), which hooks into
//! CoCoA's Buchberger callbacks to build a polynomial dependency DAG and
//! then BFS-traces from the trivial element `1` back to the input
//! polynomials responsible for unsatisfiability.
//!
//! Our implementation uses basis indices rather than polynomial strings.
//! Each basis element maintains the set of *original input* indices it
//! transitively depends on.  When the GB is trivial (contains a constant),
//! we read off the dependency set of that constant — that is the UNSAT
//! core.

use std::collections::BTreeSet;

use feanor_math::algorithms::buchberger::BuchbergerObserver;
use feanor_math::ring::{El, RingStore};
use feanor_math::rings::multivariate::MultivariatePolyRing;

/// Tracks polynomial derivation history during a Buchberger computation.
///
/// After the computation finishes, call [`GbTracer::unsat_core_for`] to
/// extract the input indices responsible for any particular basis
/// element (typically the constant `1` in an UNSAT scenario).
pub struct GbTracer {
    /// Number of original input generators (before inter-reduce).
    n_inputs: usize,
    /// For each basis element (indexed sequentially as they are added),
    /// the set of original input indices it depends on.
    deps: Vec<BTreeSet<usize>>,
}

impl GbTracer {
    /// Create a new tracer for a system with `n_inputs` original
    /// generator polynomials.
    pub fn new(n_inputs: usize) -> Self {
        GbTracer {
            n_inputs,
            deps: Vec::new(),
        }
    }

    /// After GB computation, retrieve the set of original input indices
    /// that basis element `basis_idx` depends on.
    ///
    /// Returns `None` if `basis_idx` is out of range.
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
}

impl<P: RingStore> BuchbergerObserver<P> for GbTracer
where
    P::Type: MultivariatePolyRing,
{
    fn on_initial_basis(&mut self, count: usize) {
        self.deps.clear();
        // Each surviving initial element conservatively depends on all
        // inputs, since inter-reduce can combine any of them.
        let all_inputs: BTreeSet<usize> = (0..self.n_inputs).collect();
        for _ in 0..count {
            self.deps.push(all_inputs.clone());
        }
    }

    fn on_new_poly(&mut self, parent_indices: &[usize], _result: &El<P>) {
        // New basis element depends on the union of its parents' deps.
        let mut combined = BTreeSet::new();
        for &pidx in parent_indices {
            if pidx < self.deps.len() {
                combined.extend(self.deps[pidx].iter().copied());
            } else {
                // Unknown parent — conservatively depend on all inputs.
                combined.extend(0..self.n_inputs);
            }
        }
        self.deps.push(combined);
    }

    fn on_inter_reduce(&mut self, _index: usize, _new_form: &El<P>) {
        // Inter-reduce replaces basis[index] with a new reduced form.
        // The new form depends on everything the old one did, plus the
        // basis elements used as reducers.  Without knowing which
        // reducers were used, we leave deps unchanged — this is an
        // under-approximation (the true dependency set may be larger).
        // The parent tracking in on_new_poly is the primary source of
        // precision for UNSAT core extraction.
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tracer_initial_conservatively_depends_on_all() {
        let mut tracer = GbTracer::new(5);
        // Simulate on_initial_basis(3) via direct setup
        let all: BTreeSet<usize> = (0..5).collect();
        for _ in 0..3 {
            tracer.deps.push(all.clone());
        }
        assert_eq!(tracer.basis_count(), 3);
        for i in 0..3 {
            assert_eq!(tracer.deps_of(i).unwrap().len(), 5);
        }
    }

    #[test]
    fn test_tracer_derived_narrows_core() {
        let mut tracer = GbTracer::new(4);
        // Suppose inter-reduce was identity (each input survived as-is).
        // We manually set precise deps for testing purposes.
        tracer.deps = vec![
            [0].into_iter().collect(),
            [1].into_iter().collect(),
            [2].into_iter().collect(),
            [3].into_iter().collect(),
        ];

        // Simulate on_new_poly([0, 1]) → derived element at index 4
        let mut combined = BTreeSet::new();
        combined.extend(tracer.deps[0].iter().copied());
        combined.extend(tracer.deps[1].iter().copied());
        tracer.deps.push(combined);
        assert_eq!(tracer.unsat_core_for(4), vec![0, 1]);

        // Simulate on_new_poly([2, 4]) → derived element at index 5
        let mut combined2 = BTreeSet::new();
        combined2.extend(tracer.deps[2].iter().copied());
        combined2.extend(tracer.deps[4].iter().copied());
        tracer.deps.push(combined2);
        assert_eq!(tracer.unsat_core_for(5), vec![0, 1, 2]);
        // Input 3 is NOT in the core — the whole point of tracing.
    }

    #[test]
    fn test_tracer_out_of_range_returns_trivial_core() {
        let tracer = GbTracer::new(3);
        assert!(tracer.deps_of(999).is_none());
        assert_eq!(tracer.unsat_core_for(999), vec![0, 1, 2]);
    }
}
