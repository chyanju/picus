use super::*;

#[test]
fn test_tracer_initial_one_input_per_call() {
    let mut tracer = GbTracer::new(5);
    // Simulate add_generators calling on_initial_basis 3 times.
    let p = DensePoly::zero();
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
    let p = DensePoly::zero();
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
    assert_eq!(tracer.unsat_core_for(999), vec![0, 1, 2]);
}

#[test]
fn test_tracer_pair_reducers_fold_into_new_poly_deps() {
    // Inputs 0..4 all on basis. S-pair (0, 1) is reduced against
    // active basis members 2 and 3 — those reducers must show up
    // in the new poly's core.
    let mut tracer = GbTracer::new(4);
    let p = DensePoly::zero();
    for _ in 0..4 {
        tracer.on_initial_basis(0, &p);
    }
    tracer.on_pair_reducers(&[2, 3]);
    tracer.on_new_poly(4, &p, (0, 1));
    assert_eq!(tracer.unsat_core_for(4), vec![0, 1, 2, 3]);
    // Pending should be cleared — the next pair without reducers
    // should not inherit them.
    tracer.on_new_poly(5, &p, (0, 1));
    assert_eq!(tracer.unsat_core_for(5), vec![0, 1]);
}

#[test]
fn inter_reduce_unions_reducer_deps() {
    // Five inputs on the basis: deps[i] = {i}. Element 0 is then
    // tail-reduced using elements 2 and 3, so its core must grow to
    // {0, 2, 3} (its own dep plus the reducers'). Inputs 1, 4 stay out.
    let mut tracer = GbTracer::new(5);
    let p = DensePoly::zero();
    for _ in 0..5 {
        tracer.on_initial_basis(0, &p);
    }
    tracer.on_inter_reduce(0, &[2, 3]);
    assert_eq!(tracer.unsat_core_for(0), vec![0, 2, 3]);
    // Other elements are untouched.
    assert_eq!(tracer.unsat_core_for(1), vec![1]);
    assert_eq!(tracer.unsat_core_for(4), vec![4]);
    // Out-of-range affected index is a no-op (no panic).
    tracer.on_inter_reduce(999, &[0]);
}

#[test]
fn wants_inter_reduce_deps_reflects_config() {
    let tracer = GbTracer::new(1);
    // Mirror the live config value: the method is a pure read of
    // `track_inter_reduce_deps`.
    let cfg = crate::config::with(|c| c.track_inter_reduce_deps);
    assert_eq!(tracer.wants_inter_reduce_deps(), cfg);

    // Force the flag on, then off, under a scoped override.
    {
        let _g = crate::config::ConfigGuard::with_override(|c| c.track_inter_reduce_deps = true);
        assert!(tracer.wants_inter_reduce_deps());
    }
    {
        let _g = crate::config::ConfigGuard::with_override(|c| c.track_inter_reduce_deps = false);
        assert!(!tracer.wants_inter_reduce_deps());
    }
}

#[test]
fn initial_basis_beyond_n_inputs_depends_on_all() {
    // More `on_initial_basis` events than `n_inputs`: the over-range entry
    // (index == n_inputs) conservatively depends on every input, not on a
    // single (nonexistent) input slot.
    let mut tracer = GbTracer::new(2);
    let p = DensePoly::zero();
    // Three events, but only 2 inputs declared.
    for _ in 0..3 {
        tracer.on_initial_basis(0, &p);
    }
    assert_eq!(tracer.basis_count(), 3);
    assert_eq!(tracer.unsat_core_for(0), vec![0]);
    assert_eq!(tracer.unsat_core_for(1), vec![1]);
    // The 3rd entry (i == n_inputs == 2) falls into the else branch:
    // conservatively the union of all inputs {0, 1}.
    assert_eq!(tracer.unsat_core_for(2), vec![0, 1]);
}

#[test]
fn new_poly_with_out_of_range_parents_depends_on_all() {
    // `on_new_poly` whose parent indices exceed the current deps length
    // must fold in every input (sound over-approximation) rather than
    // index out of bounds.
    let mut tracer = GbTracer::new(3);
    let p = DensePoly::zero();
    // Only one real basis element so far (deps.len() == 1, index 0).
    tracer.on_initial_basis(0, &p);
    // Parent i = 0 (in range, deps {0}), parent j = 99 (out of range →
    // union all inputs {0,1,2}). Result = {0} ∪ {0,1,2} = {0,1,2}.
    tracer.on_new_poly(1, &p, (0, 99));
    assert_eq!(tracer.unsat_core_for(1), vec![0, 1, 2]);
    // Parent i = 99 (out of range → all inputs), parent j = 0 (deps {0}).
    tracer.on_new_poly(2, &p, (99, 0));
    assert_eq!(tracer.unsat_core_for(2), vec![0, 1, 2]);
}

#[test]
fn inter_reduce_with_empty_reducers_is_noop() {
    // An in-range affected index with no reducers leaves deps unchanged.
    let mut tracer = GbTracer::new(3);
    let p = DensePoly::zero();
    for _ in 0..3 {
        tracer.on_initial_basis(0, &p);
    }
    tracer.on_inter_reduce(1, &[]);
    assert_eq!(tracer.unsat_core_for(1), vec![1]);
}
