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
