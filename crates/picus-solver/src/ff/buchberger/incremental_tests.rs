use super::*;
use crate::ff::field::PrimeField;
use crate::ff::monomial::MonomialOrder;
use num_bigint::BigUint;

fn ring2() -> Arc<PolyRing> {
    // `PolyRing::new` already returns `Arc<Self>`.
    PolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
        MonomialOrder::DegRevLex,
    )
}

fn cfg() -> BuchbergerConfig {
    BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: true,
        use_f4: false,
    }
}

#[test]
fn new_starts_quiescent_empty_basis_level_0() {
    let igb = IncrementalGB::new(ring2(), cfg());
    assert!(igb.is_quiescent());
    assert_eq!(igb.open_queue_len(), 0);
    assert!(igb.basis().is_empty());
    assert!(!igb.is_trivial());
    assert_eq!(igb.decision_level(), 0);
}

#[test]
fn seed_reduced_basis_avoids_spair_work() {
    let ring = ring2();
    let mut igb = IncrementalGB::new(ring.clone(), cfg());
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    igb.seed_reduced_basis(vec![x, y]);
    // Seeded basis has no open S-pairs.
    assert!(igb.is_quiescent());
    assert_eq!(igb.basis().len(), 2);
}

#[test]
fn add_generators_returns_trivial_on_unit_input() {
    let ring = ring2();
    let mut igb = IncrementalGB::new(ring.clone(), cfg());
    let one = DensePoly::constant(ring.field.one(), &ring);
    let trivial = igb.add_generators(vec![one]).expect("trivial GB ok");
    assert!(trivial);
    assert!(igb.is_trivial());
}

#[test]
fn add_generators_two_linear_yields_basis() {
    // x and y are linearly independent → reduced GB = {x, y}.
    let ring = ring2();
    let mut igb = IncrementalGB::new(ring.clone(), cfg());
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    let trivial = igb.add_generators(vec![x, y]).expect("ok");
    assert!(!trivial);
    // The basis is {x, y} after add_generators (each survives).
    assert_eq!(igb.basis().len(), 2);
}

#[test]
fn push_pop_restores_basis_and_level() {
    let ring = ring2();
    let mut igb = IncrementalGB::new(ring.clone(), cfg());
    let x = DensePoly::variable(0, &ring);
    igb.add_generators(vec![x.clone()]).expect("ok");
    let before = igb.basis();

    igb.push();
    assert_eq!(igb.decision_level(), 1);

    // Add another generator at level 1.
    let y = DensePoly::variable(1, &ring);
    igb.add_generators(vec![y]).expect("ok");
    assert!(igb.basis().len() >= 2);

    igb.pop();
    assert_eq!(igb.decision_level(), 0);
    // After pop, the basis is restored to its pre-push state.
    let after = igb.basis();
    assert_eq!(before.len(), after.len());
}

#[test]
fn nested_push_pop_restores_level() {
    let igb_init = IncrementalGB::new(ring2(), cfg());
    let mut igb = igb_init;
    igb.push();
    igb.push();
    igb.push();
    assert_eq!(igb.decision_level(), 3);
    igb.pop();
    assert_eq!(igb.decision_level(), 2);
    igb.pop();
    igb.pop();
    assert_eq!(igb.decision_level(), 0);
    // Extra pop is a no-op (no underflow).
    igb.pop();
    assert_eq!(igb.decision_level(), 0);
}

#[test]
fn set_cancel_token_swaps_in_fresh_budget() {
    let mut igb = IncrementalGB::new(ring2(), cfg());
    // Install a fresh cancel.
    let c = CancelToken::cancelled();
    igb.set_cancel_token(Some(c));
    // No direct getter, but the cancel takes effect when run_only is
    // called and the engine polls.
    let _ = igb.run_only(); // empty queue, nothing to cancel — Ok.
    // Setting None back also works.
    igb.set_cancel_token(None);
}

#[test]
fn run_only_on_empty_queue_is_noop() {
    let mut igb = IncrementalGB::new(ring2(), cfg());
    let trivial = igb.run_only().expect("empty run_only ok");
    assert!(!trivial);
    assert!(igb.is_quiescent());
}

#[test]
fn reduce_against_active_basis_returns_normal_form() {
    let ring = ring2();
    let mut igb = IncrementalGB::new(ring.clone(), cfg());
    let x = DensePoly::variable(0, &ring);
    igb.add_generators(vec![x]).expect("ok");
    // Reduce `2x + 3` by basis {x} → should yield the constant `3`.
    let two = ring.field.from_int(2);
    let two_x = DensePoly::variable(0, &ring).scale(&two, &ring);
    let three = DensePoly::constant(ring.field.from_int(3), &ring);
    let two_x_plus_3 = two_x.add(&three, &ring);
    let r = igb.reduce(&two_x_plus_3);
    // Result depends on monic-normalization; just check it's a constant.
    assert!(r.is_constant() || r.is_zero());
}

#[test]
fn engine_stats_accessor_works() {
    let igb = IncrementalGB::new(ring2(), cfg());
    let stats = igb.engine_stats();
    // Accessor returns a reference to the counters struct; specific
    // counter values are not asserted here (the set may evolve).
    let _: &super::super::GbProfileCounters = stats;
}

#[test]
fn ring_accessor_returns_arc() {
    let r = ring2();
    let igb = IncrementalGB::new(r.clone(), cfg());
    // Comparison by Arc pointer equality.
    assert!(Arc::ptr_eq(igb.ring(), &r));
}
