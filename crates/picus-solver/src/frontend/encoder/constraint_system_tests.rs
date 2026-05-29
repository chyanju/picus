use super::*;

fn b() -> ConstraintSystemBuilder {
    ConstraintSystemBuilder::new(BigUint::from(7u32))
}

#[test]
fn new_starts_empty() {
    let cs = b();
    assert_eq!(cs.n_vars(), 0);
    assert!(cs.var_names().is_empty());
    assert_eq!(cs.prime(), &BigUint::from(7u32));
}

#[test]
fn var_interns_idempotently() {
    let mut cs = b();
    let x1 = cs.var("x");
    let y = cs.var("y");
    let x2 = cs.var("x"); // repeated
    assert_eq!(x1, x2);
    assert_ne!(x1, y);
    assert_eq!(cs.n_vars(), 2);
    assert_eq!(cs.var_names(), &["x".to_string(), "y".to_string()]);
}

#[test]
fn set_prime_updates_in_place() {
    let mut cs = b();
    assert_eq!(cs.prime(), &BigUint::from(7u32));
    cs.set_prime(BigUint::from(11u32));
    assert_eq!(cs.prime(), &BigUint::from(11u32));
}

#[test]
fn add_equality_collects() {
    let mut cs = b();
    let x = cs.var("x");
    cs.add_equality(vec![PolyTerm {
        coeff: BigUint::from(1u32),
        vars: vec![(x, 1)],
    }]);
    let built = cs.build();
    assert_eq!(built.equalities.len(), 1);
}

#[test]
fn add_disequality_collects() {
    let mut cs = b();
    let x = cs.var("x");
    let y = cs.var("y");
    cs.add_disequality(x, y);
    let built = cs.build();
    assert_eq!(built.disequalities.len(), 1);
    assert_eq!(built.disequalities[0], (x, y));
}

#[test]
fn add_assignment_collects() {
    let mut cs = b();
    let x = cs.var("x");
    cs.add_assignment(x, BigUint::from(3u32));
    let built = cs.build();
    assert_eq!(built.assignments.len(), 1);
    assert_eq!(built.assignments[0], (x, BigUint::from(3u32)));
}

#[test]
fn add_bitsum_collects() {
    let mut cs = b();
    let b0 = cs.var("b0");
    let b1 = cs.var("b1");
    cs.add_bitsum(vec![b0, b1]);
    let built = cs.build();
    assert_eq!(built.bitsums.len(), 1);
    assert_eq!(built.bitsums[0], vec![b0, b1]);
}

#[test]
fn set_add_field_polys_is_off_by_default() {
    let cs = b().build();
    assert!(!cs.add_field_polys);
}

#[test]
fn set_add_field_polys_carries_through_build() {
    let mut cs = b();
    cs.set_add_field_polys(true);
    let built = cs.build();
    assert!(built.add_field_polys);
}

#[test]
fn fresh_disequality_vars_creates_one_d_and_shared_zero() {
    let mut cs = b();
    let mut seq = 0usize;
    let mut zero_idx: Option<VarIdx> = None;
    let (d0, z0) = cs.fresh_disequality_vars(&mut seq, &mut zero_idx);
    assert_eq!(seq, 1);
    assert_eq!(zero_idx, Some(z0));
    // Second call reuses __zero, allocates fresh d.
    let (d1, z1) = cs.fresh_disequality_vars(&mut seq, &mut zero_idx);
    assert_eq!(seq, 2);
    assert_eq!(z0, z1); // shared __zero
    assert_ne!(d0, d1); // distinct d's
    // __zero gets a `=0` assignment pinned on first call.
    let built = cs.build();
    assert_eq!(built.assignments.len(), 1);
    assert_eq!(built.assignments[0].1, BigUint::from(0u32));
}

#[test]
fn fresh_disequality_d_names_are_indexed_per_seq() {
    let mut cs = b();
    let mut seq = 5usize; // start partway through
    let mut zero_idx: Option<VarIdx> = None;
    let _ = cs.fresh_disequality_vars(&mut seq, &mut zero_idx);
    let _ = cs.fresh_disequality_vars(&mut seq, &mut zero_idx);
    assert_eq!(seq, 7);
    // The d-vars are named __diseq_d_5, __diseq_d_6.
    assert!(cs.var_names().contains(&"__diseq_d_5".to_string()));
    assert!(cs.var_names().contains(&"__diseq_d_6".to_string()));
}
