use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

#[test]
fn test_trivial_gb() {
    // x = 0 and x = 1 over GF(17) → UNSAT
    let field = PrimeField::new(BigUint::from(17u32));
    let pr = FfPolyRing::new(field, vec!["x".into()]);

    let x = pr.var(0);
    let p1 = pr.clone_poly(&x);
    let p2 = pr.sub(x, pr.one());

    match compute_gb(&pr, vec![p1, p2]) {
        GbResult::Trivial => {}
        GbResult::NonTrivial(_) | GbResult::Timeout => panic!("expected trivial GB"),
    }
}

#[test]
fn test_nontrivial_gb() {
    // x * y = 1 over GF(17) → SAT
    let field = PrimeField::new(BigUint::from(17u32));
    let pr = FfPolyRing::new(field, vec!["x".into(), "y".into()]);

    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.one());

    match compute_gb(&pr, vec![p]) {
        GbResult::Trivial | GbResult::Timeout => panic!("expected non-trivial"),
        GbResult::NonTrivial(gb) => assert!(!gb.is_empty()),
    }
}

#[test]
fn empty_input_short_circuits_to_empty_nontrivial() {
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    match compute_gb(&pr, vec![]) {
        GbResult::NonTrivial(gb) => assert!(gb.is_empty()),
        other => panic!(
            "empty input must produce NonTrivial(empty), got {:?}",
            std::mem::discriminant(&other)
        ),
    }
}

#[test]
fn compute_gb_with_timeout_some_duration_still_completes_simple_instance() {
    // Exercises the `Some(d) → CancelToken::with_timeout` branch.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    let p = pr.sub(pr.var(0), pr.constant(pr.field().from_int(2)));
    match compute_gb_with_timeout(&pr, vec![p], Some(Duration::from_secs(5))) {
        GbResult::NonTrivial(gb) => assert!(!gb.is_empty()),
        other => panic!(
            "expected NonTrivial, got {:?}",
            std::mem::discriminant(&other)
        ),
    }
}

#[test]
fn compute_gb_with_timeout_traced_empty_input_is_nontrivial() {
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    match compute_gb_with_timeout_traced(&pr, vec![], None) {
        GbResultTraced::NonTrivial(gb) => assert!(gb.is_empty()),
        other => panic!(
            "expected NonTrivial, got {:?}",
            std::mem::discriminant(&other)
        ),
    }
}

#[test]
fn compute_gb_with_timeout_traced_unsat_returns_core() {
    // x = 0 ∧ x = 1 → UNSAT, core should reference the input set.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(17u32)), vec!["x".into()]);
    let p1 = pr.var(0);
    let p2 = pr.sub(pr.var(0), pr.one());
    match compute_gb_with_timeout_traced(&pr, vec![p1, p2], None) {
        GbResultTraced::Trivial(core) => {
            // Tracer's core is a non-empty subset of input indices.
            assert!(!core.is_empty());
            for idx in &core {
                assert!(*idx < 2);
            }
        }
        other => panic!(
            "expected Trivial(core), got {:?}",
            std::mem::discriminant(&other)
        ),
    }
}

#[test]
fn is_trivial_helper_detects_nonzero_constant() {
    // Mirror the internal is_trivial check via the public surface.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    // GB = {1} is trivial.
    let one = pr.one();
    assert!(is_trivial(&pr.ring, &[one]));
    // GB = {x} is non-trivial.
    let x = pr.var(0);
    assert!(!is_trivial(&pr.ring, &[x]));
    // GB = {} is non-trivial (empty ideal).
    assert!(!is_trivial(&pr.ring, &[]));
}
