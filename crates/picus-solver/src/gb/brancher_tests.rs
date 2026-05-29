use super::*;
use crate::ff::field::PrimeField;

fn field7() -> PrimeField {
    PrimeField::new(BigUint::from(7u32))
}

fn pr() -> FfPolyRing {
    FfPolyRing::new(field7(), vec!["x".into(), "y".into()])
}

// ────────── Brancher::Roots ──────────

#[test]
fn roots_brancher_pops_lifo_and_exhausts() {
    let f = field7();
    let mut b = Brancher::Roots(vec![(0, f.from_int(2)), (0, f.from_int(3))]);
    // pop pulls from the back (LIFO).
    let (v, val) = b.next(&f).expect("first");
    assert_eq!(v, 0);
    assert_eq!(f.to_biguint(&val), BigUint::from(3u32));
    let (v, val) = b.next(&f).expect("second");
    assert_eq!(v, 0);
    assert_eq!(f.to_biguint(&val), BigUint::from(2u32));
    assert!(b.next(&f).is_none());
}

#[test]
fn roots_brancher_is_always_exhaustive() {
    let b = Brancher::Roots(vec![]);
    assert!(b.is_exhaustive());
    let f = field7();
    let b = Brancher::Roots(vec![(0, f.from_int(0))]);
    assert!(b.is_exhaustive());
}

// ────────── Brancher::round_robin ──────────

#[test]
fn round_robin_small_prime_is_exhaustive() {
    let b = Brancher::round_robin(vec![0, 1], &BigUint::from(7u32));
    assert!(b.is_exhaustive());
}

#[test]
fn round_robin_large_prime_is_non_exhaustive() {
    // BN128 prime (~254 bits) → non-exhaustive (per-var cap = u64::MAX).
    let large = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap();
    let b = Brancher::round_robin(vec![0], &large);
    assert!(!b.is_exhaustive());
}

#[test]
fn round_robin_enumerates_variable_first_then_value() {
    let f = field7();
    let mut b = Brancher::round_robin(vec![0, 1], &BigUint::from(7u32));
    // First two candidates: (0, 0), (1, 0) — same value, alternating var.
    let (v, val) = b.next(&f).expect("0");
    assert_eq!(v, 0);
    assert_eq!(f.to_biguint(&val), BigUint::from(0u32));
    let (v, val) = b.next(&f).expect("1");
    assert_eq!(v, 1);
    assert_eq!(f.to_biguint(&val), BigUint::from(0u32));
    // Then (0, 1), (1, 1).
    let (v, val) = b.next(&f).expect("2");
    assert_eq!(v, 0);
    assert_eq!(f.to_biguint(&val), BigUint::from(1u32));
}

#[test]
fn round_robin_exhausts_after_total() {
    // GF(7) × 1 var → 7 candidates total then None.
    let f = field7();
    let mut b = Brancher::round_robin(vec![0], &BigUint::from(7u32));
    for _ in 0..7 {
        assert!(b.next(&f).is_some());
    }
    assert!(b.next(&f).is_none());
}

#[test]
fn round_robin_empty_unassigned_yields_none() {
    let f = field7();
    let mut b = Brancher::round_robin(vec![], &BigUint::from(7u32));
    assert!(b.next(&f).is_none());
}

// ────────── univariate_coeffs ──────────

#[test]
fn univariate_coeffs_pure_univariate() {
    // p(x) = 2x^2 + 3x + 5 over GF(7) → [5, 3, 2]
    let pr = pr();
    let f = pr.field();
    let xx = pr.mul(pr.var(0), pr.var(0));
    let coeffs_poly = pr.add(
        pr.add(
            pr.scale(f.from_int(2), xx),
            pr.scale(f.from_int(3), pr.var(0)),
        ),
        pr.constant(f.from_int(5)),
    );
    let cs = univariate_coeffs(&pr, &coeffs_poly, 0).expect("univariate");
    assert_eq!(cs.len(), 3);
    assert_eq!(f.to_biguint(&cs[0]), BigUint::from(5u32));
    assert_eq!(f.to_biguint(&cs[1]), BigUint::from(3u32));
    assert_eq!(f.to_biguint(&cs[2]), BigUint::from(2u32));
}

#[test]
fn univariate_coeffs_returns_none_when_other_var_appears() {
    let pr = pr();
    // p = x + y → not univariate in x or y alone.
    let p = pr.add(pr.var(0), pr.var(1));
    assert!(univariate_coeffs(&pr, &p, 0).is_none());
    assert!(univariate_coeffs(&pr, &p, 1).is_none());
}

#[test]
fn univariate_coeffs_constant_poly_in_variable() {
    // p = 5 viewed in x: returns Some([5]) (constant treated as deg-0
    // poly with no x dependence).
    let pr = pr();
    let f = pr.field();
    let p = pr.constant(f.from_int(5));
    let cs = univariate_coeffs(&pr, &p, 0).expect("constant is univariate");
    assert_eq!(cs.len(), 1);
    assert_eq!(f.to_biguint(&cs[0]), BigUint::from(5u32));
}
