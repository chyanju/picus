use super::*;
use crate::ff::monomial::{Monomial, MonomialOrder};

fn mono(exps: &[u16]) -> Monomial {
    Monomial::from_exponents(exps.to_vec())
}

#[test]
fn input_signature_is_unit() {
    let s = Signature::input(2, 3);
    assert_eq!(s.idx, 2);
    assert!(s.monom.is_one());
}

#[test]
fn mul_distributes_on_the_monomial_and_keeps_index() {
    let s = Signature::input(1, 3).mul(&mono(&[1, 0, 2]));
    assert_eq!(s.idx, 1);
    assert_eq!(s.monom, mono(&[1, 0, 2]));
    let s2 = s.mul(&mono(&[0, 3, 0]));
    assert_eq!(s2.monom, mono(&[1, 3, 2]));
}

#[test]
fn cmp_is_index_major_then_monomial() {
    let o = MonomialOrder::DegRevLex;
    // Higher index dominates regardless of monomial.
    let lo_idx_big = Signature { idx: 0, monom: mono(&[5, 5, 5]) };
    let hi_idx_small = Signature { idx: 1, monom: mono(&[0, 0, 0]) };
    assert_eq!(lo_idx_big.cmp(&hi_idx_small, o), std::cmp::Ordering::Less);
    // Same index falls back to the monomial order.
    let a = Signature { idx: 1, monom: mono(&[2, 0, 0]) };
    let b = Signature { idx: 1, monom: mono(&[1, 0, 0]) };
    assert_eq!(a.cmp(&b, o), std::cmp::Ordering::Greater);
    assert_eq!(a.cmp(&a, o), std::cmp::Ordering::Equal);
}

#[test]
fn divides_requires_same_index_and_monomial_divisibility() {
    let s = Signature { idx: 1, monom: mono(&[1, 0, 0]) };
    // x divides x^2 y, same index ⇒ divides.
    assert!(s.divides(&Signature { idx: 1, monom: mono(&[2, 1, 0]) }));
    // different index ⇒ never.
    assert!(!s.divides(&Signature { idx: 0, monom: mono(&[2, 1, 0]) }));
    // not divisible (no x in target) ⇒ false.
    assert!(!s.divides(&Signature { idx: 1, monom: mono(&[0, 3, 0]) }));
}
