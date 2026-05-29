use super::*;
use crate::ff::divmask::DivMaskScheme;
use std::cmp::Ordering;

fn make(i: usize, j: usize, sugar: u32, lcm_deg: u32, age: u64) -> SPair {
    // Dummy DivMask scheme + Monomial (the exact bit pattern doesn't
    // matter for these structural tests).
    let scheme = DivMaskScheme::build(2, 4);
    let lcm = Monomial::from_exponents(vec![1u16, 1u16]);
    let lcm_divmask = scheme.compute(&lcm);
    SPair {
        i,
        j,
        sugar,
        lcm,
        lcm_divmask,
        lcm_deg,
        age,
        generation: 0,
        is_coprime: false,
    }
}

#[test]
fn ordering_key_is_sugar_lcm_deg_age() {
    let p = make(0, 1, 3, 5, 7);
    assert_eq!(p.ordering_key(), (3, 5, 7));
}

#[test]
fn eq_compares_ordering_key_only() {
    let p1 = make(0, 1, 3, 5, 7);
    let p2 = make(99, 100, 3, 5, 7); // same key, different parents
    assert_eq!(p1, p2);
}

#[test]
fn ord_breaks_ties_lex_on_ordering_key() {
    // Smaller sugar wins.
    let small_sugar = make(0, 1, 2, 5, 7);
    let big_sugar = make(0, 1, 3, 5, 7);
    assert_eq!(small_sugar.cmp(&big_sugar), Ordering::Less);

    // Equal sugar, smaller lcm_deg wins.
    let small_lcm = make(0, 1, 3, 4, 7);
    let big_lcm = make(0, 1, 3, 5, 7);
    assert_eq!(small_lcm.cmp(&big_lcm), Ordering::Less);

    // Equal sugar + lcm_deg, smaller age wins.
    let small_age = make(0, 1, 3, 5, 6);
    let big_age = make(0, 1, 3, 5, 7);
    assert_eq!(small_age.cmp(&big_age), Ordering::Less);
}

#[test]
fn partial_ord_matches_ord() {
    let a = make(0, 1, 2, 5, 7);
    let b = make(0, 1, 3, 5, 7);
    assert_eq!(a.partial_cmp(&b), Some(a.cmp(&b)));
}

#[test]
fn criterion_pair_impl_exposes_lcm_parents_and_key() {
    use crate::ff::spair_criteria::CriterionPair;
    let p = make(2, 5, 3, 4, 8);
    assert_eq!(p.parents(), (2, 5));
    assert_eq!(p.cmp_key(), (3, 4, 8));
    assert_eq!(p.lcm().exponents(), &[1u16, 1u16]);
    assert!(!p.is_coprime());
}

#[test]
fn coprime_flag_is_propagated_through_criterion_trait() {
    use crate::ff::spair_criteria::CriterionPair;
    let mut p = make(0, 1, 3, 5, 7);
    p.is_coprime = true;
    assert!(p.is_coprime());
}
