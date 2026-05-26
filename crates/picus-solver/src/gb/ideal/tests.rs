use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

#[test]
fn test_contains_simple() {
    // I = (x - 3) over GF(17). Then (x^2 - 9) ∈ I, but x ∉ I.
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let three = pr.field().from_int(3);
    let nine = pr.field().from_int(9);
    let p1 = pr.sub(pr.var(0), pr.constant(three));
    let ideal = Ideal::new(&pr, vec![p1]);

    let x = pr.var(0);
    let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let x2_minus_9 = pr.sub(x2, pr.constant(nine));
    assert!(ideal.contains(&x2_minus_9));
    assert!(!ideal.contains(&x));
}

#[test]
fn test_whole_ring() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let one = pr.one();
    let ideal = Ideal::new(&pr, vec![one]);
    assert!(ideal.is_whole_ring());
    assert!(ideal.is_zero_dim());
}

#[test]
fn test_is_zero_dim_yes() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let one = pr.field().from_int(1);
    let two = pr.field().from_int(2);
    let p1 = pr.sub(pr.var(0), pr.constant(one));
    let p2 = pr.sub(pr.var(1), pr.constant(two));
    let ideal = Ideal::new(&pr, vec![p1, p2]);
    assert!(ideal.is_zero_dim());
}

#[test]
fn test_is_zero_dim_no() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let ideal = Ideal::new(&pr, vec![xy]);
    assert!(!ideal.is_zero_dim());
}

#[test]
fn test_min_poly_constant_var() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let five = pr.field().from_int(5);
    let p1 = pr.sub(pr.var(0), pr.constant(five));
    let ideal = Ideal::new(&pr, vec![p1]);
    let mp = ideal.min_poly(0).expect("zero-dim, should have minpoly");
    assert_eq!(mp.len(), 2);
    let fp = &pr.field();
    let neg_five = fp.neg(&pr.field().from_int(5));
    assert!(fp.eq_el(&mp[0], &neg_five));
    assert!(fp.is_one(&mp[1]));
}

#[test]
fn test_min_poly_quadratic() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let x = pr.var(0);
    let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let one = pr.one();
    let p = pr.sub(x2, one);
    let ideal = Ideal::new(&pr, vec![p]);
    let mp = ideal.min_poly(0).expect("zero-dim, should have minpoly");
    assert_eq!(mp.len(), 3);
    let fp = &pr.field();
    let neg_one = fp.neg(&fp.one());
    assert!(fp.eq_el(&mp[0], &neg_one));
    assert!(fp.is_zero(&mp[1]));
    assert!(fp.is_one(&mp[2]));
}

#[test]
fn test_normalize() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let three = pr.field().from_int(3);
    let six = pr.field().from_int(6);
    let term1 = pr.scale(three, pr.var(0));
    let p = pr.add(term1, pr.constant(six));
    let ideal = Ideal::new(&pr, vec![]);
    let normalized = ideal.normalize(&p);
    let lc = leading_coefficient(&pr.ring, &normalized, FfOrder::DegRevLex);
    assert!(pr.field().is_one(&lc));
}
