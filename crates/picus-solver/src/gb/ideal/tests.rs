use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

/// Multiset of leading monomials (as exponent vectors) of `basis`.
fn lm_multiset(pr: &FfPolyRing, basis: &[Poly]) -> Vec<Vec<u16>> {
    let ctx = pr.ctx();
    let n = pr.n_vars();
    let mut v: Vec<Vec<u16>> = basis
        .iter()
        .filter_map(|p| p.leading_monomial(ctx))
        .map(|m| (0..n).map(|i| m.exponent(i)).collect())
        .collect();
    v.sort();
    v
}

#[test]
fn interreduce_dedups_equal_leading_monomials() {
    // A non-minimal Gröbner basis of I = (x²-1, y²-1) over GF(17):
    // append x²+y²-2 ∈ I, whose leading monomial x² equals the first
    // generator's. `interreduce_basis` must collapse to the canonical
    // reduced GB {x²-1, y²-1} — no duplicate leading monomial survives.
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let one = pr.constant(pr.field().from_int(1));
    let two = pr.constant(pr.field().from_int(2));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let g1 = pr.sub(pr.clone_poly(&x2), pr.clone_poly(&one)); // x² - 1
    let g2 = pr.sub(pr.clone_poly(&y2), pr.clone_poly(&one)); // y² - 1
    // x² + y² - 2  (redundant; LT = x²)
    let g3 = pr.sub(pr.add(x2, y2), two);

    // Canonical reduced GB from the two real generators.
    let reduced = compute_gb_with_order(
        &pr,
        vec![pr.clone_poly(&g1), pr.clone_poly(&g2)],
        &CancelToken::none(),
        FfOrder::DegRevLex,
    );

    let non_minimal = vec![g1, g2, g3];
    let out = interreduce_basis(&pr, non_minimal, &CancelToken::none());

    // Same leading-monomial set, same cardinality (minimal), and no
    // duplicate leading monomial.
    assert_eq!(lm_multiset(&pr, &out), lm_multiset(&pr, &reduced));
    assert_eq!(out.len(), reduced.len(), "result must be minimal");
    let lms = lm_multiset(&pr, &out);
    let mut uniq = lms.clone();
    uniq.dedup();
    assert_eq!(lms.len(), uniq.len(), "no duplicate leading monomial: {:?}", lms);
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
