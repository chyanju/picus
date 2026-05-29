use super::*;

#[test]
fn divmask_consistency() {
    let scheme = DivMaskScheme::build(4, 8);
    // a = x0^2 x1
    let a = Monomial::from_exponents(vec![2, 1, 0, 0]);
    // b = x0^4 x1^3 x2
    let b = Monomial::from_exponents(vec![4, 3, 1, 0]);
    assert!(a.divides(&b));
    let ma = scheme.compute(&a);
    let mb = scheme.compute(&b);
    assert!(ma.divides_consistent_with(mb));

    // c does not divide a (c has x2 but a doesn't)
    let c = Monomial::from_exponents(vec![1, 0, 1, 0]);
    let mc = scheme.compute(&c);
    assert!(!c.divides(&a));
    // DivMask is a NECESSARY condition, not sufficient: it may sometimes
    // return true even when divisibility fails; but if it returns false,
    // divisibility certainly fails. So we just check that whenever
    // monomial-divides is true, divmask is consistent.
    let _ = mc; // no false-negative requirement
}

#[test]
fn divmask_rejects_some() {
    // With a small max_deg threshold of 1, we have one bit per var.
    let scheme = DivMaskScheme::build(2, 1);
    let a = Monomial::from_exponents(vec![2, 0]);
    let b = Monomial::from_exponents(vec![0, 2]);
    // a does NOT divide b
    let ma = scheme.compute(&a);
    let mb = scheme.compute(&b);
    assert!(!ma.divides_consistent_with(mb));
}
