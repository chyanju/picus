use super::*;
use num_bigint::BigUint;

#[test]
fn test_poly_basic() {
    let field = PrimeField::new(BigUint::from(17u32));
    let pr = FfPolyRing::new(field, vec!["x".into(), "y".into()]);

    let x = pr.var(0);
    let y = pr.var(1);
    let sum = pr.add(x, y);
    assert!(!pr.is_zero(&sum));

    let neg_sum = pr.neg(pr.clone_poly(&sum));
    let zero = pr.add(sum, neg_sum);
    assert!(pr.is_zero(&zero));
}

/// The dense and sparse arms of the IR ring (`FfPolyRing`) must agree
/// term-for-term (the heavy randomised differential check lives in
/// `ff::repr_oracle`; this is a facade-dispatch smoke test).
#[test]
fn irpoly_dense_sparse_arms_agree() {
    let field = PrimeField::new(BigUint::from(101u32));
    let names: Vec<String> = (0..5).map(|i| format!("x{}", i)).collect();

    let build = |repr| -> Vec<(BigUint, Vec<(usize, u16)>)> {
        let pr = FfPolyRing::new_with_repr(field.clone(), names.clone(), repr);
        // p = (x0 + x1) * (x2 - 1) + x3
        let a = pr.add(pr.var(0), pr.var(1));
        let b = pr.sub(pr.var(2), pr.one());
        let p = pr.add(pr.mul(a, b), pr.var(3));
        assert!(!pr.is_zero(&p));
        // p - p == 0
        let z = pr.sub(pr.clone_poly(&p), pr.clone_poly(&p));
        assert!(z.is_zero());
        assert_eq!(z.num_terms(), 0);
        assert!(pr.zero().is_zero());
        p.collect_terms_idx(pr.ctx())
    };

    assert_eq!(build(ReprKind::Dense), build(ReprKind::Sparse));
}
