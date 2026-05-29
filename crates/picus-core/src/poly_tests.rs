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

// ── facade dispatch: PolyRingFacade methods ────────────────────────────

fn pr_dense(n_vars: usize) -> FfPolyRing {
    let f = PrimeField::new(BigUint::from(101u32));
    let names: Vec<String> = (0..n_vars).map(|i| format!("x{i}")).collect();
    FfPolyRing::new_with_repr(f, names, ReprKind::Dense)
}

#[allow(dead_code)]
fn pr_sparse(n_vars: usize) -> FfPolyRing {
    let f = PrimeField::new(BigUint::from(101u32));
    let names: Vec<String> = (0..n_vars).map(|i| format!("x{i}")).collect();
    FfPolyRing::new_with_repr(f, names, ReprKind::Sparse)
}

#[test]
fn prop_facade_var_names_round_trip() {
    let pr = pr_dense(3);
    assert_eq!(pr.var_names(), &["x0", "x1", "x2"]);
    assert_eq!(pr.n_vars(), 3);
    // var_index lookup.
    assert_eq!(pr.var_index("x0"), Some(0));
    assert_eq!(pr.var_index("x2"), Some(2));
    assert_eq!(pr.var_index("not_a_var"), None);
}

#[test]
fn prop_facade_zero_one_axioms() {
    // zero(), one() are the additive/multiplicative identities of the ring.
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let f = PrimeField::new(BigUint::from(101u32));
        let pr = FfPolyRing::new_with_repr(f, vec!["x".into(), "y".into()], repr);
        let z = pr.zero();
        let one = pr.one();
        let x = pr.var(0);
        assert!(pr.is_zero(&z));
        assert!(!pr.is_zero(&one));
        // x + 0 = x
        let s = pr.add(pr.clone_poly(&x), pr.clone_poly(&z));
        // Comparison via difference.
        assert!(pr.is_zero(&pr.sub(s, pr.clone_poly(&x))));
        // x * 1 == x (mul by one)
        let m = pr.mul(pr.clone_poly(&x), pr.clone_poly(&one));
        assert!(pr.is_zero(&pr.sub(m, pr.clone_poly(&x))));
        // x * 0 == 0
        let mz = pr.mul(pr.clone_poly(&x), pr.clone_poly(&z));
        assert!(pr.is_zero(&mz));
    }
}

#[test]
fn prop_facade_appearing_indeterminates_basic() {
    // p = x0 + x2  ⇒ appearing = {0, 2}.
    let pr = pr_dense(3);
    let p = pr.add(pr.var(0), pr.var(2));
    let app = pr.appearing_indeterminates(&p);
    assert!(!app.is_empty());
    assert_eq!(app.len(), 2);
    let vars: Vec<usize> = app.iter().collect();
    assert_eq!(vars, vec![0, 2]);
}

#[test]
fn prop_facade_appearing_indeterminates_constant_is_empty() {
    // A constant polynomial has no appearing indeterminates.
    let pr = pr_dense(3);
    let c = pr.constant(pr.field().from_u64(5));
    let app = pr.appearing_indeterminates(&c);
    assert!(app.is_empty());
    assert_eq!(app.len(), 0);
}

#[test]
fn prop_facade_scale_zero_and_one() {
    // scale by 0 ⇒ zero; scale by 1 ⇒ identity.
    let pr = pr_dense(2);
    let p = pr.add(pr.var(0), pr.var(1));
    let zero_scaled = pr.scale(pr.field().zero(), pr.clone_poly(&p));
    assert!(pr.is_zero(&zero_scaled));
    let one_scaled = pr.scale(pr.field().one(), pr.clone_poly(&p));
    assert!(pr.is_zero(&pr.sub(one_scaled, p)));
}

#[test]
fn prop_facade_terms_iter_count_matches_num_terms() {
    // The iterator yields exactly num_terms entries on both arms.
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let f = PrimeField::new(BigUint::from(101u32));
        let pr = FfPolyRing::new_with_repr(f, vec!["x".into(), "y".into(), "z".into()], repr);
        let p = pr.add(
            pr.add(pr.mul(pr.var(0), pr.var(1)), pr.var(2)),
            pr.constant(pr.field().from_u64(7)),
        );
        let n = p.num_terms();
        assert!(n > 0);
        let count = pr.ring.terms(&p).count();
        assert_eq!(count, n, "repr {repr:?}: iter count != num_terms");
    }
}

#[test]
fn prop_facade_create_term_and_exponent_at() {
    let pr = pr_dense(3);
    let m = pr.ring.create_monomial([2usize, 0, 1]);
    let c = pr.field().from_u64(7);
    let p = pr.ring.create_term(c.clone(), m.clone());
    // Single-term polynomial. iter should yield (7, x0^2 x2).
    let mut it = pr.ring.terms(&p);
    let (coeff, mono) = it.next().unwrap();
    assert!(pr.field().eq(coeff, &c));
    assert_eq!(pr.ring.exponent_at(&mono, 0), 2);
    assert_eq!(pr.ring.exponent_at(&mono, 1), 0);
    assert_eq!(pr.ring.exponent_at(&mono, 2), 1);
    assert!(it.next().is_none());
}

#[test]
fn prop_facade_indeterminate_is_var_of_degree_one() {
    let pr = pr_dense(4);
    let m = pr.ring.indeterminate(2);
    // exponent[2] = 1, rest 0.
    for i in 0..4 {
        let expected = if i == 2 { 1 } else { 0 };
        assert_eq!(pr.ring.exponent_at(&m, i), expected);
    }
}

#[test]
fn prop_facade_add_assign_sub_assign() {
    let pr = pr_dense(2);
    let mut acc = pr.var(0);
    pr.ring.add_assign(&mut acc, pr.var(1));
    // acc = x0 + x1
    let expected = pr.add(pr.var(0), pr.var(1));
    assert!(pr.is_zero(&pr.sub(pr.clone_poly(&acc), expected)));
    // Subtract back to x0.
    pr.ring.sub_assign(&mut acc, pr.var(1));
    let just_x0 = pr.var(0);
    assert!(pr.is_zero(&pr.sub(acc, just_x0)));
}

#[test]
fn prop_facade_zero_var_ring() {
    // 0 variables ⇒ only constants exist; zero() and one() distinct.
    let f = PrimeField::new(BigUint::from(7u32));
    let pr = FfPolyRing::new(f, vec![]);
    assert_eq!(pr.n_vars(), 0);
    let z = pr.zero();
    let one = pr.one();
    assert!(pr.is_zero(&z));
    assert!(!pr.is_zero(&one));
}

// ── facade dispatch: dense and sparse arms agree on appearing_indets ───

#[test]
fn prop_facade_appearing_indeterminates_arms_agree() {
    // p = (x0 + x1)*(x2 + 1)  has variables {0,1,2}.
    let build = |repr| -> Vec<usize> {
        let f = PrimeField::new(BigUint::from(101u32));
        let pr = FfPolyRing::new_with_repr(f, vec!["x0".into(), "x1".into(), "x2".into()], repr);
        let p = pr.mul(
            pr.add(pr.var(0), pr.var(1)),
            pr.add(pr.var(2), pr.one()),
        );
        let app = pr.appearing_indeterminates(&p);
        app.iter().collect()
    };
    assert_eq!(build(ReprKind::Dense), vec![0, 1, 2]);
    assert_eq!(build(ReprKind::Sparse), vec![0, 1, 2]);
}

// ── AppearingVars surface ──────────────────────────────────────────────

#[test]
fn prop_appearing_vars_index_and_get_consistent() {
    let pr = pr_dense(3);
    // p has x0 (max exp 1) and x2 (max exp 1).
    let p = pr.add(pr.var(0), pr.var(2));
    let app = pr.appearing_indeterminates(&p);
    assert_eq!(app.len(), 2);
    // get(i) returns (var, max_degree as usize).
    let (v0, d0) = app.get(0);
    let (v1, d1) = app.get(1);
    assert_eq!(v0, 0);
    assert_eq!(v1, 2);
    assert_eq!(d0, 1);
    assert_eq!(d1, 1);
    // Index<usize> returns (var, u16).
    assert_eq!(app[0], (0, 1));
    assert_eq!(app[1], (2, 1));
}
