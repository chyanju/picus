//! Spec-driven property tests for [`SparsePolynomial`].
//!
//! Expected values are derived from RING AXIOMS (commutativity, associativity,
//! distributivity, identities, inverses) and CROSS-VALIDATION against the
//! independently implemented [`DensePoly`] arm. A failure here indicates a
//! bug in the sparse implementation (the dense arm is the differential
//! oracle for the sparse engine, per `repr_oracle`).

use crate::ff::field::PrimeField;
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::ff::polynomial::{DensePoly, PolyRing};
use crate::ff::sparse_monomial::SparseMonomial;
use crate::ff::sparse_polynomial::SparsePolynomial;
use num_bigint::BigUint;
use std::sync::Arc;

fn ring_with(prime: u64, n_vars: usize, order: MonomialOrder) -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(prime));
    let names: Vec<String> = (0..n_vars).map(|i| format!("x{i}")).collect();
    PolyRing::new(f, names, order)
}

/// Compare two sparse polynomials term-for-term.
fn sparse_eq(a: &SparsePolynomial, b: &SparsePolynomial, ring: &PolyRing) -> bool {
    if a.num_terms() != b.num_terms() {
        return false;
    }
    for i in 0..a.num_terms() {
        let (ma, ca) = a.term_at(i).unwrap();
        let (mb, cb) = b.term_at(i).unwrap();
        if ma != mb {
            return false;
        }
        if !ring.field.eq(ca, cb) {
            return false;
        }
    }
    true
}

/// Build a sparse polynomial from `(exponents, coeff_u64)` triples.
fn sp(items: Vec<(Vec<u16>, i64)>, ring: &PolyRing) -> SparsePolynomial {
    let f = &ring.field;
    let terms: Vec<(SparseMonomial, crate::ff::field::FieldElem)> = items
        .into_iter()
        .map(|(e, c)| (<SparseMonomial as crate::ff::repr::MonomialRepr>::from_exponents(e), f.from_i64(c)))
        .collect();
    SparsePolynomial::from_terms(terms, ring)
}

fn sample_p(ring: &PolyRing) -> SparsePolynomial {
    // 2*x0^2*x1 + 3*x1*x2 + 5*x0 + 7
    sp(
        vec![
            (vec![2, 1, 0], 2),
            (vec![0, 1, 1], 3),
            (vec![1, 0, 0], 5),
            (vec![0, 0, 0], 7),
        ],
        ring,
    )
}

fn sample_q(ring: &PolyRing) -> SparsePolynomial {
    // x0*x2 + 4*x1 - 1
    sp(
        vec![
            (vec![1, 0, 1], 1),
            (vec![0, 1, 0], 4),
            (vec![0, 0, 0], -1),
        ],
        ring,
    )
}

fn sample_r(ring: &PolyRing) -> SparsePolynomial {
    // x0 + x1 + x2
    sp(
        vec![
            (vec![1, 0, 0], 1),
            (vec![0, 1, 0], 1),
            (vec![0, 0, 1], 1),
        ],
        ring,
    )
}

// ── (1) RING AXIOMS ─────────────────────────────────────────────────────

#[test]
fn prop_sparse_add_identity() {
    // a + 0 = a.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let z = SparsePolynomial::zero();
        assert!(sparse_eq(&a.add(&z, &r), &a, &r), "a+0 != a GF({prime})");
        assert!(sparse_eq(&z.add(&a, &r), &a, &r), "0+a != a GF({prime})");
    }
}

#[test]
fn prop_sparse_add_inverse() {
    // a + (-a) = 0.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let na = a.negate(&r);
        assert!(a.add(&na, &r).is_zero(), "a+(-a) != 0 GF({prime})");
    }
}

#[test]
fn prop_sparse_sub_self_zero() {
    // a - a = 0.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        assert!(a.sub(&a, &r).is_zero(), "a-a != 0 GF({prime})");
    }
}

#[test]
fn prop_sparse_negate_involution() {
    // -(-a) = a.
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let nn = a.negate(&r).negate(&r);
        assert!(sparse_eq(&nn, &a, &r), "-(-a) != a GF({prime})");
    }
}

#[test]
fn prop_sparse_add_commutative() {
    // a + b = b + a.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        assert!(sparse_eq(&a.add(&b, &r), &b.add(&a, &r), &r),
            "a+b != b+a GF({prime})");
    }
}

#[test]
fn prop_sparse_add_associative() {
    // (a+b)+c = a+(b+c).
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let lhs = a.add(&b, &r).add(&c, &r);
        let rhs = a.add(&b.add(&c, &r), &r);
        assert!(sparse_eq(&lhs, &rhs, &r), "(a+b)+c != a+(b+c) GF({prime})");
    }
}

#[test]
fn prop_sparse_mul_identity_and_zero() {
    // a*1 = a; a*0 = 0.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let one = SparsePolynomial::constant(r.field.one(), &r);
        let zero = SparsePolynomial::zero();
        assert!(sparse_eq(&a.mul(&one, &r), &a, &r), "a*1 != a GF({prime})");
        assert!(sparse_eq(&one.mul(&a, &r), &a, &r), "1*a != a GF({prime})");
        assert!(a.mul(&zero, &r).is_zero(), "a*0 != 0 GF({prime})");
        assert!(zero.mul(&a, &r).is_zero(), "0*a != 0 GF({prime})");
    }
}

#[test]
fn prop_sparse_mul_commutative() {
    // a*b = b*a.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        assert!(sparse_eq(&a.mul(&b, &r), &b.mul(&a, &r), &r),
            "a*b != b*a GF({prime})");
    }
}

#[test]
fn prop_sparse_mul_associative() {
    // (a*b)*c = a*(b*c).
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let lhs = a.mul(&b, &r).mul(&c, &r);
        let rhs = a.mul(&b.mul(&c, &r), &r);
        assert!(sparse_eq(&lhs, &rhs, &r), "(a*b)*c != a*(b*c) GF({prime})");
    }
}

#[test]
fn prop_sparse_distributivity() {
    // a*(b+c) = a*b + a*c.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let lhs = a.mul(&b.add(&c, &r), &r);
        let rhs = a.mul(&b, &r).add(&a.mul(&c, &r), &r);
        assert!(sparse_eq(&lhs, &rhs, &r),
            "a*(b+c) != a*b+a*c GF({prime})");
    }
}

#[test]
fn prop_sparse_deg_of_product() {
    // For nonzero a,b in an integral domain: deg(a*b) = deg(a)+deg(b).
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r); // deg 3
        let b = sample_q(&r); // deg 2
        let prod = a.mul(&b, &r);
        assert_eq!(
            prod.total_degree(),
            a.total_degree() + b.total_degree(),
            "deg(a*b) != deg(a)+deg(b) GF({prime})"
        );
    }
}

#[test]
fn prop_sparse_leading_term_of_product() {
    // LT(a*b) = LT(a)*LT(b) over a field (no zero divisors).
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let f = &r.field;
    let a = sample_p(&r);
    let b = sample_q(&r);
    let prod = a.mul(&b, &r);
    let lc_a = a.leading_coefficient().unwrap();
    let lc_b = b.leading_coefficient().unwrap();
    let lc_prod = prod.leading_coefficient().unwrap();
    assert!(f.eq(lc_prod, &f.mul(lc_a, lc_b)), "LC(a*b) != LC(a)*LC(b)");
    // Leading monomials: componentwise sum.
    let lm_a = a.leading_monomial().unwrap();
    let lm_b = b.leading_monomial().unwrap();
    let lm_p = prod.leading_monomial().unwrap();
    let exps_a = <SparseMonomial as crate::ff::repr::MonomialRepr>::to_dense(lm_a);
    let exps_b = <SparseMonomial as crate::ff::repr::MonomialRepr>::to_dense(lm_b);
    let exps_p = <SparseMonomial as crate::ff::repr::MonomialRepr>::to_dense(lm_p);
    let expected: Vec<u16> = exps_a.iter().zip(exps_b.iter()).map(|(x, y)| x + y).collect();
    assert_eq!(exps_p, expected, "LM(a*b) != LM(a)*LM(b)");
}

#[test]
fn prop_sparse_scale_one_identity_zero_collapse() {
    // scale(a, 1) = a; scale(a, 0) = 0.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        assert!(sparse_eq(&a.scale(&r.field.one(), &r), &a, &r),
            "scale(a,1) != a GF({prime})");
        assert!(a.scale(&r.field.zero(), &r).is_zero(),
            "scale(a,0) != 0 GF({prime})");
    }
}

#[test]
fn prop_sparse_scale_inverse_roundtrip() {
    // scale(scale(a, c), c^-1) = a for c != 0.
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let c = r.field.from_u64(2);
        let cinv = r.field.inv(&c).unwrap();
        let s = a.scale(&c, &r).scale(&cinv, &r);
        assert!(sparse_eq(&s, &a, &r),
            "scale(scale(a,c),c^-1) != a GF({prime})");
    }
}

// ── (3) IDEMPOTENCE ─────────────────────────────────────────────────────

#[test]
fn prop_sparse_make_monic_idempotent() {
    // monic(monic(p)) = monic(p) and LC(monic(p)) = 1.
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let m = p.make_monic(&r);
        let mm = m.make_monic(&r);
        assert!(sparse_eq(&m, &mm, &r),
            "monic idempotence GF({prime})");
        assert!(r.field.is_one(m.leading_coefficient().unwrap()),
            "monic LC != 1 GF({prime})");
    }
}

#[test]
fn prop_sparse_make_monic_of_zero_is_zero() {
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    assert!(SparsePolynomial::zero().make_monic(&r).is_zero());
}

// ── (4) INVARIANTS ──────────────────────────────────────────────────────

#[test]
fn prop_sparse_evaluate_homomorphism() {
    // E is a ring hom: E(a+b) = E(a)+E(b), E(a*b) = E(a)*E(b).
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let a = sample_p(&r);
        let b = sample_q(&r);
        let v = vec![f.from_u64(2), f.from_u64(3), f.from_u64(5)];
        let ea = a.evaluate(&v, &r);
        let eb = b.evaluate(&v, &r);
        let sum = a.add(&b, &r).evaluate(&v, &r);
        let prd = a.mul(&b, &r).evaluate(&v, &r);
        assert!(f.eq(&sum, &f.add(&ea, &eb)),
            "E(a+b) != E(a)+E(b) GF({prime})");
        assert!(f.eq(&prd, &f.mul(&ea, &eb)),
            "E(a*b) != E(a)*E(b) GF({prime})");
    }
}

#[test]
fn prop_sparse_evaluate_variable_is_value() {
    // E(x_i)(v) = v_i.
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let v = vec![f.from_u64(2), f.from_u64(5), f.from_u64(11)];
        for i in 0..3 {
            let xi = SparsePolynomial::variable(i, &r);
            assert!(f.eq(&xi.evaluate(&v, &r), &v[i]),
                "E(x{i}) != v[{i}] GF({prime})");
        }
    }
}

#[test]
fn prop_sparse_evaluate_constant() {
    // E(c)(v) = c for any constant c.
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let c = f.from_u64(13 % prime);
        let p = SparsePolynomial::constant(c.clone(), &r);
        let v = vec![f.from_u64(7), f.from_u64(11), f.from_u64(13)];
        assert!(f.eq(&p.evaluate(&v, &r), &c),
            "E(const) != const GF({prime})");
    }
}

#[test]
fn prop_sparse_fermat_eval_zero() {
    // For each prime p and each a in GF(p), the polynomial x^p - x evaluates
    // to 0 (Fermat's little theorem). Test univariate.
    for &prime in &[2u64, 3, 5, 7] {
        let r = ring_with(prime, 1, MonomialOrder::DegRevLex);
        let f = &r.field;
        let xp_minus_x = sp(
            vec![(vec![prime as u16], 1), (vec![1], -1)],
            &r,
        );
        for a in 0..prime {
            let v = vec![f.from_u64(a)];
            assert!(f.is_zero(&xp_minus_x.evaluate(&v, &r)),
                "Fermat fail at {a} in GF({prime})");
        }
    }
}

// ── (4) REDUCTION INVARIANTS ────────────────────────────────────────────

#[test]
fn prop_sparse_reduce_zero_is_zero() {
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let d = sample_p(&r);
    let dr: Vec<&SparsePolynomial> = vec![&d];
    let nf = SparsePolynomial::zero().reduce_by_refs(&dr, &r);
    assert!(nf.is_zero(), "0 reduced != 0");
}

#[test]
fn prop_sparse_reduce_self_yields_zero() {
    // p reduced by [p] yields 0.
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let nf = p.reduce_by_refs(&[&p], &r);
        assert!(nf.is_zero(), "p mod p != 0 GF({prime})");
    }
}

#[test]
fn prop_sparse_reduce_multiple_of_self_zero() {
    // (q*p) reduced by [p] = 0.
    for &prime in &[7u64, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let q = sample_q(&r);
        let qp = q.mul(&p, &r);
        let nf = qp.reduce_by_refs(&[&p], &r);
        assert!(nf.is_zero(), "(q*p) mod p != 0 GF({prime})");
    }
}

#[test]
fn prop_sparse_reduce_naive_matches_geobucket() {
    // The naive reducer is the differential oracle for the geobucket
    // production path (per `reduce_by_refs_naive` docstring): same
    // divisor order => identical normal form.
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let p = sp(
        vec![
            (vec![4, 2, 0], 1),
            (vec![3, 1, 0], 5),
            (vec![1, 2, 0], 7),
            (vec![0, 0, 1], 1),
            (vec![0, 0, 0], 11),
        ],
        &r,
    );
    let d1 = sp(vec![(vec![3, 0, 0], 1), (vec![0, 1, 0], -2)], &r);
    let d2 = sp(vec![(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)], &r);
    let d3 = sp(vec![(vec![0, 2, 0], 1), (vec![0, 0, 0], -1)], &r);
    let divs: Vec<&SparsePolynomial> = vec![&d1, &d2, &d3];
    let naive = p.reduce_by_refs_naive(&divs, &r);
    let geo = p.reduce_by_refs(&divs, &r);
    assert!(sparse_eq(&naive, &geo, &r),
        "naive reducer disagrees with geobucket");
}

// ── (7) EDGE CASES ──────────────────────────────────────────────────────

#[test]
fn prop_sparse_zero_poly_has_no_lc() {
    let r = ring_with(7, 3, MonomialOrder::DegRevLex);
    let z = SparsePolynomial::zero();
    assert!(z.is_zero());
    assert_eq!(z.num_terms(), 0);
    assert!(z.leading_coefficient().is_none());
    assert!(z.leading_monomial().is_none());
    assert_eq!(z.total_degree(), 0);
}

#[test]
fn prop_sparse_constant_zero_is_zero_poly() {
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = SparsePolynomial::constant(r.field.zero(), &r);
        assert!(p.is_zero(), "constant(0) != 0 GF({prime})");
    }
}

#[test]
fn prop_sparse_zero_var_ring() {
    // 0 variables: only constants are representable.
    let f = PrimeField::new(BigUint::from(7u32));
    let r = PolyRing::new(f, vec![], MonomialOrder::DegRevLex);
    let one = SparsePolynomial::constant(r.field.one(), &r);
    let z = SparsePolynomial::zero();
    assert_eq!(one.num_terms(), 1);
    assert!(one.is_constant());
    assert!(z.is_zero());
    // 1 + 1 over GF(7) = 2 with 1 term.
    let two = one.add(&one, &r);
    assert_eq!(two.num_terms(), 1);
    assert!(r.field.eq(two.leading_coefficient().unwrap(), &r.field.from_u64(2)));
}

#[test]
fn prop_sparse_one_var_ring() {
    // 1 variable, basic identity.
    let r = ring_with(101, 1, MonomialOrder::DegRevLex);
    let xp1 = sp(vec![(vec![1], 1), (vec![0], 1)], &r);
    let xm1 = sp(vec![(vec![1], 1), (vec![0], -1)], &r);
    let prod = xp1.mul(&xm1, &r);
    let expected = sp(vec![(vec![2], 1), (vec![0], -1)], &r);
    assert!(sparse_eq(&prod, &expected, &r), "(x+1)(x-1) != x^2-1");
}

// ── (8) DETERMINISM ─────────────────────────────────────────────────────

#[test]
fn prop_sparse_determinism() {
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let a = sample_p(&r);
    let b = sample_q(&r);
    assert!(sparse_eq(&a.add(&b, &r), &a.add(&b, &r), &r));
    assert!(sparse_eq(&a.mul(&b, &r), &a.mul(&b, &r), &r));
    assert!(sparse_eq(&a.make_monic(&r), &a.make_monic(&r), &r));
    assert_eq!(a.content_hash(), a.content_hash());
}

// ── (2) ROUND-TRIP: dense <-> sparse ────────────────────────────────────

#[test]
fn prop_sparse_dense_roundtrip() {
    // from_dense(to_dense(s)) == s and to_dense(from_dense(d)) == d, i.e.
    // the dense/sparse boundary is bijective for valid polynomials.
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let s = sample_p(&r);
    let d = s.to_dense(&r);
    let s2 = SparsePolynomial::from_dense(&d, &r);
    assert!(sparse_eq(&s, &s2, &r),
        "sparse -> dense -> sparse not identity");
    // Reverse: dense first.
    let f = &r.field;
    let dorig = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(2)),
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(5)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(7)),
        ],
        &r,
    );
    let s3 = SparsePolynomial::from_dense(&dorig, &r);
    let d2 = s3.to_dense(&r);
    assert_eq!(dorig.num_terms(), d2.num_terms());
    for i in 0..dorig.num_terms() {
        assert_eq!(dorig.term(i, &r).exponents(), d2.term(i, &r).exponents());
        assert!(r.field.eq(dorig.term(i, &r).coefficient(),
                           d2.term(i, &r).coefficient()));
    }
}

// ── (9) ENGINE EQUIVALENCE: sparse vs dense match term-by-term ──────────

/// Convert a sparse polynomial to a dense one and compare against the
/// dense computation, for each binary op. The sparse engine MUST agree
/// with the dense engine on all polynomial-ring operations.

#[test]
fn prop_sparse_dense_equivalence_add() {
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let sa = sample_p(&r);
    let sb = sample_q(&r);
    let da = sa.to_dense(&r);
    let db = sb.to_dense(&r);
    let s_sum = sa.add(&sb, &r);
    let d_sum = da.add(&db, &r);
    // Compare via dense materialisation of sparse result.
    let s_as_dense = s_sum.to_dense(&r);
    assert_eq!(d_sum.num_terms(), s_as_dense.num_terms(),
        "term count mismatch on add");
    for i in 0..d_sum.num_terms() {
        assert_eq!(d_sum.term(i, &r).exponents(),
                   s_as_dense.term(i, &r).exponents());
        assert!(r.field.eq(d_sum.term(i, &r).coefficient(),
                           s_as_dense.term(i, &r).coefficient()));
    }
}

#[test]
fn prop_sparse_dense_equivalence_mul() {
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let sa = sample_p(&r);
    let sb = sample_q(&r);
    let da = sa.to_dense(&r);
    let db = sb.to_dense(&r);
    let s_prod = sa.mul(&sb, &r);
    let d_prod = da.mul(&db, &r);
    let s_as_dense = s_prod.to_dense(&r);
    assert_eq!(d_prod.num_terms(), s_as_dense.num_terms(),
        "term count mismatch on mul");
    for i in 0..d_prod.num_terms() {
        assert_eq!(d_prod.term(i, &r).exponents(),
                   s_as_dense.term(i, &r).exponents());
        assert!(r.field.eq(d_prod.term(i, &r).coefficient(),
                           s_as_dense.term(i, &r).coefficient()));
    }
}

#[test]
fn prop_sparse_dense_equivalence_reduce() {
    // Sparse and dense reducers must agree on the normal form
    // (same divisor order => same NF).
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let p = sp(
        vec![
            (vec![4, 2, 0], 1),
            (vec![3, 1, 0], 5),
            (vec![1, 2, 0], 7),
            (vec![0, 0, 1], 1),
            (vec![0, 0, 0], 11),
        ],
        &r,
    );
    let d1 = sp(vec![(vec![3, 0, 0], 1), (vec![0, 1, 0], -2)], &r);
    let d2 = sp(vec![(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)], &r);
    let d3 = sp(vec![(vec![0, 2, 0], 1), (vec![0, 0, 0], -1)], &r);
    let divs: Vec<&SparsePolynomial> = vec![&d1, &d2, &d3];
    let s_nf = p.reduce_by_refs(&divs, &r);

    // Dense equivalent.
    let pd = p.to_dense(&r);
    let dd1 = d1.to_dense(&r);
    let dd2 = d2.to_dense(&r);
    let dd3 = d3.to_dense(&r);
    let ddivs: Vec<&DensePoly> = vec![&dd1, &dd2, &dd3];
    let d_nf = pd.reduce_by(&ddivs.into_iter().cloned().collect::<Vec<_>>(), &r);
    let s_nf_dense = s_nf.to_dense(&r);
    assert_eq!(d_nf.num_terms(), s_nf_dense.num_terms(),
        "sparse and dense reducer disagree on term count");
    for i in 0..d_nf.num_terms() {
        assert_eq!(d_nf.term(i, &r).exponents(),
                   s_nf_dense.term(i, &r).exponents());
        assert!(r.field.eq(d_nf.term(i, &r).coefficient(),
                           s_nf_dense.term(i, &r).coefficient()));
    }
}

// ── (1) Lex specifics ───────────────────────────────────────────────────

#[test]
fn prop_sparse_lex_leading_term() {
    // Under Lex, x0 > x1^5 because x0's exponent is checked first.
    let r = ring_with(101, 2, MonomialOrder::Lex);
    let p = sp(vec![(vec![1, 0], 1), (vec![0, 5], 1)], &r);
    let lm = p.leading_monomial().unwrap();
    let exps = <SparseMonomial as crate::ff::repr::MonomialRepr>::to_dense(lm);
    assert_eq!(exps, vec![1, 0], "Lex LT should be x0, not x1^5");
}

#[test]
fn prop_sparse_degrevlex_leading_term() {
    // Under DegRevLex, x1^5 > x0 because deg(x1^5)=5 > deg(x0)=1.
    let r = ring_with(101, 2, MonomialOrder::DegRevLex);
    let p = sp(vec![(vec![1, 0], 1), (vec![0, 5], 1)], &r);
    let lm = p.leading_monomial().unwrap();
    let exps = <SparseMonomial as crate::ff::repr::MonomialRepr>::to_dense(lm);
    assert_eq!(exps, vec![0, 5], "DegRevLex LT should be x1^5");
}
