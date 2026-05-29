use super::*;
use num_bigint::BigUint;

fn small_ring() -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(101u32));
    PolyRing::new(
        f,
        vec!["x".into(), "y".into(), "z".into()],
        MonomialOrder::DegRevLex,
    )
}

#[test]
fn reduce_by_refs_lex_ring_non_monotone_degree_no_panic() {
    // Under Lex order a polynomial's terms descend by the order but NOT by
    // total degree (`x` > `y^2` in Lex, yet lower degree). The dense reducer
    // finalises its normal form via `from_raw_sorted`, which must not assume
    // degree-monotonicity. Reduce `x + y^2` by `x*y` (which divides neither
    // term) so both pass through and the result is rebuilt with ascending
    // total degrees [1, 2].
    let f = PrimeField::new(BigUint::from(101u32));
    let r = PolyRing::new(f, vec!["x".into(), "y".into()], MonomialOrder::Lex);
    let fld = &r.field;
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0]), fld.from_u64(1)),
            (Monomial::from_exponents(vec![0, 2]), fld.from_u64(1)),
        ],
        &r,
    );
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 1]), fld.from_u64(1))],
        &r,
    );
    // Must not panic; both terms are irreducible by `x*y`.
    let nf = p.reduce_by_refs(&[&d], &r);
    assert_eq!(nf.num_terms(), 2);
    assert_eq!(nf.leading_term(&r).unwrap().exponents(), &[1, 0]); // x is Lex-leading
}

#[test]
fn from_terms_sorts_and_dedupes() {
    let r = small_ring();
    let f = &r.field;
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(5)),
            (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(3)),
            (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(4)), // should sum
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(2)),
        ],
        &r,
    );
    // After dedup: [(2,1,0)*7, (1,0,0)*2, (0,0,0)*5] (descending DegRevLex)
    assert_eq!(p.num_terms(), 3);
    let lt = p.leading_term(&r).unwrap();
    assert_eq!(lt.exponents(), &[2, 1, 0]);
    assert_eq!(*lt.coefficient(), f.from_u64(7));
}

#[test]
fn add_sub_cancellation() {
    let r = small_ring();
    let f = &r.field;
    let a = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(3)),
            (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(5)),
        ],
        &r,
    );
    let b = a.clone();
    let zero = a.sub(&b, &r);
    assert!(zero.is_zero());
    let two_a = a.add(&a, &r);
    assert_eq!(two_a.num_terms(), 2);
    assert_eq!(
        *two_a.leading_term(&r).unwrap().coefficient(),
        f.from_u64(6)
    );
}

#[test]
fn mul_works() {
    let r = small_ring();
    let f = &r.field;
    // (x + 1)(x - 1) = x^2 - 1
    let a = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(1)),
        ],
        &r,
    );
    let b = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    let prod = a.mul(&b, &r);
    // x^2 - 1
    assert_eq!(prod.num_terms(), 2);
    let terms: Vec<_> = prod.terms(&r).collect();
    assert_eq!(terms[0].exponents(), &[2, 0, 0]);
    assert_eq!(*terms[0].coefficient(), f.from_u64(1));
    assert_eq!(terms[1].exponents(), &[0, 0, 0]);
    assert_eq!(*terms[1].coefficient(), f.from_i64(-1));
}

#[test]
fn reduce_by_simple() {
    let r = small_ring();
    let f = &r.field;
    // Divide x^2*y by (x*y - 1) over GF(101) DegRevLex.
    // Quotient: x; remainder: x.
    let f1 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    let g = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(1))],
        &r,
    );
    let nf = g.reduce_by(&[f1.clone()], &r);
    // x^2*y mod (x*y - 1): subtract x * (x*y - 1) = x^2*y - x => remainder x
    assert_eq!(nf.num_terms(), 1);
    let lt = nf.leading_term(&r).unwrap();
    assert_eq!(lt.exponents(), &[1, 0, 0]);
    assert_eq!(*lt.coefficient(), f.from_u64(1));
}

#[test]
fn reduce_by_refs_geobucket_matches_naive() {
    // Build a non-trivial reduction: a polynomial with multiple terms
    // reducible by several divisors, requiring many reduction steps.
    let r = small_ring();
    let f = &r.field;
    // Divisors: x^3 - 2*y, x*y - z, y^2 - 1
    let d1 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![3, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 1, 0]), f.from_i64(-2)),
        ],
        &r,
    );
    let d2 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 1]), f.from_i64(-1)),
        ],
        &r,
    );
    let d3 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![0, 2, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    // Subject: x^4*y^2 + 5*x^3*y + 7*x*y^2 + z + 11
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![4, 2, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![3, 1, 0]), f.from_u64(5)),
            (Monomial::from_exponents(vec![1, 2, 0]), f.from_u64(7)),
            (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(11)),
        ],
        &r,
    );
    let divs: Vec<&DensePoly> = vec![&d1, &d2, &d3];
    let geo = p.reduce_by_refs_geobucket(&divs, &r, None, None, None);
    let naive = p.reduce_by_refs_naive(&divs, &r);
    let dispatched = p.reduce_by_refs(&divs, &r);
    assert_eq!(geo.num_terms(), naive.num_terms());
    assert_eq!(dispatched.num_terms(), naive.num_terms());
    for (a, b) in geo.terms(&r).zip(naive.terms(&r)) {
        assert_eq!(a.exponents(), b.exponents());
        assert_eq!(a.coefficient(), b.coefficient());
    }
    for (a, b) in dispatched.terms(&r).zip(naive.terms(&r)) {
        assert_eq!(a.exponents(), b.exponents());
        assert_eq!(a.coefficient(), b.coefficient());
    }
}

fn assert_indexed_matches_geobucket(n: usize) {
    // Unique-match divisor set d_i = x_i^2 - (i+1): leading term x_i^2 in its
    // own variable, so any monomial is divisible by at most one — the normal
    // form is independent of scan order, so the per-call reducer's bucket
    // HashMap order and the ReducerIndex's order cannot diverge.
    let f = PrimeField::new(BigUint::from(101u32));
    let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let r = PolyRing::new(f, names, MonomialOrder::DegRevLex);
    let fp = &r.field;
    let divisors: Vec<DensePoly> = (0..n)
        .map(|i| {
            let mut sq = vec![0u16; n];
            sq[i] = 2;
            DensePoly::from_terms(
                vec![
                    (Monomial::from_exponents(sq), fp.from_u64(1)),
                    (Monomial::from_exponents(vec![0u16; n]), fp.from_u64((i as u64 + 1) % 101)),
                ],
                &r,
            )
        })
        .collect();
    let div_refs: Vec<&DensePoly> = divisors.iter().collect();
    // p = Σ_i x_i^2 + x_7 (x_7, degree 1, is irreducible by any x_j^2).
    let mut terms: Vec<(Monomial, FieldElem)> = (0..n)
        .map(|i| {
            let mut sq = vec![0u16; n];
            sq[i] = 2;
            (Monomial::from_exponents(sq), fp.from_u64(1))
        })
        .collect();
    let mut x7 = vec![0u16; n];
    x7[7] = 1;
    terms.push((Monomial::from_exponents(x7), fp.from_u64(1)));
    let p = DensePoly::from_terms(terms, &r);

    let original = p.reduce_by_refs_geobucket(&div_refs, &r, None, None, None);
    let index = super::ReducerIndex::build(&div_refs, &r, None);
    assert_eq!(index.len(), n);
    let mut uc = vec![0u64; n];
    let indexed = p.reduce_by_refs_geobucket_indexed(&index, &div_refs, &r, None, Some(&mut uc));

    assert_eq!(indexed.num_terms(), original.num_terms(), "indexed vs geobucket term count (n={n})");
    for (a, b) in indexed.terms(&r).zip(original.terms(&r)) {
        assert_eq!(a.exponents(), b.exponents(), "indexed exps diverge (n={n})");
        assert_eq!(a.coefficient(), b.coefficient(), "indexed coeffs diverge (n={n})");
    }
    let used = uc.iter().filter(|&&c| c > 0).count();
    assert_eq!(used, n, "each x_i^2 reduced by its unique divisor once (n={n})");
}

#[test]
fn reduce_indexed_matches_geobucket_order_path() {
    // 100 divisors: >= SORT_THRESHOLD (64), < BUCKET_THRESHOLD (256) → the
    // ReducerIndex uses the degree-`order` path.
    assert!(100 >= super::ReducerIndex::SORT_THRESHOLD);
    assert!(100 < super::ReducerIndex::BUCKET_THRESHOLD);
    assert_indexed_matches_geobucket(100);
}

#[test]
fn reduce_indexed_matches_geobucket_bucket_path() {
    // 300 divisors: >= BUCKET_THRESHOLD → the ReducerIndex uses DivMask buckets.
    assert!(300 >= super::ReducerIndex::BUCKET_THRESHOLD);
    assert_indexed_matches_geobucket(300);
}

#[test]
fn reduce_by_refs_geobucket_to_zero() {
    // DensePoly that fully reduces to zero — exercises the cancellation
    // path in pop_leading_term across many steps.
    let r = small_ring();
    let f = &r.field;
    let d = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 1, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    // p = (x - y) * (x^2 + x*y + y^2) = x^3 - y^3
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![3, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 3, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    // p reduced by (x - y): leading reductions cancel until 0.
    let nf = p.reduce_by_refs_geobucket(&[&d], &r, None, None, None);
    let nf_naive = p.reduce_by_refs_naive(&[&d], &r);
    assert!(nf.is_zero(), "geobucket reduction should yield zero");
    assert!(nf_naive.is_zero(), "naive reduction should also yield zero");
}

#[test]
fn evaluate_and_substitute() {
    let r = small_ring();
    let f = &r.field;
    // p = x*y + 2*z + 3
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(2)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(3)),
        ],
        &r,
    );
    // p(2,3,4) = 6 + 8 + 3 = 17
    let v = vec![f.from_u64(2), f.from_u64(3), f.from_u64(4)];
    assert_eq!(p.evaluate(&v, &r), f.from_u64(17));
    // substitute z=4: p' = x*y + 11
    let q = p.substitute_var(2, &f.from_u64(4), &r);
    assert_eq!(q.num_terms(), 2);
}

#[test]
fn make_monic_works() {
    let r = small_ring();
    let f = &r.field;
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(7)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(14)),
        ],
        &r,
    );
    let m = p.make_monic(&r);
    assert!(f.is_one(m.leading_coefficient().unwrap()));
    // 14/7 = 2
    let const_term = m.terms(&r).last().unwrap();
    assert_eq!(*const_term.coefficient(), f.from_u64(2));
}

// ─────────────────────────────────────────────────────────────────────────
// SPEC-DRIVEN PROPERTY TESTS
//
// Expected values come from MATHEMATICAL IDENTITIES, not from reading the
// source. Each test enforces a ring-axiom / monomial-order property that
// MUST hold by definition; a failure is a bug in the implementation.
// ─────────────────────────────────────────────────────────────────────────

/// Polynomial equality under the ring order: same number of terms, and
/// for each index i, same exponent vector and same coefficient.
fn poly_eq(a: &DensePoly, b: &DensePoly, ring: &PolyRing) -> bool {
    if a.num_terms() != b.num_terms() {
        return false;
    }
    for i in 0..a.num_terms() {
        let ta = a.term(i, ring);
        let tb = b.term(i, ring);
        if ta.exponents() != tb.exponents() {
            return false;
        }
        if !ring.field.eq(ta.coefficient(), tb.coefficient()) {
            return false;
        }
    }
    true
}

fn ring_with(prime: u64, n_vars: usize, order: MonomialOrder) -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(prime));
    let names: Vec<String> = (0..n_vars).map(|i| format!("x{i}")).collect();
    PolyRing::new(f, names, order)
}

/// A standard sample polynomial in 3 vars used across property tests:
/// 2*x0^2*x1 + 3*x1*x2 + 5*x0 + 7
fn sample_p(ring: &PolyRing) -> DensePoly {
    let f = &ring.field;
    DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(2)),
            (Monomial::from_exponents(vec![0, 1, 1]), f.from_u64(3)),
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(5)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(7)),
        ],
        ring,
    )
}

/// A second sample in 3 vars: x0*x2 + 4*x1 - 1
fn sample_q(ring: &PolyRing) -> DensePoly {
    let f = &ring.field;
    DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 1]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(4)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
        ],
        ring,
    )
}

/// A third sample in 3 vars: x0 + x1 + x2
fn sample_r(ring: &PolyRing) -> DensePoly {
    let f = &ring.field;
    DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(1)),
        ],
        ring,
    )
}

// ── (1) ALGEBRAIC IDENTITIES — ring axioms ──────────────────────────────

#[test]
fn prop_add_identity_a_plus_zero_eq_a() {
    // Ring axiom: 0 is the additive identity. a + 0 = a.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let z = DensePoly::zero();
        let lhs = a.add(&z, &r);
        let rhs = z.add(&a, &r);
        assert!(poly_eq(&lhs, &a, &r), "a + 0 != a in GF({prime})");
        assert!(poly_eq(&rhs, &a, &r), "0 + a != a in GF({prime})");
    }
}

#[test]
fn prop_add_inverse_a_plus_neg_a_eq_zero() {
    // Ring axiom: every a has an additive inverse. a + (-a) = 0.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let na = a.negate(&r);
        let s = a.add(&na, &r);
        assert!(s.is_zero(), "a + (-a) != 0 in GF({prime})");
    }
}

#[test]
fn prop_sub_self_eq_zero() {
    // a - a = 0 for every polynomial.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let z = p.sub(&p, &r);
        assert!(z.is_zero(), "a - a != 0 in GF({prime})");
    }
}

#[test]
fn prop_negate_involution() {
    // -(-a) = a (additive inverse is its own inverse).
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let nn = a.negate(&r).negate(&r);
        assert!(poly_eq(&nn, &a, &r), "-(-a) != a in GF({prime})");
    }
}

#[test]
fn prop_add_commutative() {
    // a + b = b + a.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let ab = a.add(&b, &r);
        let ba = b.add(&a, &r);
        assert!(poly_eq(&ab, &ba, &r), "a + b != b + a in GF({prime})");
    }
}

#[test]
fn prop_add_associative() {
    // (a + b) + c = a + (b + c).
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let lhs = a.add(&b, &r).add(&c, &r);
        let rhs = a.add(&b.add(&c, &r), &r);
        assert!(poly_eq(&lhs, &rhs, &r), "(a+b)+c != a+(b+c) in GF({prime})");
    }
}

#[test]
fn prop_mul_identity_a_times_one_eq_a() {
    // a * 1 = a (1 is the multiplicative identity).
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let one = DensePoly::constant(r.field.one(), &r);
        let l = a.mul(&one, &r);
        let r2 = one.mul(&a, &r);
        assert!(poly_eq(&l, &a, &r), "a * 1 != a in GF({prime})");
        assert!(poly_eq(&r2, &a, &r), "1 * a != a in GF({prime})");
    }
}

#[test]
fn prop_mul_absorbing_zero() {
    // a * 0 = 0 = 0 * a.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let z = DensePoly::zero();
        assert!(a.mul(&z, &r).is_zero(), "a * 0 != 0 in GF({prime})");
        assert!(z.mul(&a, &r).is_zero(), "0 * a != 0 in GF({prime})");
    }
}

#[test]
fn prop_mul_commutative() {
    // a * b = b * a in a commutative ring.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let ab = a.mul(&b, &r);
        let ba = b.mul(&a, &r);
        assert!(poly_eq(&ab, &ba, &r), "a*b != b*a in GF({prime})");
    }
}

#[test]
fn prop_mul_associative() {
    // (a*b)*c = a*(b*c).
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let lhs = a.mul(&b, &r).mul(&c, &r);
        let rhs = a.mul(&b.mul(&c, &r), &r);
        assert!(poly_eq(&lhs, &rhs, &r), "(a*b)*c != a*(b*c) in GF({prime})");
    }
}

#[test]
fn prop_distributivity_left() {
    // a*(b+c) = a*b + a*c (ring axiom).
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let lhs = a.mul(&b.add(&c, &r), &r);
        let rhs = a.mul(&b, &r).add(&a.mul(&c, &r), &r);
        assert!(poly_eq(&lhs, &rhs, &r), "a*(b+c) != a*b + a*c in GF({prime})");
    }
}

#[test]
fn prop_distributivity_right() {
    // (b+c)*a = b*a + c*a.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let lhs = b.add(&c, &r).mul(&a, &r);
        let rhs = b.mul(&a, &r).add(&c.mul(&a, &r), &r);
        assert!(poly_eq(&lhs, &rhs, &r), "(b+c)*a != b*a + c*a in GF({prime})");
    }
}

#[test]
fn prop_deg_of_product_under_degrevlex() {
    // For nonzero a,b: deg(a*b) = deg(a) + deg(b).
    // True in any commutative ring without zero divisors (a prime field is
    // a field, so an integral domain). DegRevLex's `total_degree` is
    // monotone in the leading position so this is also the polynomial's
    // total degree.
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r); // deg 3 (x0^2 * x1)
        let b = sample_q(&r); // deg 2 (x0 * x2)
        let prod = a.mul(&b, &r);
        assert_eq!(
            prod.total_degree(),
            a.total_degree() + b.total_degree(),
            "deg(a*b) != deg(a)+deg(b) in GF({prime})"
        );
    }
}

#[test]
fn prop_leading_monomial_of_product_under_degrevlex() {
    // LT(a*b) = LT(a) * LT(b) for nonzero a,b over a field (integral
    // domain). The product's leading monomial is the componentwise sum
    // of the operands' leading monomials.
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let a = sample_p(&r);
    let b = sample_q(&r);
    let lm_a = a.leading_monomial(&r).unwrap();
    let lm_b = b.leading_monomial(&r).unwrap();
    let prod = a.mul(&b, &r);
    let lm_prod = prod.leading_monomial(&r).unwrap();
    let expected: Vec<u16> = lm_a
        .exponents()
        .iter()
        .zip(lm_b.exponents().iter())
        .map(|(x, y)| x + y)
        .collect();
    assert_eq!(lm_prod.exponents(), expected.as_slice(),
        "LM(a*b) != LM(a)*LM(b)");
    let lc_a = a.leading_coefficient().unwrap();
    let lc_b = b.leading_coefficient().unwrap();
    let lc_prod = prod.leading_coefficient().unwrap();
    assert!(
        r.field.eq(lc_prod, &r.field.mul(lc_a, lc_b)),
        "LC(a*b) != LC(a)*LC(b)"
    );
}

#[test]
fn prop_scale_one_is_identity() {
    // c=1: scaling is identity.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let s = a.scale(&r.field.one(), &r);
        assert!(poly_eq(&s, &a, &r), "scale(a,1) != a in GF({prime})");
    }
}

#[test]
fn prop_scale_zero_is_zero() {
    // c=0: scaling produces the zero polynomial.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let s = a.scale(&r.field.zero(), &r);
        assert!(s.is_zero(), "scale(a,0) != 0 in GF({prime})");
    }
}

#[test]
fn prop_scale_inverse_roundtrip() {
    // For c ≠ 0: scale(scale(a, c), c^{-1}) = a.
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let c = r.field.from_u64(2);
        let cinv = r.field.inv(&c).unwrap();
        let s = a.scale(&c, &r).scale(&cinv, &r);
        assert!(poly_eq(&s, &a, &r),
            "scale(scale(a,c), c^-1) != a in GF({prime})");
    }
}

// ── (3) IDEMPOTENCE ─────────────────────────────────────────────────────

#[test]
fn prop_make_monic_idempotent() {
    // monic(monic(p)) = monic(p).
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let m = p.make_monic(&r);
        let mm = m.make_monic(&r);
        assert!(poly_eq(&m, &mm, &r), "monic idempotence in GF({prime})");
    }
}

#[test]
fn prop_make_monic_leading_coeff_is_one() {
    // The leading coefficient of monic(p) must be 1 for nonzero p (def).
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let m = p.make_monic(&r);
        assert!(r.field.is_one(m.leading_coefficient().unwrap()),
            "monic LC != 1 in GF({prime})");
    }
}

#[test]
fn prop_negate_negate_idempotent_arm() {
    // After two negations the polynomial is the original (involution).
    // Distinct from `prop_negate_involution` above to exercise on
    // distinct sample. Covers GF(2) (where -a == a).
    let r = ring_with(2, 3, MonomialOrder::DegRevLex);
    let p = sample_q(&r);
    let n = p.negate(&r);
    // In GF(2), -1 = 1 so negation is the identity.
    assert!(poly_eq(&n, &p, &r), "in GF(2), -a should equal a");
}

// ── (4) INVARIANTS POST-OPERATION ───────────────────────────────────────

#[test]
fn prop_evaluate_additive_homomorphism() {
    // E(a + b)(v) = E(a)(v) + E(b)(v): evaluation is a ring hom into GF(p).
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let a = sample_p(&r);
        let b = sample_q(&r);
        let v = vec![f.from_u64(2), f.from_u64(3), f.from_u64(5)];
        let sum_then_eval = a.add(&b, &r).evaluate(&v, &r);
        let eval_then_sum = f.add(&a.evaluate(&v, &r), &b.evaluate(&v, &r));
        assert!(f.eq(&sum_then_eval, &eval_then_sum),
            "E(a+b) != E(a)+E(b) in GF({prime})");
    }
}

#[test]
fn prop_evaluate_multiplicative_homomorphism() {
    // E(a * b)(v) = E(a)(v) * E(b)(v).
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let a = sample_p(&r);
        let b = sample_q(&r);
        let v = vec![f.from_u64(2), f.from_u64(3), f.from_u64(5)];
        let prod_then_eval = a.mul(&b, &r).evaluate(&v, &r);
        let eval_then_prod = f.mul(&a.evaluate(&v, &r), &b.evaluate(&v, &r));
        assert!(f.eq(&prod_then_eval, &eval_then_prod),
            "E(a*b) != E(a)*E(b) in GF({prime})");
    }
}

#[test]
fn prop_evaluate_constant_is_constant() {
    // E(c)(v) = c for any constant polynomial c and any values v.
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let c = f.from_u64(42 % prime);
        let p = DensePoly::constant(c.clone(), &r);
        let v = vec![f.from_u64(11), f.from_u64(13), f.from_u64(17)];
        let e = p.evaluate(&v, &r);
        assert!(f.eq(&e, &c), "E(const)(v) != const in GF({prime})");
    }
}

#[test]
fn prop_evaluate_variable_x_at_v_is_v() {
    // E(x_i)(v) = v_i: variable polynomial evaluates to its value.
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let v = vec![f.from_u64(2), f.from_u64(5), f.from_u64(11)];
        for i in 0..3 {
            let xi = DensePoly::variable(i, &r);
            let ev = xi.evaluate(&v, &r);
            assert!(f.eq(&ev, &v[i]),
                "E(x{i})(v) != v[{i}] in GF({prime})");
        }
    }
}

#[test]
fn prop_fermat_little_theorem_evaluation() {
    // Fermat: a^p = a in GF(p). So the polynomial x^p - x evaluates to 0
    // at every a in GF(p). Test by evaluating at every element.
    for &prime in &[2u64, 3, 5, 7] {
        let r = ring_with(prime, 1, MonomialOrder::DegRevLex);
        let f = &r.field;
        // x^p - x
        let xp = DensePoly::from_terms(
            vec![
                (Monomial::from_exponents(vec![prime as u16]), f.from_u64(1)),
                (Monomial::from_exponents(vec![1]), f.from_i64(-1)),
            ],
            &r,
        );
        for a in 0..prime {
            let v = vec![f.from_u64(a)];
            let e = xp.evaluate(&v, &r);
            assert!(f.is_zero(&e),
                "Fermat: x^{prime} - x at {a} != 0 in GF({prime})");
        }
    }
}

#[test]
fn prop_substitute_var_then_evaluate_remaining() {
    // p(x0,x1,x2) at (a0,a1,a2)
    //   == substitute_var(p, 0, a0)(0,x1,x2) at (0,a1,a2)
    // because after substitution the substituted variable no longer
    // matters (any value at its slot yields the same result).
    for &prime in &[7u64, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let p = sample_p(&r);
        let a0 = f.from_u64(3);
        let a1 = f.from_u64(4);
        let a2 = f.from_u64(5);
        let direct = p.evaluate(&[a0.clone(), a1.clone(), a2.clone()], &r);
        let sub = p.substitute_var(0, &a0, &r);
        // After substitution at var 0, any value at slot 0 must yield same:
        let through = sub.evaluate(&[f.zero(), a1.clone(), a2.clone()], &r);
        assert!(f.eq(&direct, &through),
            "substitute_var ; evaluate != direct evaluate in GF({prime})");
        // Sanity: a different value at the substituted slot is also equal.
        let through2 = sub.evaluate(&[f.from_u64(99), a1, a2], &r);
        assert!(f.eq(&through, &through2),
            "substituted variable still influences value in GF({prime})");
    }
}

// ── (7) EDGE PRIMES & SHAPES ────────────────────────────────────────────

#[test]
fn prop_zero_var_ring_constants_only() {
    // 0 variables: only constants. constant(c) has 1 term if c≠0 else 0.
    let f = PrimeField::new(BigUint::from(7u32));
    let r = PolyRing::new(f, vec![], MonomialOrder::DegRevLex);
    let z = DensePoly::constant(r.field.zero(), &r);
    assert!(z.is_zero(), "constant(0) should be zero");
    let one = DensePoly::constant(r.field.one(), &r);
    assert_eq!(one.num_terms(), 1, "constant(1) should have one term");
    assert_eq!(one.total_degree(), 0, "constant has degree 0");
    assert!(one.is_constant(), "constant is_constant");
    // 1 * 1 = 1.
    let sq = one.mul(&one, &r);
    assert!(poly_eq(&sq, &one, &r), "1*1 != 1 in 0-var ring");
}

#[test]
fn prop_one_var_ring_basic_identities() {
    // Univariate ring: degree of product = sum of degrees; (x+1)(x-1) = x^2 - 1.
    let r = ring_with(101, 1, MonomialOrder::DegRevLex);
    let f = &r.field;
    let xp1 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0]), f.from_u64(1)),
        ],
        &r,
    );
    let xm1 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0]), f.from_i64(-1)),
        ],
        &r,
    );
    let prod = xp1.mul(&xm1, &r);
    // Expected: x^2 - 1
    let expected = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0]), f.from_i64(-1)),
        ],
        &r,
    );
    assert!(poly_eq(&prod, &expected, &r), "(x+1)(x-1) != x^2 - 1");
}

#[test]
fn prop_zero_poly_has_no_terms_no_lc() {
    // Definitional: zero polynomial has no leading term, num_terms == 0,
    // is_zero == true, total_degree == 0 by convention.
    let r = ring_with(7, 3, MonomialOrder::DegRevLex);
    let z = DensePoly::zero();
    assert!(z.is_zero());
    assert_eq!(z.num_terms(), 0);
    assert!(z.leading_coefficient().is_none());
    assert!(z.leading_monomial(&r).is_none());
    assert!(z.leading_term(&r).is_none());
    assert_eq!(z.total_degree(), 0);
}

#[test]
fn prop_constant_zero_yields_zero_poly() {
    // Edge: constant(0) must collapse to the zero polynomial across primes.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = DensePoly::constant(r.field.zero(), &r);
        assert!(p.is_zero(), "constant(0) != zero poly in GF({prime})");
    }
}

#[test]
fn prop_make_monic_of_zero_is_zero() {
    // monic(0) = 0 by convention (no leading coefficient to divide by).
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let m = DensePoly::zero().make_monic(&r);
    assert!(m.is_zero(), "monic(0) != 0");
}

// ── (8) DETERMINISM ─────────────────────────────────────────────────────

#[test]
fn prop_determinism_arithmetic() {
    // Same inputs → same outputs across two invocations (no hidden state).
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let a = sample_p(&r);
    let b = sample_q(&r);
    let s1 = a.add(&b, &r);
    let s2 = a.add(&b, &r);
    assert!(poly_eq(&s1, &s2, &r), "add not deterministic");
    let p1 = a.mul(&b, &r);
    let p2 = a.mul(&b, &r);
    assert!(poly_eq(&p1, &p2, &r), "mul not deterministic");
    let m1 = a.make_monic(&r);
    let m2 = a.make_monic(&r);
    assert!(poly_eq(&m1, &m2, &r), "make_monic not deterministic");
}

#[test]
fn prop_content_hash_deterministic() {
    // content_hash should be a pure function of the polynomial's exponent
    // layout + degrees + leading coefficient (per its docstring's
    // memo-key contract). Two calls on the same poly must agree.
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let p = sample_p(&r);
    let h1 = p.content_hash();
    let h2 = p.content_hash();
    assert_eq!(h1, h2, "content_hash not deterministic");
    // Rebuilt-from-same-terms poly should have identical content_hash too.
    let p2 = sample_p(&r);
    assert_eq!(p.content_hash(), p2.content_hash(),
        "content_hash differs between identical builds");
}

// ── (1) again — Lex order specifics ─────────────────────────────────────

#[test]
fn prop_leading_term_lex_ordering() {
    // Under Lex, the leading monomial is the lex-greatest. By definition
    // of Lex, for `x0` and `x1^5` with x0 > x1 in variable order: x0 wins.
    let r = ring_with(101, 2, MonomialOrder::Lex);
    let f = &r.field;
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 5]), f.from_u64(1)),
        ],
        &r,
    );
    let lm = p.leading_monomial(&r).unwrap();
    assert_eq!(lm.exponents(), &[1, 0], "Lex LT should be x0, not x1^5");
}

#[test]
fn prop_leading_term_degrevlex_ordering() {
    // Under DegRevLex, the leading monomial has the highest total degree
    // among the terms (DegRevLex is degree-then-revlex). For `x0` vs
    // `x1^5`: 1 < 5 so x1^5 wins.
    let r = ring_with(101, 2, MonomialOrder::DegRevLex);
    let f = &r.field;
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 5]), f.from_u64(1)),
        ],
        &r,
    );
    let lm = p.leading_monomial(&r).unwrap();
    assert_eq!(lm.exponents(), &[0, 5], "DegRevLex LT should be x1^5");
}

#[test]
fn prop_reduce_by_empty_divisors_identity() {
    // Reducing by an empty divisor set returns the polynomial unchanged
    // (the normal form is the polynomial itself: nothing to cancel against).
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let p = sample_p(&r);
    let nf = p.reduce_by(&[], &r);
    assert!(poly_eq(&nf, &p, &r),
        "reduce_by(empty) should be identity");
}

#[test]
fn prop_reduce_zero_by_anything_is_zero() {
    // Reducing the zero polynomial yields zero regardless of divisors
    // (0 mod anything = 0).
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let f = &r.field;
    let d1 = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let nf = DensePoly::zero().reduce_by(&[d1], &r);
    assert!(nf.is_zero(), "0 reduced != 0");
}

#[test]
fn prop_reduce_self_yields_zero() {
    // p reduced by [p] yields zero: p divides p, so p ≡ 0 (mod p).
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let nf = p.reduce_by(&[p.clone()], &r);
        assert!(nf.is_zero(), "p mod p != 0 in GF({prime})");
    }
}

#[test]
fn prop_reduce_by_multiple_of_self_yields_zero() {
    // (q * p) reduced by [p] = 0 because p divides q*p in the ideal sense.
    for &prime in &[7u64, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let q = sample_q(&r);
        let qp = q.mul(&p, &r);
        let nf = qp.reduce_by(&[p.clone()], &r);
        assert!(nf.is_zero(), "(q*p) mod p != 0 in GF({prime})");
    }
}

// ── (9) ENGINE EQUIVALENCE: Dense vs Sparse ─────────────────────────────

fn ring_repr(prime: u64, n_vars: usize, repr: crate::config::ReprKind) -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(prime));
    let names: Vec<String> = (0..n_vars).map(|i| format!("x{i}")).collect();
    PolyRing::new_with_repr(f, names, MonomialOrder::DegRevLex, repr)
}

#[test]
fn prop_dense_sparse_add_agree() {
    // Building the same polynomial pair under each arm and adding must
    // yield equal coefficient lists (engine-equivalence).
    use crate::config::ReprKind;
    let rd = ring_repr(101, 3, ReprKind::Dense);
    let rs = ring_repr(101, 3, ReprKind::Sparse);
    let f = &rd.field;
    let build = |ring: &PolyRing| -> Polynomial {
        Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(2)),
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(5)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(7)),
            ],
            ring,
        )
    };
    let ad = build(&rd);
    let as_ = build(&rs);
    let bd = build(&rd).add(&Polynomial::variable(2, &rd), &rd);
    let bs = build(&rs).add(&Polynomial::variable(2, &rs), &rs);
    let sd = ad.add(&bd, &rd);
    let ss = as_.add(&bs, &rs);
    // Compare via dense materialisation.
    let sd_d = sd.as_dense(&rd).into_owned();
    let ss_d = ss.as_dense(&rs).into_owned();
    assert!(poly_eq(&sd_d, &ss_d, &rd),
        "dense+dense != sparse+sparse (after add)");
}

#[test]
fn prop_dense_sparse_mul_agree() {
    use crate::config::ReprKind;
    let rd = ring_repr(101, 3, ReprKind::Dense);
    let rs = ring_repr(101, 3, ReprKind::Sparse);
    let f = &rd.field;
    let build_a = |ring: &PolyRing| -> Polynomial {
        Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(1)),
            ],
            ring,
        )
    };
    let build_b = |ring: &PolyRing| -> Polynomial {
        Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
            ],
            ring,
        )
    };
    let pd = build_a(&rd).mul(&build_b(&rd), &rd);
    let ps = build_a(&rs).mul(&build_b(&rs), &rs);
    let pd_d = pd.as_dense(&rd).into_owned();
    let ps_d = ps.as_dense(&rs).into_owned();
    // Expected by math: (x+1)(x-1) = x^2 - 1.
    assert!(poly_eq(&pd_d, &ps_d, &rd),
        "dense*dense != sparse*sparse");
    assert_eq!(pd_d.num_terms(), 2);
    assert_eq!(pd_d.leading_monomial(&rd).unwrap().exponents(), &[2, 0, 0]);
}

#[test]
fn prop_dense_sparse_evaluate_agree() {
    use crate::config::ReprKind;
    let rd = ring_repr(101, 3, ReprKind::Dense);
    let rs = ring_repr(101, 3, ReprKind::Sparse);
    let f = &rd.field;
    let build = |ring: &PolyRing| -> Polynomial {
        Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(2)),
                (Monomial::from_exponents(vec![0, 1, 1]), f.from_u64(3)),
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(5)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(7)),
            ],
            ring,
        )
    };
    let pd = build(&rd);
    let ps = build(&rs);
    let v = vec![f.from_u64(2), f.from_u64(3), f.from_u64(5)];
    let ed = pd.evaluate(&v, &rd);
    let es = ps.evaluate(&v, &rs);
    assert!(f.eq(&ed, &es), "dense vs sparse evaluate disagree");
}
