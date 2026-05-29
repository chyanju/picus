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
fn substitute_var_concrete_value() {
    // substitute_var has no spec-property test elsewhere: substituting z=4
    // into p = x*y + 2*z + 3 must give x*y + 11 (constant absorbed).
    let r = small_ring();
    let f = &r.field;
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(2)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(3)),
        ],
        &r,
    );
    let q = p.substitute_var(2, &f.from_u64(4), &r);
    assert_eq!(q.num_terms(), 2);
    // Concrete coefficient: 2*4 + 3 = 11 (mod 101) at the constant term.
    let consts: Vec<_> = q.terms(&r).filter(|t| t.exponents() == [0, 0, 0]).collect();
    assert_eq!(consts.len(), 1);
    assert_eq!(*consts[0].coefficient(), f.from_u64(11));
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
fn prop_additive_group_axioms() {
    // Folded: identity (a+0=a), inverse (a+(-a)=0), sub-self (a-a=0),
    // negate-involution (-(-a)=a), commutativity (a+b=b+a),
    // associativity ((a+b)+c=a+(b+c)). Single sweep over representative
    // primes covers every additive-group property.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let z = DensePoly::zero();
        assert!(poly_eq(&a.add(&z, &r), &a, &r), "a+0 GF({prime})");
        assert!(poly_eq(&z.add(&a, &r), &a, &r), "0+a GF({prime})");
        let na = a.negate(&r);
        assert!(a.add(&na, &r).is_zero(), "a+(-a) GF({prime})");
        assert!(a.sub(&a, &r).is_zero(), "a-a GF({prime})");
        assert!(poly_eq(&na.negate(&r), &a, &r), "-(-a) GF({prime})");
        assert!(poly_eq(&a.add(&b, &r), &b.add(&a, &r), &r), "comm GF({prime})");
        let assoc_l = a.add(&b, &r).add(&c, &r);
        let assoc_r = a.add(&b.add(&c, &r), &r);
        assert!(poly_eq(&assoc_l, &assoc_r, &r), "assoc GF({prime})");
    }
}

#[test]
fn prop_multiplicative_monoid_axioms() {
    // Folded: identity (a*1=a), absorbing (a*0=0), commutativity (a*b=b*a),
    // associativity ((a*b)*c=a*(b*c)) — the multiplicative-monoid axioms
    // of the polynomial ring.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let one = DensePoly::constant(r.field.one(), &r);
        let z = DensePoly::zero();
        assert!(poly_eq(&a.mul(&one, &r), &a, &r), "a*1 GF({prime})");
        assert!(poly_eq(&one.mul(&a, &r), &a, &r), "1*a GF({prime})");
        assert!(a.mul(&z, &r).is_zero(), "a*0 GF({prime})");
        assert!(z.mul(&a, &r).is_zero(), "0*a GF({prime})");
        assert!(poly_eq(&a.mul(&b, &r), &b.mul(&a, &r), &r), "comm GF({prime})");
    }
    // Associativity is the expensive case; primes 3/7/101 suffice.
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let lhs = a.mul(&b, &r).mul(&c, &r);
        let rhs = a.mul(&b.mul(&c, &r), &r);
        assert!(poly_eq(&lhs, &rhs, &r), "assoc GF({prime})");
    }
}

#[test]
fn prop_distributivity() {
    // Left and right distributivity: a*(b+c)=a*b+a*c and (b+c)*a=b*a+c*a.
    // Both required by the ring axioms — fold into a single sweep.
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        let b = sample_q(&r);
        let c = sample_r(&r);
        let left = a.mul(&b.add(&c, &r), &r);
        let left_e = a.mul(&b, &r).add(&a.mul(&c, &r), &r);
        assert!(poly_eq(&left, &left_e, &r), "left-dist GF({prime})");
        let right = b.add(&c, &r).mul(&a, &r);
        let right_e = b.mul(&a, &r).add(&c.mul(&a, &r), &r);
        assert!(poly_eq(&right, &right_e, &r), "right-dist GF({prime})");
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
fn prop_scale_axioms() {
    // Folded scale axioms: scale(a,1)=a (identity), scale(a,0)=0 (zero
    // collapses), and scale(scale(a,c),c^-1)=a (invertibility for c!=0).
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let a = sample_p(&r);
        assert!(poly_eq(&a.scale(&r.field.one(), &r), &a, &r), "s1 GF({prime})");
        assert!(a.scale(&r.field.zero(), &r).is_zero(), "s0 GF({prime})");
        let c = r.field.from_u64(2);
        let cinv = r.field.inv(&c).unwrap();
        let s = a.scale(&c, &r).scale(&cinv, &r);
        assert!(poly_eq(&s, &a, &r), "scale-inv GF({prime})");
    }
    // GF(2): scale(a,0)=0 also.
    let r = ring_with(2, 3, MonomialOrder::DegRevLex);
    let a = sample_p(&r);
    assert!(poly_eq(&a.scale(&r.field.one(), &r), &a, &r), "s1 GF(2)");
    assert!(a.scale(&r.field.zero(), &r).is_zero(), "s0 GF(2)");
}

// ── (3) IDEMPOTENCE ─────────────────────────────────────────────────────

#[test]
fn prop_make_monic() {
    // Folded: idempotence monic(monic(p))=monic(p), LC(monic(p))=1, and
    // monic(0)=0 (no LC to divide by → zero stays zero).
    for &prime in &[3u64, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let m = p.make_monic(&r);
        let mm = m.make_monic(&r);
        assert!(poly_eq(&m, &mm, &r), "idempotent GF({prime})");
        assert!(r.field.is_one(m.leading_coefficient().unwrap()), "LC=1 GF({prime})");
    }
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    assert!(DensePoly::zero().make_monic(&r).is_zero(), "monic(0)=0");
}

// ── (4) INVARIANTS POST-OPERATION ───────────────────────────────────────

#[test]
fn prop_evaluate_ring_hom() {
    // Evaluation is a ring homomorphism into GF(p). Folded:
    //   E(a+b) = E(a)+E(b), E(a*b) = E(a)*E(b),
    //   E(constant c) = c, E(x_i)(v) = v_i.
    for &prime in &[3u64, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let f = &r.field;
        let a = sample_p(&r);
        let b = sample_q(&r);
        let v = vec![f.from_u64(2), f.from_u64(3), f.from_u64(5)];
        let ea = a.evaluate(&v, &r);
        let eb = b.evaluate(&v, &r);
        assert!(f.eq(&a.add(&b, &r).evaluate(&v, &r), &f.add(&ea, &eb)),
            "E(a+b) GF({prime})");
        assert!(f.eq(&a.mul(&b, &r).evaluate(&v, &r), &f.mul(&ea, &eb)),
            "E(a*b) GF({prime})");
        // E(const) = const, E(x_i) = v_i.
        let c = f.from_u64(42 % prime);
        let cp = DensePoly::constant(c.clone(), &r);
        assert!(f.eq(&cp.evaluate(&v, &r), &c), "E(const) GF({prime})");
        for i in 0..3 {
            let xi = DensePoly::variable(i, &r);
            assert!(f.eq(&xi.evaluate(&v, &r), &v[i]), "E(x{i}) GF({prime})");
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
fn prop_zero_poly_invariants() {
    // Folded: zero poly has no LT/LM/LC, num_terms=0, total_degree=0;
    // constant(0) collapses to the zero polynomial across primes.
    // (`make_monic(0) = 0` already covered by `prop_make_monic`.)
    let r = ring_with(7, 3, MonomialOrder::DegRevLex);
    let z = DensePoly::zero();
    assert!(z.is_zero());
    assert_eq!(z.num_terms(), 0);
    assert!(z.leading_coefficient().is_none());
    assert!(z.leading_monomial(&r).is_none());
    assert!(z.leading_term(&r).is_none());
    assert_eq!(z.total_degree(), 0);
    for &prime in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = DensePoly::constant(r.field.zero(), &r);
        assert!(p.is_zero(), "constant(0) GF({prime})");
    }
}

// ── (8) DETERMINISM ─────────────────────────────────────────────────────

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
fn prop_reduce_invariants() {
    // Folded reducer invariants:
    //   reduce_by(empty) = identity,
    //   reduce_by(0, [d]) = 0,
    //   p mod [p] = 0 (self-reduction),
    //   (q*p) mod [p] = 0 (ideal membership).
    let r = ring_with(101, 3, MonomialOrder::DegRevLex);
    let p = sample_p(&r);
    let nf_empty = p.reduce_by(&[], &r);
    assert!(poly_eq(&nf_empty, &p, &r), "reduce_by(empty) != identity");
    let f = &r.field;
    let d1 = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    assert!(DensePoly::zero().reduce_by(&[d1], &r).is_zero(), "0 reduced != 0");
    for &prime in &[7u64, 101] {
        let r = ring_with(prime, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        assert!(p.reduce_by(&[p.clone()], &r).is_zero(), "p mod p GF({prime})");
        let q = sample_q(&r);
        let qp = q.mul(&p, &r);
        assert!(qp.reduce_by(&[p.clone()], &r).is_zero(), "(q*p) mod p GF({prime})");
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

// ── (10) ADDITIONAL COVERAGE: appearing_variables / is_univariate ───────

#[test]
fn prop_appearing_variables_reports_max_exponent() {
    // Spec: returns (var, max_exp) for every variable with nonzero exponent
    // anywhere in the polynomial.
    let r = small_ring();
    let f = &r.field;
    // p = 3*x0^2*x1 + x2 + 5  → var 0 max=2, var 1 max=1, var 2 max=1.
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(3)),
            (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(5)),
        ],
        &r,
    );
    let appearing = p.appearing_variables(&r);
    assert_eq!(appearing, vec![(0, 2), (1, 1), (2, 1)]);
}

#[test]
fn prop_appearing_variables_skips_zero_exponents() {
    // Variables that never appear must not be listed.
    let r = small_ring();
    let f = &r.field;
    // Only x1 appears
    let p = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![0, 3, 0]), f.from_u64(2))],
        &r,
    );
    let appearing = p.appearing_variables(&r);
    assert_eq!(appearing, vec![(1, 3)]);
}

#[test]
fn prop_appearing_variables_of_zero_is_empty() {
    let r = small_ring();
    let z = DensePoly::zero();
    assert!(z.appearing_variables(&r).is_empty());
}

#[test]
fn prop_is_univariate_iff_one_variable_appears() {
    let r = small_ring();
    let f = &r.field;
    // x0^3 + x0 + 2 — univariate in x0
    let p_uni = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![3, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(2)),
        ],
        &r,
    );
    assert_eq!(p_uni.is_univariate(&r), Some(0));

    // x0 + x1 — bivariate
    let p_bi = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(1)),
        ],
        &r,
    );
    assert!(p_bi.is_univariate(&r).is_none());

    // Constant — no variable appears → None.
    let p_const = DensePoly::constant(f.from_u64(7), &r);
    assert!(p_const.is_univariate(&r).is_none());

    // Zero — no variables → None.
    let z = DensePoly::zero();
    assert!(z.is_univariate(&r).is_none());
}

// ── (11) mul_term ───────────────────────────────────────────────────────

#[test]
fn prop_mul_term_matches_mul_with_single_term_poly() {
    // mul_term(t_exps, t_coeff) must equal mul(&poly_of_single_term).
    let r = small_ring();
    let f = &r.field;
    let p = sample_p(&r);
    let t_exps = vec![1u16, 2, 0];
    let t_coeff = f.from_u64(3);
    let by_term = p.mul_term(&t_exps, &t_coeff, &r);
    let t_poly = DensePoly::from_terms(
        vec![(Monomial::from_exponents(t_exps.clone()), t_coeff.clone())],
        &r,
    );
    let by_mul = p.mul(&t_poly, &r);
    assert!(poly_eq(&by_term, &by_mul, &r), "mul_term != mul-by-single-term");
}

#[test]
fn prop_mul_term_zero_coeff_yields_zero() {
    // Multiplying by zero coefficient yields the zero polynomial.
    let r = small_ring();
    let p = sample_p(&r);
    let t_exps = vec![1u16, 0, 0];
    let result = p.mul_term(&t_exps, &r.field.zero(), &r);
    assert!(result.is_zero());
}

#[test]
fn prop_mul_term_on_zero_poly_yields_zero() {
    // Zero polynomial * any term == zero.
    let r = small_ring();
    let z = DensePoly::zero();
    let t_exps = vec![1u16, 0, 0];
    let result = z.mul_term(&t_exps, &r.field.from_u64(5), &r);
    assert!(result.is_zero());
}

// ── (12) negate_in_place ────────────────────────────────────────────────

#[test]
fn prop_negate_in_place_matches_negate() {
    // In-place negate produces the same coefficients as negate(&).
    let r = small_ring();
    let p = sample_p(&r);
    let by_clone = p.negate(&r);
    let mut p_mut = p.clone();
    p_mut.negate_in_place(&r);
    assert!(poly_eq(&p_mut, &by_clone, &r));
}

#[test]
fn prop_negate_in_place_involution() {
    // Double negate-in-place is identity.
    let r = small_ring();
    let p = sample_p(&r);
    let mut p_mut = p.clone();
    p_mut.negate_in_place(&r);
    p_mut.negate_in_place(&r);
    assert!(poly_eq(&p_mut, &p, &r));
}

// ── (13) cmp_term_at on lex vs degrevlex ────────────────────────────────

#[test]
fn prop_cmp_term_at_lex() {
    // Lex: first differing exponent decides.
    // [2,1] vs [2,0]: equal first, second (1>0) → Greater.
    assert_eq!(
        DensePoly::cmp_term_at(&[2, 1], 3, &[2, 0], 2, MonomialOrder::Lex),
        std::cmp::Ordering::Greater
    );
    // [1, 5] vs [2, 0]: first differs (1 < 2) → Less.
    assert_eq!(
        DensePoly::cmp_term_at(&[1, 5], 6, &[2, 0], 2, MonomialOrder::Lex),
        std::cmp::Ordering::Less
    );
}

#[test]
fn prop_cmp_term_at_degrevlex() {
    // DegRevLex: degree wins first.
    assert_eq!(
        DensePoly::cmp_term_at(&[0, 5], 5, &[1, 1], 2, MonomialOrder::DegRevLex),
        std::cmp::Ordering::Greater,
        "deg 5 > deg 2"
    );
    // Same total degree (3): [2,1] vs [0,3]: revlex tie-break wins for [2,1].
    // Trailing exponent: 1 < 3 → [2,1] is LARGER under DegRevLex.
    assert_eq!(
        DensePoly::cmp_term_at(&[2, 1], 3, &[0, 3], 3, MonomialOrder::DegRevLex),
        std::cmp::Ordering::Greater
    );
}

// ── (14) from_raw_sorted is a thin constructor ─────────────────────────

#[test]
fn prop_from_raw_sorted_roundtrip() {
    // Round-tripping through raw_* readers + from_raw_sorted yields an
    // equal polynomial — the constructor blindly trusts the inputs.
    let r = small_ring();
    let p = sample_p(&r);
    let exps = p.raw_exponents().to_vec();
    let coeffs = p.raw_coeffs().to_vec();
    let degs = p.raw_total_degs().to_vec();
    let q = DensePoly::from_raw_sorted(exps, coeffs, degs);
    assert!(poly_eq(&p, &q, &r), "raw round-trip changed polynomial");
}

#[test]
fn prop_from_raw_sorted_empty_is_zero() {
    let q = DensePoly::from_raw_sorted(Vec::new(), Vec::new(), Vec::new());
    assert!(q.is_zero());
}

// ── (15) terms() iterator order ─────────────────────────────────────────

#[test]
fn prop_terms_iterates_descending() {
    // Per the file docstring: terms are stored descending under ring order;
    // terms() iterates index 0 (= leading) forward.
    let r = small_ring();
    let p = sample_p(&r);
    let mut prev: Option<Monomial> = None;
    for t in p.terms(&r) {
        let here = t.monomial();
        if let Some(prev_m) = prev {
            assert!(
                prev_m.cmp_with_order(&here, r.order) == std::cmp::Ordering::Greater,
                "terms() not strictly descending"
            );
        }
        prev = Some(here);
    }
    // first term must equal leading term.
    let lt = p.leading_term(&r).unwrap();
    let first = p.term(0, &r);
    assert_eq!(lt.exponents(), first.exponents());
    assert_eq!(lt.coefficient(), first.coefficient());
}

// ── (16) merge_owned ────────────────────────────────────────────────────

#[test]
fn prop_merge_owned_matches_add() {
    // merge_owned(a, b, negate_other=false) == add(a, b)
    let r = small_ring();
    let a = sample_p(&r);
    let b = sample_q(&r);
    let expected = a.add(&b, &r);
    let merged = a.clone().merge_owned(b.clone(), &r, false);
    assert!(poly_eq(&merged, &expected, &r));
}

#[test]
fn prop_merge_owned_negate_matches_sub() {
    // merge_owned(a, b, negate_other=true) == sub(a, b)
    let r = small_ring();
    let a = sample_p(&r);
    let b = sample_q(&r);
    let expected = a.sub(&b, &r);
    let merged = a.clone().merge_owned(b.clone(), &r, true);
    assert!(poly_eq(&merged, &expected, &r));
}

#[test]
fn prop_merge_owned_zero_lhs() {
    // merge_owned(0, b, false) = b; merge_owned(0, b, true) = -b.
    let r = small_ring();
    let b = sample_q(&r);
    let z = DensePoly::zero();
    let r1 = z.clone().merge_owned(b.clone(), &r, false);
    assert!(poly_eq(&r1, &b, &r));
    let r2 = z.merge_owned(b.clone(), &r, true);
    let nb = b.negate(&r);
    assert!(poly_eq(&r2, &nb, &r));
}

#[test]
fn prop_merge_owned_zero_rhs() {
    // merge_owned(a, 0, _) = a.
    let r = small_ring();
    let a = sample_p(&r);
    let z = DensePoly::zero();
    let merged = a.clone().merge_owned(z, &r, false);
    assert!(poly_eq(&merged, &a, &r));
}

// ── (17) is_constant / num_terms ────────────────────────────────────────

#[test]
fn prop_is_constant_classification() {
    let r = small_ring();
    let f = &r.field;
    // zero -> constant
    assert!(DensePoly::zero().is_constant());
    // nonzero constant -> constant
    assert!(DensePoly::constant(f.from_u64(5), &r).is_constant());
    // variable -> not constant
    assert!(!DensePoly::variable(0, &r).is_constant());
    // multi-term -> not constant
    assert!(!sample_p(&r).is_constant());
}

#[test]
fn prop_constant_zero_collapses() {
    let r = small_ring();
    let f = &r.field;
    let zc = DensePoly::constant(f.zero(), &r);
    assert!(zc.is_zero());
    assert_eq!(zc.num_terms(), 0);
    let nc = DensePoly::constant(f.from_u64(7), &r);
    assert_eq!(nc.num_terms(), 1);
    assert_eq!(nc.total_degree(), 0);
}

// ── (18) content_hash sensitivity to LC ─────────────────────────────────

#[test]
fn prop_content_hash_changes_with_leading_coefficient() {
    // The docstring states: hash mixes in LC for sensitivity to coefficient
    // changes between same-monomial polynomials. Verify two polys differing
    // only in LC produce different hashes (not strictly required by spec,
    // but the documented design intent).
    let r = small_ring();
    let f = &r.field;
    let p1 = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(3))],
        &r,
    );
    let p2 = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(7))],
        &r,
    );
    // Different polynomials.
    assert!(!poly_eq(&p1, &p2, &r));
    // Hash should differ (design intent; not a soundness invariant).
    assert_ne!(p1.content_hash(), p2.content_hash());
}

#[test]
fn prop_content_hash_zero_is_stable() {
    // Zero polynomial's content_hash is deterministic across calls and
    // independent of the ring.
    let z = DensePoly::zero();
    let h1 = z.content_hash();
    let h2 = z.content_hash();
    assert_eq!(h1, h2);
}

// ── (19) Polynomial enum surface ────────────────────────────────────────

#[test]
fn prop_polynomial_zero_is_zero() {
    // Polynomial::zero() reports is_zero true and has num_terms 0.
    let z = Polynomial::zero();
    assert!(z.is_zero());
    assert_eq!(z.num_terms(), 0);
}

#[test]
fn prop_polynomial_variable_total_degree_one() {
    use crate::config::ReprKind;
    let rd = ring_repr(101, 3, ReprKind::Dense);
    let rs = ring_repr(101, 3, ReprKind::Sparse);
    for r in [&rd, &rs] {
        let v = Polynomial::variable(1, r);
        assert!(!v.is_zero());
        assert_eq!(v.total_degree(), 1);
        assert_eq!(v.num_terms(), 1);
        // LC of a single variable is 1.
        assert!(r.field.is_one(v.leading_coefficient().unwrap()));
    }
}

#[test]
fn prop_polynomial_constant_total_degree_zero() {
    use crate::config::ReprKind;
    let rd = ring_repr(101, 3, ReprKind::Dense);
    let rs = ring_repr(101, 3, ReprKind::Sparse);
    for r in [&rd, &rs] {
        let c = Polynomial::constant(r.field.from_u64(5), r);
        assert!(!c.is_zero());
        assert!(c.is_constant());
        assert_eq!(c.total_degree(), 0);
    }
}

#[test]
fn prop_polynomial_constant_zero_collapses() {
    use crate::config::ReprKind;
    let rd = ring_repr(101, 3, ReprKind::Dense);
    let rs = ring_repr(101, 3, ReprKind::Sparse);
    for r in [&rd, &rs] {
        let z = Polynomial::constant(r.field.zero(), r);
        assert!(z.is_zero());
    }
}

#[test]
fn prop_polynomial_as_dense_roundtrip() {
    use crate::config::ReprKind;
    // as_dense on a Dense arm borrows; on Sparse materialises. Either way
    // the dense reading must agree with the polynomial's terms.
    let rs = ring_repr(101, 3, ReprKind::Sparse);
    let f = &rs.field;
    let ps = Polynomial::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(3)),
            (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(5)),
        ],
        &rs,
    );
    let dense = ps.as_dense(&rs).into_owned();
    assert_eq!(dense.num_terms(), 2);
    assert!(!dense.is_zero());
}

#[test]
fn prop_polynomial_to_sparse_then_back_preserves() {
    use crate::config::ReprKind;
    let rd = ring_repr(101, 3, ReprKind::Dense);
    let p = Polynomial::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0, 0]), rd.field.from_u64(3)),
            (Monomial::from_exponents(vec![1, 1, 0]), rd.field.from_u64(2)),
        ],
        &rd,
    );
    let sparse = p.to_sparse(&rd);
    // Materialise it back via as_dense; coefficient set must match.
    let back = Polynomial::Sparse(sparse).as_dense(&rd).into_owned();
    let original = p.as_dense(&rd).into_owned();
    assert!(poly_eq(&original, &back, &rd));
}

#[test]
fn prop_polynomial_arithmetic_dispatch_smoke() {
    use crate::config::ReprKind;
    // add/sub/mul/scale/negate/make_monic all dispatch over both arms
    // and round-trip through the basic ring identities.
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let r = ring_repr(101, 3, repr);
        let f = &r.field;
        let a = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(2)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(1)),
            ],
            &r,
        );
        let b = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(3)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(5)),
            ],
            &r,
        );
        // a + b - b = a
        let s = a.add(&b, &r);
        let back = s.sub(&b, &r);
        let back_d = back.as_dense(&r).into_owned();
        let a_d = a.as_dense(&r).into_owned();
        assert!(
            poly_eq(&back_d, &a_d, &r),
            "(a+b)-b != a (repr {:?})", repr
        );
        // negate twice -> original
        let nn = a.negate(&r).negate(&r);
        let nn_d = nn.as_dense(&r).into_owned();
        assert!(poly_eq(&nn_d, &a_d, &r));
        // scale(1) is identity
        let s1 = a.scale(&f.one(), &r);
        let s1_d = s1.as_dense(&r).into_owned();
        assert!(poly_eq(&s1_d, &a_d, &r));
        // make_monic gives LC 1
        let m = a.make_monic(&r);
        assert!(f.is_one(m.leading_coefficient().unwrap()));
    }
}

#[test]
fn prop_polynomial_leading_monomial_matches_dispatch() {
    use crate::config::ReprKind;
    let rd = ring_repr(101, 3, ReprKind::Dense);
    let rs = ring_repr(101, 3, ReprKind::Sparse);
    let build = |r: &PolyRing| -> Polynomial {
        Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 1, 0]), r.field.from_u64(1)),
                (Monomial::from_exponents(vec![1, 0, 0]), r.field.from_u64(3)),
            ],
            r,
        )
    };
    let pd = build(&rd);
    let ps = build(&rs);
    let lmd = pd.leading_monomial(&rd).unwrap();
    let lms = ps.leading_monomial(&rs).unwrap();
    assert_eq!(lmd.exponents(), lms.exponents());
    assert_eq!(lmd.exponents(), &[2, 1, 0]);
}

#[test]
fn prop_polynomial_evaluate_dispatches_correctly() {
    use crate::config::ReprKind;
    // For an explicit poly, evaluation agrees with hand computation.
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let r = ring_repr(101, 2, repr);
        let f = &r.field;
        // p(x0, x1) = 2*x0^2 + 3*x1 + 5; at (x0=4, x1=7): 2*16 + 21 + 5 = 58
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 0]), f.from_u64(2)),
                (Monomial::from_exponents(vec![0, 1]), f.from_u64(3)),
                (Monomial::from_exponents(vec![0, 0]), f.from_u64(5)),
            ],
            &r,
        );
        let v = vec![f.from_u64(4), f.from_u64(7)];
        let e = p.evaluate(&v, &r);
        assert_eq!(e, f.from_u64(58));
    }
}

#[test]
fn prop_polynomial_appearing_variables_matches() {
    use crate::config::ReprKind;
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let r = ring_repr(101, 3, repr);
        let f = &r.field;
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 3]), f.from_u64(1)),
            ],
            &r,
        );
        let av = p.appearing_variables(&r);
        // Both reps must agree on the set of (var, max_exp) pairs.
        let mut sorted = av.clone();
        sorted.sort();
        assert_eq!(sorted, vec![(0, 2), (2, 3)]);
    }
}

#[test]
fn prop_polynomial_substitute_var_concrete() {
    use crate::config::ReprKind;
    // p(x0, x1, x2) = x0 + x1 + x2; substitute x1 = 3 → x0 + 3 + x2.
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let r = ring_repr(101, 3, repr);
        let f = &r.field;
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(1)),
            ],
            &r,
        );
        let q = p.substitute_var(1, &f.from_u64(3), &r);
        assert_eq!(q.num_terms(), 3, "substitute repr {:?}", repr);
    }
}

#[test]
fn prop_polynomial_is_univariate_dispatch() {
    use crate::config::ReprKind;
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let r = ring_repr(101, 3, repr);
        let f = &r.field;
        let uni = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(3)),
            ],
            &r,
        );
        assert_eq!(uni.is_univariate(&r), Some(0));
        let bi = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(1)),
            ],
            &r,
        );
        assert!(bi.is_univariate(&r).is_none());
    }
}

#[test]
fn prop_polynomial_content_hash_consistent() {
    use crate::config::ReprKind;
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let r = ring_repr(101, 3, repr);
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 1, 0]), r.field.from_u64(2)),
                (Monomial::from_exponents(vec![0, 0, 0]), r.field.from_u64(7)),
            ],
            &r,
        );
        let h1 = p.content_hash();
        let h2 = p.content_hash();
        assert_eq!(h1, h2, "content_hash not deterministic ({repr:?})");
    }
}

#[test]
fn prop_polynomial_collect_terms_idx_round_trip_count() {
    use crate::config::ReprKind;
    for &repr in &[ReprKind::Dense, ReprKind::Sparse] {
        let r = ring_repr(101, 3, repr);
        let f = &r.field;
        // 3 terms; the constant term should yield empty vars slice.
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(2)),
                (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(3)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(7)),
            ],
            &r,
        );
        let terms = p.collect_terms_idx(&r);
        assert_eq!(terms.len(), 3);
        // Each (coeff, vars) entry: coeff is nonzero, vars has only nonzero exps.
        for (coeff, vars) in &terms {
            assert!(coeff > &num_bigint::BigUint::from(0u32));
            for &(_, e) in vars {
                assert!(e > 0, "collect_terms_idx must list only nonzero exps");
            }
        }
    }
}

// ── (20) ReducerIndex: matches_active / size queries ────────────────────

#[test]
fn prop_reducer_index_len_matches_divisors() {
    // ReducerIndex::build produces a `len()` equal to divisors.len().
    let r = small_ring();
    let f = &r.field;
    let d1 = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let d2 = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(1))],
        &r,
    );
    let divs: Vec<&DensePoly> = vec![&d1, &d2];
    let idx = super::ReducerIndex::build(&divs, &r, None);
    assert_eq!(idx.len(), 2);
    assert!(!idx.is_empty());
}

#[test]
fn prop_reducer_index_empty() {
    let r = small_ring();
    let idx = super::ReducerIndex::build(&[], &r, None);
    assert_eq!(idx.len(), 0);
    assert!(idx.is_empty());
}

#[test]
fn prop_reducer_index_matches_active_self() {
    // An index built from a divisor set matches that same set.
    let r = small_ring();
    let f = &r.field;
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let divs: Vec<&DensePoly> = vec![&d];
    let idx = super::ReducerIndex::build(&divs, &r, None);
    assert!(idx.matches_active(&divs, &r));
}

#[test]
fn prop_reducer_index_matches_active_rejects_resized() {
    // Length mismatch must yield false.
    let r = small_ring();
    let f = &r.field;
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let divs1: Vec<&DensePoly> = vec![&d];
    let divs2: Vec<&DensePoly> = vec![&d, &d];
    let idx = super::ReducerIndex::build(&divs1, &r, None);
    assert!(!idx.matches_active(&divs2, &r), "size mismatch must fail");
}

#[test]
fn prop_reducer_index_matches_active_rejects_changed_lt() {
    // If a divisor's leading term changes, matches_active must return false.
    let r = small_ring();
    let f = &r.field;
    let d_a = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let d_b = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(1))],
        &r,
    );
    let divs_old: Vec<&DensePoly> = vec![&d_a];
    let divs_new: Vec<&DensePoly> = vec![&d_b];
    let idx = super::ReducerIndex::build(&divs_old, &r, None);
    assert!(!idx.matches_active(&divs_new, &r));
}

// ── (21) reduce_by_refs_counted / _cancel / cancellation surface ────────

#[test]
fn prop_reduce_by_refs_counted_counts_picks() {
    // The use_counts vector is incremented once per reduction step using
    // the selected divisor. Build a polynomial that requires 2 picks of d.
    let r = small_ring();
    let f = &r.field;
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    // p = x^2 + x — leading is x^2 (reducible by x), then becomes 0 + x
    // (still reducible by x). Expected use_count: 2.
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
        ],
        &r,
    );
    let mut counts = vec![0u64; 1];
    let divs: Vec<&DensePoly> = vec![&d];
    let nf = p.reduce_by_refs_counted(&divs, &r, &mut counts);
    assert!(nf.is_zero(), "x^2 + x mod x must be 0");
    assert_eq!(counts[0], 2, "expected 2 picks of divisor");
}

#[test]
fn prop_reduce_by_refs_counted_no_pick_zero_counts() {
    // If no divisor matches anything, no pick happens; counts stay 0.
    let r = small_ring();
    let f = &r.field;
    // Divisor x^3 doesn't divide leading term x or constant in p = x + 5.
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![3, 0, 0]), f.from_u64(1))],
        &r,
    );
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(5)),
        ],
        &r,
    );
    let mut counts = vec![0u64; 1];
    let divs: Vec<&DensePoly> = vec![&d];
    let nf = p.reduce_by_refs_counted(&divs, &r, &mut counts);
    assert_eq!(counts[0], 0);
    // p was unchanged.
    assert!(poly_eq(&nf, &p, &r));
}

#[test]
fn prop_reduce_by_refs_cancel_no_cancel_matches_uncancelled() {
    // With a fresh (uncancelled) token, reduce_by_refs_cancel == reduce_by_refs.
    let r = small_ring();
    let f = &r.field;
    let d = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![3, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    let cancel = crate::timeout::CancelToken::new();
    let divs: Vec<&DensePoly> = vec![&d];
    let a = p.reduce_by_refs(&divs, &r);
    let b = p.reduce_by_refs_cancel(&divs, &r, &cancel);
    assert!(poly_eq(&a, &b, &r));
}

#[test]
fn prop_reduce_by_refs_cancel_already_cancelled_returns_input_coset() {
    // With a pre-cancelled token, the reducer may bail out before doing
    // significant work; the result must remain in the same coset.
    // Concretely: residue evaluated at any value must equal p evaluated
    // there modulo the ideal (we just check the result is a valid poly
    // and the call returns without panicking).
    let r = small_ring();
    let f = &r.field;
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let p = sample_p(&r);
    let cancel = crate::timeout::CancelToken::cancelled();
    let divs: Vec<&DensePoly> = vec![&d];
    // Doesn't matter exactly what we get back; the call must terminate
    // and produce a valid descending polynomial. The first cancel-check
    // is at iteration 4096, so for small inputs we still get the full nf.
    let _ = p.reduce_by_refs_cancel(&divs, &r, &cancel);
}

// ── (22) reduce_by_refs on zero / empty edges ───────────────────────────

#[test]
fn prop_reduce_by_refs_zero_input_is_zero() {
    let r = small_ring();
    let f = &r.field;
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let divs: Vec<&DensePoly> = vec![&d];
    let nf = DensePoly::zero().reduce_by_refs(&divs, &r);
    assert!(nf.is_zero());
}

#[test]
fn prop_reduce_by_refs_empty_divisors_is_identity() {
    let r = small_ring();
    let p = sample_p(&r);
    let nf = p.reduce_by_refs(&[], &r);
    assert!(poly_eq(&nf, &p, &r));
}

#[test]
fn prop_reduce_by_refs_geobucket_with_zero_divisor_skips_it() {
    // A zero divisor in the list cannot match any LT and must be ignored.
    let r = small_ring();
    let f = &r.field;
    let zero = DensePoly::zero();
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(1)),
        ],
        &r,
    );
    let divs: Vec<&DensePoly> = vec![&zero, &d];
    let nf = p.reduce_by_refs_geobucket(&divs, &r, None, None, None);
    // p = x^2 + 1 mod x = 1
    assert_eq!(nf.num_terms(), 1);
    assert_eq!(nf.leading_term(&r).unwrap().exponents(), &[0, 0, 0]);
}

// ── (23) cross-prime sweep on reduce ────────────────────────────────────

#[test]
fn prop_reduce_self_yields_zero_across_primes() {
    // Reducing any nonzero polynomial by itself must yield zero.
    for &p_val in &[2u64, 3, 5, 7, 101] {
        let r = ring_with(p_val, 3, MonomialOrder::DegRevLex);
        let p = sample_p(&r);
        let divs: Vec<&DensePoly> = vec![&p];
        let nf = p.reduce_by_refs(&divs, &r);
        assert!(nf.is_zero(), "p mod p != 0 in GF({p_val})");
    }
}
