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
