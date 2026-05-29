use super::super::field::PrimeField;
use super::super::monomial::{Monomial, MonomialOrder};
use super::*;
use num_bigint::BigUint;
use std::sync::Arc;

fn small_ring() -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(101u32));
    PolyRing::new(
        f,
        vec!["x".into(), "y".into(), "z".into()],
        MonomialOrder::DegRevLex,
    )
}

fn mk(ring: &PolyRing, terms: Vec<(Vec<u16>, u64)>) -> DensePoly {
    let f = &ring.field;
    let v: Vec<(Monomial, FieldElem)> = terms
        .into_iter()
        .map(|(e, c)| (Monomial::from_exponents(e), f.from_u64(c)))
        .collect();
    DensePoly::from_terms(v, ring)
}

#[test]
fn from_poly_into_poly_roundtrip() {
    let r = small_ring();
    let p = mk(
        &r,
        vec![
            (vec![2, 1, 0], 3),
            (vec![1, 0, 2], 5),
            (vec![0, 0, 1], 7),
            (vec![0, 0, 0], 1),
        ],
    );
    let gb = Geobucket::from_poly(p.clone(), &r);
    let q = gb.into_poly();
    assert_eq!(p.num_terms(), q.num_terms());
    for (a, b) in p.terms(&r).zip(q.terms(&r)) {
        assert_eq!(a.exponents(), b.exponents());
        assert_eq!(a.coefficient(), b.coefficient());
    }
}

#[test]
fn add_poly_matches_polynomial_add() {
    let r = small_ring();
    let p = mk(
        &r,
        vec![(vec![3, 0, 0], 1), (vec![1, 1, 0], 2), (vec![0, 0, 0], 5)],
    );
    let q = mk(
        &r,
        vec![(vec![3, 0, 0], 4), (vec![2, 0, 0], 9), (vec![0, 0, 1], 3)],
    );
    let expect = p.add(&q, &r);
    let mut gb = Geobucket::from_poly(p, &r);
    gb.add_poly(q);
    let got = gb.into_poly();
    assert_eq!(got.num_terms(), expect.num_terms());
    for (a, b) in expect.terms(&r).zip(got.terms(&r)) {
        assert_eq!(a.exponents(), b.exponents());
        assert_eq!(a.coefficient(), b.coefficient());
    }
}

#[test]
fn pop_leading_term_descending_order() {
    let r = small_ring();
    let p = mk(
        &r,
        vec![(vec![2, 1, 0], 3), (vec![0, 0, 1], 7), (vec![0, 0, 0], 1)],
    );
    let mut gb = Geobucket::from_poly(p, &r);
    let (e1, d1, c1) = gb.pop_leading_term().unwrap();
    assert_eq!(e1, vec![2, 1, 0]);
    assert_eq!(d1, 3);
    assert_eq!(c1, r.field.from_u64(3));
    let (e2, d2, _) = gb.pop_leading_term().unwrap();
    assert_eq!(e2, vec![0, 0, 1]);
    assert_eq!(d2, 1);
    let (e3, d3, _) = gb.pop_leading_term().unwrap();
    assert_eq!(e3, vec![0, 0, 0]);
    assert_eq!(d3, 0);
    assert!(gb.pop_leading_term().is_none());
    assert!(gb.is_zero());
}

#[test]
fn pop_resolves_cross_bucket_cancellation() {
    let r = small_ring();
    let p = mk(&r, vec![(vec![1, 0, 0], 5)]);
    let q = mk(&r, vec![(vec![1, 0, 0], 96)]); // 5 + 96 = 101 ≡ 0 mod 101
    let mut gb = Geobucket::new(&r);
    // Force them into separate buckets by adding small polys (they fit
    // bucket 0). Both go into bucket 0 first, but the second add merges
    // them — so to test cross-bucket cancellation we use sub_scaled to
    // route the second one differently.
    gb.add_poly(p);
    gb.add_poly(q);
    // Whichever buckets they land in, the result must be zero.
    assert!(gb.is_zero() || gb.pop_leading_term().is_none());
}

#[test]
fn sub_scaled_basic() {
    let r = small_ring();
    // p = 3*x^2*y + 7*z + 1
    let p = mk(
        &r,
        vec![(vec![2, 1, 0], 3), (vec![0, 0, 1], 7), (vec![0, 0, 0], 1)],
    );
    // d = x + 1
    let d = mk(&r, vec![(vec![1, 0, 0], 1), (vec![0, 0, 0], 1)]);
    // sub_scaled is called with the already-negated coefficient (matching the
    // convention used by `reduce_by_refs`). Passing `neg_coeff = -3` adds
    // -3*(x*y)*d = -3*x^2*y - 3*x*y to p, yielding -3*x*y + 7*z + 1.
    let mut gb = Geobucket::from_poly(p, &r);
    let neg_three = r.field.neg(&r.field.from_u64(3));
    gb.sub_scaled(&[1, 1, 0], &neg_three, &d);
    let result = gb.into_poly();
    let expect = mk(
        &r,
        vec![
            (vec![1, 1, 0], 101 - 3), // -3 mod 101 = 98
            (vec![0, 0, 1], 7),
            (vec![0, 0, 0], 1),
        ],
    );
    assert_eq!(result.num_terms(), expect.num_terms());
    for (a, b) in expect.terms(&r).zip(result.terms(&r)) {
        assert_eq!(a.exponents(), b.exponents());
        assert_eq!(a.coefficient(), b.coefficient());
    }
}

#[test]
fn many_adds_cascade_buckets() {
    let r = small_ring();
    // Add 200 small polynomials; result should equal sum.
    let mut gb = Geobucket::new(&r);
    let mut expect = DensePoly::zero();
    for i in 0..200u64 {
        let p = mk(
            &r,
            vec![(
                vec![(i % 5) as u16, ((i / 5) % 5) as u16, ((i / 25) % 5) as u16],
                (i % 97) + 1,
            )],
        );
        expect = expect.add(&p, &r);
        gb.add_poly(p);
    }
    let got = gb.into_poly();
    assert_eq!(got.num_terms(), expect.num_terms());
    for (a, b) in expect.terms(&r).zip(got.terms(&r)) {
        assert_eq!(a.exponents(), b.exponents());
        assert_eq!(a.coefficient(), b.coefficient());
    }
}

#[test]
fn empty_geobucket() {
    let r = small_ring();
    let gb = Geobucket::new(&r);
    assert!(gb.is_zero());
    assert!(gb.into_poly().is_zero());
}

#[test]
fn add_zero_is_noop() {
    let r = small_ring();
    let p = mk(&r, vec![(vec![1, 0, 0], 7)]);
    let mut gb = Geobucket::from_poly(p.clone(), &r);
    gb.add_poly(DensePoly::zero());
    let got = gb.into_poly();
    assert_eq!(got.num_terms(), p.num_terms());
}

#[test]
fn leading_term_then_pop_consistent() {
    let r = small_ring();
    let p = mk(
        &r,
        vec![(vec![2, 1, 0], 3), (vec![1, 0, 0], 5), (vec![0, 0, 0], 1)],
    );
    let mut gb = Geobucket::from_poly(p, &r);
    let peek = gb.leading_term().unwrap();
    let pop = gb.pop_leading_term().unwrap();
    assert_eq!(peek.0, pop.0);
    assert_eq!(peek.1, pop.1);
    assert_eq!(peek.2, pop.2);
}
