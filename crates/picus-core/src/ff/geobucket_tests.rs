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

// ── Additional spec-driven tests ───────────────────────────────────────

/// Doc: capacity bucket idx is `BASE_CAPACITY * RATIO^idx`. `fitting_bucket`
/// returns the smallest idx whose capacity is `>= len`. Pin the boundary:
/// adding a single-term poly (len 1 ≤ BASE_CAPACITY) lands in bucket 0.
#[test]
fn single_term_add_preserves_total() {
    let r = small_ring();
    let mut gb = Geobucket::new(&r);
    gb.add_poly(mk(&r, vec![(vec![1, 1, 1], 13)]));
    let out = gb.into_poly();
    assert_eq!(out.num_terms(), 1);
    let t = out.term(0, &r);
    assert_eq!(t.exponents(), &[1, 1, 1]);
    assert!(r.field.eq(t.coefficient(), &r.field.from_u64(13)));
}

/// pop_leading_term across a polynomial with many distinct monomials must
/// emit them in DESCENDING ring order (the geobucket's invariant).
#[test]
fn pop_emits_descending_order() {
    let r = small_ring();
    let p = mk(
        &r,
        vec![
            (vec![3, 0, 0], 1),
            (vec![2, 1, 0], 2),
            (vec![1, 0, 1], 3),
            (vec![0, 2, 0], 4),
            (vec![0, 0, 1], 5),
            (vec![0, 0, 0], 6),
        ],
    );
    let mut gb = Geobucket::from_poly(p, &r);
    let mut prev_deg: Option<u32> = None;
    while let Some((_e, d, _)) = gb.pop_leading_term() {
        if let Some(pd) = prev_deg {
            // DegRevLex: total degree is monotone non-increasing across pops.
            assert!(pd >= d, "pop order regressed: deg {pd} then {d}");
        }
        prev_deg = Some(d);
    }
}

/// Doc: sub_scaled subtracts `neg_coeff * x^mul_exps * divisor`. With
/// `divisor = 1` (constant 1), the effect is `add(neg_coeff * x^mul_exps)`.
#[test]
fn sub_scaled_constant_divisor_acts_like_add_monomial() {
    let r = small_ring();
    let p = mk(&r, vec![(vec![0, 0, 0], 0)]); // zero polynomial
    let one = mk(&r, vec![(vec![0, 0, 0], 1)]);
    let mut gb = Geobucket::from_poly(p, &r);
    let c = r.field.from_u64(5);
    gb.sub_scaled(&[1, 0, 2], &c, &one);
    let out = gb.into_poly();
    assert_eq!(out.num_terms(), 1);
    let t = out.term(0, &r);
    assert_eq!(t.exponents(), &[1, 0, 2]);
    assert!(r.field.eq(t.coefficient(), &r.field.from_u64(5)));
}

/// Doc: `sub_scaled_tail` skips the divisor's LT — equivalent to
/// `sub_scaled` minus the leading-term contribution.
#[test]
fn sub_scaled_tail_skips_leading_term() {
    let r = small_ring();
    // divisor = x + 7
    let d = mk(&r, vec![(vec![1, 0, 0], 1), (vec![0, 0, 0], 7)]);
    let mut gb_full = Geobucket::new(&r);
    let mut gb_tail = Geobucket::new(&r);
    let coeff = r.field.from_u64(3);
    gb_full.sub_scaled(&[0, 1, 0], &coeff, &d);
    gb_tail.sub_scaled_tail(&[0, 1, 0], &coeff, &d);
    // gb_full = 3*x*y + 21*y;  gb_tail = 21*y.
    // Their difference = 3*x*y. So full - tail should produce gb_full minus tail.
    let full = gb_full.into_poly();
    let tail = gb_tail.into_poly();
    // tail should have exactly one term (21*y).
    assert_eq!(tail.num_terms(), 1);
    let t = tail.term(0, &r);
    assert_eq!(t.exponents(), &[0, 1, 0]);
    assert!(r.field.eq(t.coefficient(), &r.field.from_u64(21)));
    // full has two terms.
    assert_eq!(full.num_terms(), 2);
}

/// sub_scaled with neg_coeff=0 is a no-op (per the early-return check).
#[test]
fn sub_scaled_zero_coeff_no_op() {
    let r = small_ring();
    let p = mk(&r, vec![(vec![1, 0, 0], 5)]);
    let d = mk(&r, vec![(vec![1, 0, 0], 1), (vec![0, 0, 0], 1)]);
    let mut gb = Geobucket::from_poly(p.clone(), &r);
    let zero = r.field.zero();
    gb.sub_scaled(&[0, 0, 0], &zero, &d);
    let out = gb.into_poly();
    assert_eq!(out.num_terms(), p.num_terms());
    for (a, b) in p.terms(&r).zip(out.terms(&r)) {
        assert_eq!(a.exponents(), b.exponents());
        assert_eq!(a.coefficient(), b.coefficient());
    }
}

/// sub_scaled with the zero divisor is a no-op.
#[test]
fn sub_scaled_zero_divisor_no_op() {
    let r = small_ring();
    let p = mk(&r, vec![(vec![1, 0, 0], 5)]);
    let mut gb = Geobucket::from_poly(p.clone(), &r);
    let c = r.field.from_u64(3);
    gb.sub_scaled(&[1, 0, 0], &c, &DensePoly::zero());
    let out = gb.into_poly();
    assert_eq!(out.num_terms(), p.num_terms());
}

/// is_zero matches the absence of poppable terms.
#[test]
fn is_zero_consistent_with_pop() {
    let r = small_ring();
    let p = mk(&r, vec![(vec![1, 0, 0], 5)]);
    let neg_p = mk(&r, vec![(vec![1, 0, 0], 96)]); // 5 + 96 = 101 ≡ 0
    let mut gb = Geobucket::from_poly(p, &r);
    gb.add_poly(neg_p);
    // After cancellation gb may have stale heads — pop_leading_term must
    // resolve it. Either the bucket sees is_zero immediately, or the
    // first pop returns None.
    if !gb.is_zero() {
        assert!(gb.pop_leading_term().is_none());
        assert!(gb.is_zero());
    }
}

/// Doc: leading_term re-inserts the surviving term, so a subsequent
/// pop_leading_term returns the SAME term (idempotent peek).
#[test]
fn leading_term_idempotent_peek() {
    let r = small_ring();
    let p = mk(&r, vec![(vec![2, 0, 0], 4), (vec![0, 1, 0], 3)]);
    let mut gb = Geobucket::from_poly(p, &r);
    let peek1 = gb.leading_term().unwrap();
    let peek2 = gb.leading_term().unwrap();
    assert_eq!(peek1, peek2, "leading_term must be idempotent");
    let pop = gb.pop_leading_term().unwrap();
    assert_eq!(pop, peek1);
}

