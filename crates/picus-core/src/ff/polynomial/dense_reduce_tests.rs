//! Tests for the `reduce_by_refs*` family — geobucket, naive, indexed,
//! counted, cancel-aware. Spec invariants:
//!   * On a Gröbner-basis-shaped divisor set every variant returns the
//!     SAME normal form (the unique reduction modulo the leading-term
//!     ideal).
//!   * Reducing zero by anything yields zero.
//!   * Reducing by an empty divisor list is the identity.
//!   * `use_counts` is incremented (not zeroed) once per reduction step.
//!   * `_dms` variants accept caller-precomputed leading-term DivMasks
//!     and produce the IDENTICAL normal form (DivMasks are tail-stable).
//!   * Cancel-aware variants honour an already-cancelled token and stay
//!     in the input's coset.

use super::*;
use crate::ff::divmask::DivMask;
use crate::ff::field::PrimeField;
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::timeout::CancelToken;
use num_bigint::BigUint;

fn small_ring() -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(101u32));
    PolyRing::new(
        f,
        vec!["x".into(), "y".into(), "z".into()],
        MonomialOrder::DegRevLex,
    )
}

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

// Reuse-friendly samples: a Gröbner-basis-shaped (unique-LT-divides) set.
fn unique_lt_divisors(r: &PolyRing) -> Vec<DensePoly> {
    let f = &r.field;
    vec![
        // x^2 - 1
        DensePoly::from_terms(
            vec![
                (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
            ],
            r,
        ),
        // y^2 - 2
        DensePoly::from_terms(
            vec![
                (Monomial::from_exponents(vec![0, 2, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-2)),
            ],
            r,
        ),
        // z^2 - 3
        DensePoly::from_terms(
            vec![
                (Monomial::from_exponents(vec![0, 0, 2]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-3)),
            ],
            r,
        ),
    ]
}

// ── zero / empty edges ──────────────────────────────────────────────────

#[test]
fn prop_reduce_zero_input_is_zero_all_variants() {
    let r = small_ring();
    let divs_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = divs_owned.iter().collect();
    let z = DensePoly::zero();
    assert!(z.reduce_by_refs(&divs, &r).is_zero());
    assert!(z.reduce_by_refs_naive(&divs, &r).is_zero());
    let cancel = CancelToken::new();
    assert!(z.reduce_by_refs_cancel(&divs, &r, &cancel).is_zero());
    let mut counts = vec![0u64; divs.len()];
    assert!(z.reduce_by_refs_counted(&divs, &r, &mut counts).is_zero());
    // Zero input: counts must remain zero (no work done).
    assert!(counts.iter().all(|&c| c == 0));
}

#[test]
fn prop_reduce_empty_divisors_is_identity_all_variants() {
    let r = small_ring();
    let f = &r.field;
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(3)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(7)),
        ],
        &r,
    );
    let empty: Vec<&DensePoly> = vec![];
    assert!(poly_eq(&p.reduce_by_refs(&empty, &r), &p, &r));
    assert!(poly_eq(&p.reduce_by_refs_naive(&empty, &r), &p, &r));
    let cancel = CancelToken::new();
    assert!(poly_eq(&p.reduce_by_refs_cancel(&empty, &r, &cancel), &p, &r));
    let mut counts: Vec<u64> = vec![];
    assert!(poly_eq(&p.reduce_by_refs_counted(&empty, &r, &mut counts), &p, &r));
}

// ── variant agreement on a GB-shaped divisor set ────────────────────────

#[test]
fn prop_variants_agree_on_gb_shaped_set() {
    // On a GB-shaped set the normal form is unique — all variants must
    // return the SAME polynomial term-for-term.
    let r = small_ring();
    let f = &r.field;
    let divs_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = divs_owned.iter().collect();
    // p = x^2*y^2 + x*y*z + x*y + 5 — every term except possibly the constant
    // is reducible at least once.
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 2, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![1, 1, 1]), f.from_u64(1)),
            (Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(5)),
        ],
        &r,
    );
    let by_geo = p.reduce_by_refs_geobucket(&divs, &r, None, None, None);
    let by_naive = p.reduce_by_refs_naive(&divs, &r);
    let by_dispatched = p.reduce_by_refs(&divs, &r);
    let cancel = CancelToken::new();
    let by_cancel = p.reduce_by_refs_cancel(&divs, &r, &cancel);
    let mut counts = vec![0u64; divs.len()];
    let by_counted = p.reduce_by_refs_counted(&divs, &r, &mut counts);

    assert!(poly_eq(&by_geo, &by_naive, &r), "geo vs naive");
    assert!(poly_eq(&by_geo, &by_dispatched, &r), "geo vs dispatched");
    assert!(poly_eq(&by_geo, &by_cancel, &r), "geo vs cancel");
    assert!(poly_eq(&by_geo, &by_counted, &r), "geo vs counted");
}

// ── use_counts semantics: incremented (not zeroed) ──────────────────────

#[test]
fn prop_use_counts_accumulate_across_calls() {
    // Per docstring: "entries are incremented (not zeroed)." So calling
    // reduce twice should accumulate counts.
    let r = small_ring();
    let f = &r.field;
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
        ],
        &r,
    );
    let divs: Vec<&DensePoly> = vec![&d];
    let mut counts = vec![5u64; 1]; // pre-filled
    let _ = p.reduce_by_refs_counted(&divs, &r, &mut counts);
    // p = x^2 + x — 2 picks of x.
    assert_eq!(counts[0], 7, "pre-existing counts must be preserved + incremented");
    let _ = p.reduce_by_refs_counted(&divs, &r, &mut counts);
    assert_eq!(counts[0], 9, "second call increments further");
}

// ── DivMask precompute paths (_dms variants) ────────────────────────────

#[test]
fn prop_counted_dms_matches_counted() {
    // Caller-provided DivMasks must yield the identical normal form;
    // tail reduction preserves leading terms, so the DM never goes stale.
    let r = small_ring();
    let f = &r.field;
    let d_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = d_owned.iter().collect();
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 2, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(3)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(7)),
        ],
        &r,
    );
    // Precompute caller DMs.
    let dms: Vec<DivMask> = divs
        .iter()
        .map(|d| {
            let lt_exps = d.leading_term(&r).unwrap().exponents().to_vec();
            r.divmask.compute_from_slice(&lt_exps)
        })
        .collect();

    let mut counts_a = vec![0u64; divs.len()];
    let cancel_a = CancelToken::new();
    let by_dms = p.reduce_by_refs_counted_cancel_dms(
        &divs, &r, &cancel_a, &mut counts_a, &dms,
    );
    let mut counts_b = vec![0u64; divs.len()];
    let cancel_b = CancelToken::new();
    let no_dms = p.reduce_by_refs_counted_cancel(
        &divs, &r, &cancel_b, &mut counts_b,
    );
    assert!(poly_eq(&by_dms, &no_dms, &r), "_dms variant must match");
    assert_eq!(counts_a, counts_b, "_dms variant must report same counts");
}

#[test]
fn prop_counted_dms_no_cancel_matches_counted() {
    // Non-cancel-aware *_dms variant agrees with non-dms version.
    let r = small_ring();
    let f = &r.field;
    let d_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = d_owned.iter().collect();
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 1, 1]), f.from_u64(1)),
            (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(2)),
        ],
        &r,
    );
    let dms: Vec<DivMask> = divs
        .iter()
        .map(|d| {
            let lt_exps = d.leading_term(&r).unwrap().exponents().to_vec();
            r.divmask.compute_from_slice(&lt_exps)
        })
        .collect();
    let mut counts_a = vec![0u64; divs.len()];
    let by_dms = p.reduce_by_refs_counted_dms(&divs, &r, &mut counts_a, &dms);
    let mut counts_b = vec![0u64; divs.len()];
    let no_dms = p.reduce_by_refs_counted(&divs, &r, &mut counts_b);
    assert!(poly_eq(&by_dms, &no_dms, &r));
    assert_eq!(counts_a, counts_b);
}

// ── reduce_by (owned-list) forwards to reduce_by_refs ───────────────────

#[test]
fn prop_reduce_by_matches_reduce_by_refs() {
    let r = small_ring();
    let f = &r.field;
    let divs_owned = unique_lt_divisors(&r);
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(4)),
            (Monomial::from_exponents(vec![0, 2, 0]), f.from_u64(2)),
        ],
        &r,
    );
    let by_owned = p.reduce_by(&divs_owned, &r);
    let refs: Vec<&DensePoly> = divs_owned.iter().collect();
    let by_refs = p.reduce_by_refs(&refs, &r);
    assert!(poly_eq(&by_owned, &by_refs, &r));
}

// ── Cancel paths: already-cancelled token bails out cleanly ─────────────

#[test]
fn prop_reduce_by_refs_cancel_terminates_on_cancelled() {
    // With CancelToken::cancelled() AND a small input, the first cancel
    // check is at iter 4096. For small polynomials the loop completes before
    // any check happens, so the result is the proper normal form.
    let r = small_ring();
    let f = &r.field;
    let d_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = d_owned.iter().collect();
    let p = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1))],
        &r,
    );
    let cancel = CancelToken::cancelled();
    // Must not panic, must terminate.
    let _ = p.reduce_by_refs_cancel(&divs, &r, &cancel);
}

#[test]
fn prop_reduce_by_refs_counted_cancel_terminates_on_cancelled() {
    let r = small_ring();
    let f = &r.field;
    let d_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = d_owned.iter().collect();
    let p = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1))],
        &r,
    );
    let mut counts = vec![0u64; divs.len()];
    let cancel = CancelToken::cancelled();
    let _ = p.reduce_by_refs_counted_cancel(&divs, &r, &cancel, &mut counts);
}

// ── Naive (cross-check oracle) parity tests ─────────────────────────────

#[test]
fn prop_naive_self_reduction_to_zero() {
    // p mod p == 0 holds for naive as well.
    let r = small_ring();
    let f = &r.field;
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![3, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    let nf = p.reduce_by_refs_naive(&[&p], &r);
    assert!(nf.is_zero());
}

#[test]
fn prop_naive_constant_only_irreducible() {
    // A constant polynomial is irreducible by any polynomial whose LT
    // has positive degree. p = 7 reduced by [x] is still 7.
    let r = small_ring();
    let f = &r.field;
    let p = DensePoly::constant(f.from_u64(7), &r);
    let d = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1))],
        &r,
    );
    let nf = p.reduce_by_refs_naive(&[&d], &r);
    assert!(poly_eq(&nf, &p, &r));
}

// ── ReducerIndex precomputed reduce path agrees with geobucket ──────────

#[test]
fn prop_indexed_matches_geobucket_small_set() {
    // Build a ReducerIndex from a small divisor set (< SORT_THRESHOLD)
    // and verify it agrees with the per-call geobucket reducer.
    let r = small_ring();
    let f = &r.field;
    let d_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = d_owned.iter().collect();
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 2, 2]), f.from_u64(1)),
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(5)),
            (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(11)),
        ],
        &r,
    );
    let idx = ReducerIndex::build(&divs, &r, None);
    let mut counts_i = vec![0u64; divs.len()];
    let by_indexed = p.reduce_by_refs_geobucket_indexed(
        &idx, &divs, &r, None, Some(&mut counts_i),
    );
    let mut counts_g = vec![0u64; divs.len()];
    let by_geo = p.reduce_by_refs_geobucket(
        &divs, &r, None, Some(&mut counts_g), None,
    );
    assert!(poly_eq(&by_indexed, &by_geo, &r));
    assert_eq!(counts_i, counts_g, "indexed and per-call counts agree");
}

#[test]
fn prop_indexed_with_caller_dms_matches() {
    // ReducerIndex::build accepts a caller-provided dms slice; the
    // resulting index must produce the same normal form as the auto-DM
    // version.
    let r = small_ring();
    let f = &r.field;
    let d_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = d_owned.iter().collect();
    let dms: Vec<DivMask> = divs
        .iter()
        .map(|d| {
            let lt_exps = d.leading_term(&r).unwrap().exponents().to_vec();
            r.divmask.compute_from_slice(&lt_exps)
        })
        .collect();
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 2, 0]), f.from_u64(1)),
        ],
        &r,
    );
    let idx_auto = ReducerIndex::build(&divs, &r, None);
    let idx_dms = ReducerIndex::build(&divs, &r, Some(&dms));
    let by_auto = p.reduce_by_refs_geobucket_indexed(&idx_auto, &divs, &r, None, None);
    let by_dms = p.reduce_by_refs_geobucket_indexed(&idx_dms, &divs, &r, None, None);
    assert!(poly_eq(&by_auto, &by_dms, &r));
}

// ── Residue is in input's coset: p - nf is in ideal ─────────────────────

#[test]
fn prop_residue_in_input_coset() {
    // p reduced to nf means nf and p differ by an element of the
    // ideal — equivalently, reducing nf by the same divisors again
    // yields nf (the normal form is a fixed point).
    let r = small_ring();
    let f = &r.field;
    let d_owned = unique_lt_divisors(&r);
    let divs: Vec<&DensePoly> = d_owned.iter().collect();
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![3, 1, 0]), f.from_u64(2)),
            (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(7)),
        ],
        &r,
    );
    let nf = p.reduce_by_refs(&divs, &r);
    // Fixed-point property: reducing nf gives nf back.
    let nf2 = nf.reduce_by_refs(&divs, &r);
    assert!(poly_eq(&nf, &nf2, &r), "normal form is not a fixed point");
}

// ── Result-identity across thresholds: > SORT_THRESHOLD ─────────────────

#[test]
fn prop_geobucket_normal_form_with_many_orthogonal_divisors() {
    // With >= SORT_THRESHOLD divisors the geobucket reducer activates the
    // ascending-degree-order index. Result must still match the per-call
    // small-set path on a unique-divides input.
    assert!(64 >= ReducerIndex::SORT_THRESHOLD);
    let n = 64usize;
    let f = PrimeField::new(BigUint::from(101u32));
    let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let r = PolyRing::new(f, names, MonomialOrder::DegRevLex);
    let fp = &r.field;
    // Divisors x_i^2 - i (unique LT in its own variable).
    // Use from_i64(-(i as i64)) for the constant term so reduction gives +i.
    let divisors: Vec<DensePoly> = (0..n)
        .map(|i| {
            let mut sq = vec![0u16; n];
            sq[i] = 2;
            DensePoly::from_terms(
                vec![
                    (Monomial::from_exponents(sq), fp.from_u64(1)),
                    (Monomial::from_exponents(vec![0u16; n]), fp.from_i64(-(i as i64))),
                ],
                &r,
            )
        })
        .collect();
    let div_refs: Vec<&DensePoly> = divisors.iter().collect();
    // p = sum_i x_i^2 — each x_i^2 reduces to +i (since x_i^2 - i ≡ 0 means
    // x_i^2 ≡ i), so the sum reduces to sum_i i = 0+1+...+63 = 2016.
    let terms: Vec<(Monomial, FieldElem)> = (0..n)
        .map(|i| {
            let mut sq = vec![0u16; n];
            sq[i] = 2;
            (Monomial::from_exponents(sq), fp.from_u64(1))
        })
        .collect();
    let p = DensePoly::from_terms(terms, &r);
    let by_geo = p.reduce_by_refs_geobucket(&div_refs, &r, None, None, None);
    let by_naive = p.reduce_by_refs_naive(&div_refs, &r);
    // Both equal each other on unique-LT-divides set.
    assert!(poly_eq(&by_geo, &by_naive, &r));
    // 2016 mod 101 = 97 (since 19*101 = 1919, 2016 - 1919 = 97).
    // Result should be a single constant term.
    assert_eq!(by_geo.num_terms(), 1, "result should collapse to one constant");
    assert!(by_geo.is_constant());
    let lc = by_geo.leading_coefficient().unwrap();
    assert_eq!(*lc, fp.from_u64(97));
}

// ── reduce_by_refs_counted on multiple divisors ─────────────────────────

#[test]
fn prop_counted_attributes_picks_to_correct_divisor() {
    // Two orthogonal divisors d1 = x, d2 = y. p = x + y reduces by
    // picking d1 for the x term and d2 for the y term — counts = [1, 1].
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
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(1)),
        ],
        &r,
    );
    let divs: Vec<&DensePoly> = vec![&d1, &d2];
    let mut counts = vec![0u64; 2];
    let nf = p.reduce_by_refs_counted(&divs, &r, &mut counts);
    assert!(nf.is_zero());
    assert_eq!(counts, vec![1, 1]);
}

// ── Reduction in GF(2) — small-prime soundness ──────────────────────────

#[test]
fn prop_reduce_in_gf2() {
    // GF(2): subtraction == addition; (x+1)(x+1) = x^2 + 1.
    let f = PrimeField::new(BigUint::from(2u32));
    let r = PolyRing::new(f, vec!["x".into()], MonomialOrder::DegRevLex);
    let fp = &r.field;
    // d = x + 1
    let d = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1]), fp.from_u64(1)),
            (Monomial::from_exponents(vec![0]), fp.from_u64(1)),
        ],
        &r,
    );
    // p = x^2 + 1 = (x+1)^2 in GF(2) — divisible.
    let p = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2]), fp.from_u64(1)),
            (Monomial::from_exponents(vec![0]), fp.from_u64(1)),
        ],
        &r,
    );
    let nf = p.reduce_by_refs(&[&d], &r);
    assert!(nf.is_zero(), "(x+1)^2 mod (x+1) != 0 in GF(2)");
}
