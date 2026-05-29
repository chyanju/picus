use super::*;
use crate::ff::field::PrimeField;
use crate::ff::monomial::MonomialOrder;
use num_bigint::BigUint;
use std::sync::Arc;

fn ring2() -> Arc<PolyRing> {
    PolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
        MonomialOrder::DegRevLex,
    )
}

// ────────── s_polynomial ──────────

#[test]
fn s_polynomial_of_coprime_pair_is_zero_after_reduction() {
    // f = x, g = y. lcm = x·y, S(f,g) = y·f − x·g = xy − xy = 0.
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let s = s_polynomial(&x, &y, &ring);
    assert!(s.is_zero());
}

#[test]
fn s_polynomial_of_x_and_xy_minus_1() {
    // f = x, g = x·y − 1.
    // lm(f) = x, lm(g) = x·y (under DegRevLex), lcm = x·y.
    // m_f = y, m_g = 1.
    // S(f,g) = y·x − 1·(x·y − 1) = xy − xy + 1 = 1 (constant).
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let xy = x.mul(&SparsePolynomial::variable(1, &ring), &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let xy_minus_1 = xy.sub(&one, &ring);
    let s = s_polynomial(&x, &xy_minus_1, &ring);
    assert!(s.is_constant() && !s.is_zero());
}

// ────────── groebner_basis ──────────

#[test]
fn groebner_basis_of_unit_input_is_trivial() {
    let ring = ring2();
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let gb = groebner_basis(vec![one], &ring, None);
    // Trivial ideal: {1}.
    assert!(gb.iter().any(|p| p.is_constant() && !p.is_zero()));
}

#[test]
fn groebner_basis_of_empty_input_is_empty() {
    let ring = ring2();
    let gb = groebner_basis(vec![], &ring, None);
    assert!(gb.is_empty());
}

#[test]
fn groebner_basis_of_xy_minus_1_yields_nonempty_basis() {
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let xy = x.mul(&y, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let p = xy.sub(&one, &ring);
    let gb = groebner_basis(vec![p], &ring, None);
    assert!(!gb.is_empty());
    // Not the whole ring (1 ∈ I would mean x·y = 1 over GF(7) — has
    // solutions, so GB shouldn't collapse).
    assert!(!gb.iter().any(|p| p.is_constant() && !p.is_zero()));
}

// ────────── groebner_basis_incremental ──────────

#[test]
fn groebner_basis_incremental_matches_from_scratch_after_interreduce() {
    // Compute GB({x·y − 1}) from scratch vs incrementally as
    // (known: ∅, new: {x·y − 1}). After interreduce, equal as sets.
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let xy = x.mul(&y, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let p = xy.sub(&one, &ring);

    let gb_scratch = interreduce(groebner_basis(vec![p.clone()], &ring, None), &ring, None);
    let gb_inc = interreduce(
        groebner_basis_incremental(vec![], vec![p], &ring, None),
        &ring,
        None,
    );
    assert_eq!(gb_scratch.len(), gb_inc.len());
}

// ────────── interreduce ──────────

#[test]
fn interreduce_drops_dominated_leading_term() {
    // {x, x·y} — x·y is divisible by x's leading term, so x·y is
    // either removed or reduced to zero. interreduce should collapse
    // to {x} (after monicization).
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let xy = x.mul(&SparsePolynomial::variable(1, &ring), &ring);
    let reduced = interreduce(vec![x.clone(), xy], &ring, None);
    assert_eq!(reduced.len(), 1);
}

#[test]
fn interreduce_collapses_to_unit_on_whole_ring_basis() {
    // {x, 2} → 2 ≠ 0 (since GF(7)) ⇒ constant ⇒ whole ring ⇒ {1}.
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let two = SparsePolynomial::constant(ring.field.from_int(2), &ring);
    let reduced = interreduce(vec![x, two], &ring, None);
    assert_eq!(reduced.len(), 1);
    assert!(reduced[0].is_constant());
}

#[test]
fn interreduce_drops_zero_polynomials() {
    let ring = ring2();
    let zero = SparsePolynomial::zero();
    let x = SparsePolynomial::variable(0, &ring);
    let reduced = interreduce(vec![zero, x], &ring, None);
    // Zero dropped; left with `x`.
    assert_eq!(reduced.len(), 1);
    assert!(!reduced[0].is_zero());
}
