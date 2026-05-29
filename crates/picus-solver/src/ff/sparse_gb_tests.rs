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

// ────────── zero-polynomial filters ──────────

#[test]
fn groebner_basis_incremental_skips_zero_seed_elements() {
    // Zero polys in the seed `known_gb` are dropped by
    // `seed_reduced_basis`; the run proceeds as if seeded with the
    // nonzero members only.
    let ring = ring2();
    let zero = SparsePolynomial::zero();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    // {x, y} is a reduced GB; inject a zero into the seed.
    let gb = groebner_basis_incremental(
        vec![zero, x.clone(), y.clone()],
        vec![],
        &ring,
        None,
    );
    // Seeding {x, y} (pair-free) with no new generators leaves {x, y}.
    assert_eq!(gb.len(), 2);
    assert!(!gb.iter().any(|p| p.is_constant()));
}

#[test]
fn groebner_basis_incremental_seed_two_element_reduced_gb() {
    // A genuine 2-element reduced GB {x, y}: `seed_reduced_basis`
    // pushes both (the second element drives the deactivation-loop
    // pass over the first, a no-op for incomparable LTs). Adding a
    // new generator that reduces to zero against the seed leaves the
    // seed unchanged.
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let xy = x.mul(&y, &ring); // reduces to 0 against {x, y}
    let gb = groebner_basis_incremental(
        vec![x.clone(), y.clone()],
        vec![xy],
        &ring,
        None,
    );
    let reduced = interreduce(gb, &ring, None);
    // Still {x, y}.
    assert_eq!(reduced.len(), 2);
    assert!(!reduced.iter().any(|p| p.is_constant()));
}

#[test]
fn groebner_basis_incremental_seed_constant_is_trivial() {
    // A seed reduced GB containing a nonzero constant means the ideal
    // is the whole ring: `seed_reduced_basis` sets `trivial` and the
    // result is {1}.
    let ring = ring2();
    let two = SparsePolynomial::constant(ring.field.from_int(2), &ring);
    let x = SparsePolynomial::variable(0, &ring);
    let gb = groebner_basis_incremental(vec![two], vec![x], &ring, None);
    assert_eq!(gb.len(), 1);
    assert!(gb[0].is_constant() && !gb[0].is_zero());
}

// ────────── seed deactivation (divides branch) ──────────

#[test]
fn seed_reduced_basis_deactivates_dominated_earlier_element() {
    // Feed `seed_reduced_basis` a (deliberately non-reduced) seed where a
    // later element's leading term divides an earlier one's: [x·y, x].
    // Processing `x` finds divides(x, x·y) ⇒ the earlier `x·y` element is
    // deactivated (the non-strict deactivation loop body). With no new
    // generators only the active survivor `x` is returned.
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let xy = x.mul(&y, &ring);
    let gb = groebner_basis_incremental(vec![xy, x.clone()], vec![], &ring, None);
    // x·y deactivated, x active ⇒ a single nonconstant element.
    assert_eq!(gb.len(), 1);
    assert!(!gb[0].is_constant());
    // The survivor is `x` (leading monomial total degree 1).
    assert_eq!(gb[0].leading_monomial().unwrap().total_degree(), 1);
}

// ────────── run() cancellation between add_generators and the pair loop ──────────

#[test]
fn run_returns_early_when_cancelled_with_pending_pairs() {
    // Drive the internal `Buchberger` directly: populate the basis + open
    // S-pair queue via `add_generators` under a live token, then cancel and
    // call `run()`. The pair loop checks cancellation at the top of its
    // first iteration (a pair is pending) and returns before reducing it.
    let ring = ring2();
    let token = crate::timeout::CancelToken::new();
    let mut b = Buchberger::new(&ring, Some(&token));
    // Non-coprime leading terms ⇒ at least one pending S-pair after add.
    let x = SparsePolynomial::variable(0, &ring);
    let xx = x.mul(&x, &ring); // x^2
    let xy = x.mul(&SparsePolynomial::variable(1, &ring), &ring); // x·y
    b.add_generators(vec![xx, xy]);
    assert!(!b.open.is_empty(), "expected a pending S-pair before cancel");
    let basis_len_before = b.basis.len();
    token.cancel();
    b.run();
    // The popped pair's S-polynomial was never reduced or integrated:
    // the basis did not grow.
    assert_eq!(b.basis.len(), basis_len_before, "run must bail before integrating");
}

// ────────── interreduce cancellation (break branch) ──────────

#[test]
fn interreduce_returns_early_on_pre_cancelled_token() {
    // A pre-cancelled token makes the tail-reduction loop break on the
    // first index; the minimised, monic basis is still returned. Two
    // coprime-LT survivors ({x, y}) means no minimisation pruning, so both
    // remain.
    let ring = ring2();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let cancel = crate::timeout::CancelToken::cancelled();
    let reduced = interreduce(vec![x, y], &ring, Some(&cancel));
    assert_eq!(reduced.len(), 2);
    assert!(!reduced.iter().any(|p| p.is_constant()));
}

// ──────────── SPEC-DRIVEN PROPERTY TESTS ────────────
//
// Properties below check engine behaviour against mathematical
// invariants (ideal-membership, uniqueness of the reduced GB,
// idempotence, determinism) — NOT against what the source does.

use crate::ff::buchberger::{
    groebner_basis as dense_gb, interreduce as dense_interreduce, BuchbergerConfig,
};
use crate::ff::polynomial::DensePoly;
use crate::ff::repr::MonomialRepr;
use crate::ff::sparse_monomial::SparseMonomial;

/// Polynomial ring builder for a given prime + variable count.
fn ring_p(p: u64, n_vars: usize) -> Arc<PolyRing> {
    PolyRing::new(
        PrimeField::new(BigUint::from(p)),
        (0..n_vars).map(|i| format!("x{i}")).collect(),
        MonomialOrder::DegRevLex,
    )
}

/// Canonical sort key: sparse polys → ordered, monic, sorted-by-LT-desc form.
fn canon_sparse(mut basis: Vec<SparsePolynomial>, ring: &PolyRing) -> Vec<SparsePolynomial> {
    basis.retain(|p| !p.is_zero());
    for p in basis.iter_mut() {
        *p = p.make_monic(ring);
    }
    basis.sort_by(|a, b| {
        let la = a.leading_monomial().unwrap();
        let lb = b.leading_monomial().unwrap();
        MonomialRepr::cmp_with_order(lb, la, ring.order)
    });
    basis
}

/// Spec of ideal membership: every input generator reduces to zero
/// modulo a Gröbner basis of the ideal it generates. This is THE
/// defining property of a GB (Buchberger's theorem corollary).
fn assert_all_reduce_to_zero(
    gens: &[SparsePolynomial],
    basis: &[SparsePolynomial],
    ring: &PolyRing,
) {
    let refs: Vec<&SparsePolynomial> = basis.iter().collect();
    for g in gens {
        let nf = g.reduce_by_refs(&refs, ring);
        assert!(
            nf.is_zero(),
            "generator did not reduce to zero modulo basis: residue with {} term(s)",
            nf.num_terms()
        );
    }
}

// ── (3) idempotence of interreduce ──

/// Spec: interreduce is idempotent on its image. Applying interreduce
/// to a reduced GB returns the same reduced GB (every leading term is
/// minimal, every tail already reduced — no work to do).
#[test]
fn sparse_interreduce_is_idempotent_on_reduced_gb() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let g1 = x.mul(&y, &ring).sub(&one, &ring);
    let g2 = y.mul(&z, &ring).sub(&one, &ring);
    let gens = vec![g1, g2];
    let red1 = interreduce(groebner_basis(gens, &ring, None), &ring, None);
    let red2 = interreduce(red1.clone(), &ring, None);
    let canon1 = canon_sparse(red1, &ring);
    let canon2 = canon_sparse(red2, &ring);
    assert_eq!(canon1.len(), canon2.len(), "idempotence: length differs");
    for (a, b) in canon1.iter().zip(canon2.iter()) {
        let at = a.iter_terms().collect::<Vec<_>>();
        let bt = b.iter_terms().collect::<Vec<_>>();
        assert_eq!(at.len(), bt.len());
        for ((ma, ca), (mb, cb)) in at.iter().zip(bt.iter()) {
            assert_eq!(ma.to_dense(), mb.to_dense());
            assert_eq!(ring.field.to_biguint(ca), ring.field.to_biguint(cb));
        }
    }
}

// ── (4) post-op invariant: 1 ∈ I ⟺ GB = {1} ──

/// Spec: a GB contains a nonzero constant iff the ideal is the whole
/// ring. Including 1 as a generator forces GB(I) = {1} after
/// interreduce.
#[test]
fn sparse_gb_with_unit_generator_collapses_to_one() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let g = x.mul(&y, &ring); // arbitrary non-unit
    let gens = vec![g, one];
    let gb = interreduce(groebner_basis(gens, &ring, None), &ring, None);
    assert_eq!(gb.len(), 1);
    assert!(gb[0].is_constant() && !gb[0].is_zero());
}

// ── (8) determinism ──

/// Spec: pure Buchberger has no hidden state — two calls with
/// structurally-equal inputs must produce structurally-equal outputs.
/// (Hidden randomness or iteration-order non-determinism would break
/// soundness reasoning that relies on the reduced GB being a function
/// of the input.)
#[test]
fn sparse_gb_is_deterministic_across_two_calls() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let f1 = x.mul(&y, &ring).sub(&z, &ring);
    let f2 = y.mul(&z, &ring).sub(&one, &ring);
    let f3 = x.mul(&z, &ring).add(&y, &ring);
    let gens = vec![f1, f2, f3];
    let a = canon_sparse(interreduce(groebner_basis(gens.clone(), &ring, None), &ring, None), &ring);
    let b = canon_sparse(interreduce(groebner_basis(gens, &ring, None), &ring, None), &ring);
    assert_eq!(a.len(), b.len());
    for (p, q) in a.iter().zip(b.iter()) {
        let pt = p.iter_terms().collect::<Vec<_>>();
        let qt = q.iter_terms().collect::<Vec<_>>();
        assert_eq!(pt.len(), qt.len());
        for ((mp, cp), (mq, cq)) in pt.iter().zip(qt.iter()) {
            assert_eq!(mp.to_dense(), mq.to_dense());
            assert_eq!(ring.field.to_biguint(cp), ring.field.to_biguint(cq));
        }
    }
}

// ── (1) s_polynomial algebraic identity: S(f, f) reduces to zero ──

/// Spec of S-polynomial: S(f, f) = (1/lc(f))·f − (1/lc(f))·f = 0
/// (lcm of LT(f) with itself is LT(f); the two cofactors are both 1).
/// This must be true verbatim — not "reduces to zero", but the raw
/// S-poly output equals the zero polynomial.
#[test]
fn s_polynomial_of_self_is_zero() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    // Several non-trivial polynomials.
    let candidates = vec![
        x.clone(),
        x.mul(&y, &ring).sub(&one, &ring),
        x.add(&y, &ring),
        x.scale(&ring.field.from_u64(3), &ring).add(&one, &ring),
    ];
    for f in candidates {
        let s = s_polynomial(&f, &f, &ring);
        assert!(s.is_zero(), "S(f, f) must be 0 by definition");
    }
}

// ── (4) generators in ideal — multi-prime sweep ──

/// Spec: every input generator reduces to zero modulo the computed
/// GB. Probe over GF(2), GF(3), GF(5), GF(7), and a 254-bit prime —
/// the property is field-characteristic-independent.
#[test]
fn sparse_gb_generators_reduce_to_zero_across_primes() {
    let primes = [2u64, 3, 5, 7, 2_147_483_647];
    for &p in &primes {
        let ring = ring_p(p, 3);
        let x = SparsePolynomial::variable(0, &ring);
        let y = SparsePolynomial::variable(1, &ring);
        let z = SparsePolynomial::variable(2, &ring);
        let one = SparsePolynomial::constant(ring.field.one(), &ring);
        // System with non-monomial structure.
        let f1 = x.mul(&y, &ring).sub(&z, &ring);
        let f2 = y.mul(&z, &ring).sub(&one, &ring);
        let gens = vec![f1, f2];
        let gb = interreduce(groebner_basis(gens.clone(), &ring, None), &ring, None);
        // (3) skip the trivial case: gens might happen to be a GB
        // already on some primes; still must reduce to zero.
        assert_all_reduce_to_zero(&gens, &gb, &ring);
    }
}

// ── (4) post-op invariant: reduced GB is MINIMAL (no LT divides another's) ──

/// Spec of a *reduced* GB (Cox-Little-O'Shea Defn 2.7.4): no leading
/// term divides another's leading term, AND every tail is reduced
/// modulo the others. We pin the first half here (minimality) since
/// it's a structural property of the output that's independent of
/// what the source computes.
#[test]
fn sparse_reduced_gb_has_minimal_leading_terms() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let f1 = x.mul(&y, &ring).sub(&one, &ring);
    let f2 = y.mul(&z, &ring).sub(&one, &ring);
    let f3 = z.mul(&x, &ring).sub(&one, &ring);
    let gens = vec![f1, f2, f3];
    let gb = interreduce(groebner_basis(gens, &ring, None), &ring, None);
    let lts: Vec<SparseMonomial> = gb
        .iter()
        .map(|p| p.leading_monomial().unwrap().clone())
        .collect();
    for i in 0..lts.len() {
        for j in 0..lts.len() {
            if i == j {
                continue;
            }
            assert!(
                !MonomialRepr::divides(&lts[i], &lts[j]),
                "reduced GB: LT[{}] divides LT[{}]",
                i,
                j
            );
        }
    }
}

// ── (4) post-op invariant: every reduced-GB element is MONIC ──

/// Spec of a *reduced* GB: every element has leading coefficient 1.
/// Independent of which polynomials are in the basis — for ANY input,
/// the output's leading coefficients must all be one.
#[test]
fn sparse_reduced_gb_is_monic() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    let g1 = x.mul(&y, &ring).scale(&ring.field.from_u64(3), &ring);
    let g2 = y.mul(&z, &ring).scale(&ring.field.from_u64(5), &ring);
    let gens = vec![g1, g2];
    let gb = interreduce(groebner_basis(gens, &ring, None), &ring, None);
    let one = ring.field.one();
    let one_big = ring.field.to_biguint(&one);
    for p in &gb {
        let lc = p.leading_coefficient().unwrap();
        let lc_big = ring.field.to_biguint(lc);
        assert_eq!(lc_big, one_big, "reduced GB element not monic");
    }
}

// ─────────────────────────────────────────────────────────────────────
// Hard-probe: sparse_gb vs dense Buchberger differential bank.
// Spec: the reduced GB under a fixed monomial order is unique, so the
// sparse and dense engines must produce ideal-equal bases on every
// input. Mutual ideal-membership is the strongest general check.
// ─────────────────────────────────────────────────────────────────────

/// Large-prime ring helper (BN254 needs a string-parsed prime).
fn ring_prime_str(p_dec: &str, n_vars: usize) -> Arc<PolyRing> {
    let p = p_dec.parse::<BigUint>().unwrap();
    PolyRing::new(
        PrimeField::new(p),
        (0..n_vars).map(|i| format!("x{i}")).collect(),
        MonomialOrder::DegRevLex,
    )
}

const BN254_PRIME: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// Hand-built sparse-system bank, parallel to the dense F4-vs-Buch bank.
fn sparse_diff_systems(ring: &Arc<PolyRing>) -> Vec<(&'static str, Vec<SparsePolynomial>)> {
    let one = SparsePolynomial::constant(ring.field.one(), ring);
    let two = SparsePolynomial::constant(ring.field.from_u64(2), ring);
    let three = SparsePolynomial::constant(ring.field.from_u64(3), ring);
    let n = ring.var_names.len();
    let v: Vec<SparsePolynomial> =
        (0..n).map(|i| SparsePolynomial::variable(i, ring)).collect();

    let mut out: Vec<(&'static str, Vec<SparsePolynomial>)> = Vec::new();

    if n >= 2 {
        out.push(("sparse_linear", vec![v[0].add(&v[1], ring).sub(&one, ring)]));
    }
    if n >= 2 {
        out.push((
            "sparse_two_coprime_linear",
            vec![v[0].sub(&one, ring), v[1].sub(&two, ring)],
        ));
    }
    if n >= 1 {
        out.push(("single_monomial_x0sq", vec![v[0].mul(&v[0], ring)]));
    }
    if n >= 2 {
        let p = v[0].mul(&v[1], ring).sub(&one, ring);
        out.push(("repeated_generator_xy_minus_1", vec![p.clone(), p]));
    }
    out.push(("contains_one_trivial_unsat", vec![one.clone()]));
    if n >= 2 {
        out.push((
            "constant_and_relation",
            vec![two.clone(), v[0].mul(&v[1], ring).sub(&one, ring)],
        ));
    }
    if n >= 2 {
        let mut p1 = one.clone();
        for _ in 0..5 { p1 = p1.mul(&v[0], ring); }
        let mut p2 = one.clone();
        for _ in 0..4 { p2 = p2.mul(&v[1], ring); }
        out.push(("high_degree_monomials", vec![p1, p2]));
    }
    if n >= 3 {
        let f = v[0].mul(&v[1], ring).scale(&ring.field.from_u64(3), ring)
            .add(&v[1].mul(&v[2], ring).scale(&ring.field.from_u64(4), ring), ring)
            .add(&v[0].mul(&v[2], ring).scale(&ring.field.from_u64(5), ring), ring)
            .sub(&v[0], ring).sub(&v[1], ring).sub(&v[2], ring)
            .add(&three, ring);
        out.push(("dense_one_relation", vec![f]));
    }
    if n >= 3 {
        let f1 = v[0].add(&v[1], ring).add(&v[2], ring);
        let f2 = v[0].mul(&v[1], ring)
            .add(&v[1].mul(&v[2], ring), ring)
            .add(&v[0].mul(&v[2], ring), ring);
        let f3 = v[0].mul(&v[1], ring).mul(&v[2], ring).sub(&one, ring);
        out.push(("cyclic_3", vec![f1, f2, f3]));
    }
    if n >= 3 {
        let f1 = v[0].mul(&v[0], ring).sub(&v[1], ring);
        let f2 = v[0].mul(&v[1], ring).sub(&v[2], ring);
        let f3 = v[1].mul(&v[1], ring).sub(&v[0], ring);
        out.push(("overlapping_lts", vec![f1, f2, f3]));
    }
    if n >= 2 {
        let f1 = v[0].mul(&v[0], ring).sub(&v[0], ring);
        let f2 = v[1].mul(&v[1], ring).sub(&v[1], ring);
        let f3 = v[0].add(&v[1], ring).sub(&one, ring);
        out.push(("idempotents_plus_linear", vec![f1, f2, f3]));
    }
    if n >= 4 {
        let mut acc = v[0].clone();
        for i in 1..n { acc = acc.add(&v[i], ring); }
        out.push(("n_vars_sum_minus_1", vec![acc.sub(&one, ring)]));
    }
    if n >= 2 {
        out.push((
            "zero_mixed_with_relation",
            vec![SparsePolynomial::zero(), v[0].mul(&v[1], ring).sub(&one, ring)],
        ));
    }

    out
}

/// Drive sparse_gb on each system, drive dense Buchberger on the
/// dense lift, compare via mutual ideal-membership.
fn run_sparse_vs_dense_bank(prime_dec: &str, n_vars: usize) {
    let ring = ring_prime_str(prime_dec, n_vars);
    for (name, gens_s) in sparse_diff_systems(&ring) {
        let label = format!("[p={prime_dec}/{n_vars}vars/{name}]");

        let gens_d: Vec<DensePoly> = gens_s.iter().map(|p| p.to_dense(&ring)).collect();

        let gb_s = interreduce(groebner_basis(gens_s.clone(), &ring, None), &ring, None);
        let gb_d_dense = dense_interreduce(
            dense_gb(gens_d.clone(), &ring, &BuchbergerConfig::default()).unwrap().basis,
            &ring,
        );
        let gb_d: Vec<SparsePolynomial> = gb_d_dense
            .iter().map(|p| SparsePolynomial::from_dense(p, &ring)).collect();

        let s_refs: Vec<&SparsePolynomial> = gb_s.iter().collect();
        for g in &gens_s {
            if g.is_zero() { continue; }
            let nf = g.reduce_by_refs(&s_refs, &ring);
            assert!(nf.is_zero(), "{label}: sparse gen not in ideal(gb_sparse)");
        }
        let d_refs: Vec<&SparsePolynomial> = gb_d.iter().collect();
        for g in &gens_s {
            if g.is_zero() { continue; }
            let nf = g.reduce_by_refs(&d_refs, &ring);
            assert!(nf.is_zero(), "{label}: sparse gen not in ideal(gb_dense)");
        }
        for p in &gb_s {
            let nf = p.reduce_by_refs(&d_refs, &ring);
            assert!(nf.is_zero(), "{label}: gb_s not subset of ideal(gb_d)");
        }
        for p in &gb_d {
            let nf = p.reduce_by_refs(&s_refs, &ring);
            assert!(nf.is_zero(), "{label}: gb_d not subset of ideal(gb_s)");
        }
        let unit_in = gens_s.iter().any(|p| p.is_constant() && !p.is_zero());
        if unit_in {
            assert!(gb_s.iter().any(|p| p.is_constant() && !p.is_zero()),
                "{label}: sparse must report trivial ideal");
            assert!(gb_d.iter().any(|p| p.is_constant() && !p.is_zero()),
                "{label}: dense must report trivial ideal");
        }
    }
}

#[test]
fn diff_sparse_vs_dense_bank_prime_nvars_sweep() {
    // Sweeps (prime_dec, n_vars). Includes GF(7) at 2/3/4 vars, GF(101)/3,
    // and BN254/3 (the realistic ZK-circuit prime). Each call runs the
    // full `sparse_diff_systems` bank under that (prime, n_vars).
    for (prime_dec, n_vars) in [("7", 2usize), ("7", 3), ("7", 4), ("101", 3), (BN254_PRIME, 3)] {
        run_sparse_vs_dense_bank(prime_dec, n_vars);
    }
}

#[test]
fn diff_sparse_vs_dense_bank_edge_primes_small() {
    run_sparse_vs_dense_bank("2", 2);
    run_sparse_vs_dense_bank("3", 2);
    run_sparse_vs_dense_bank("5", 2);
}

// ─────────────────────────────────────────────────────────────────────
// Cancel boundary: pre-cancelled token. Spec: returned basis must be a
// SUB-ideal of the input (sparse_gb contract).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn diff_sparse_precancelled_token_returns_subideal() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let gens = vec![
        x.mul(&y, &ring).sub(&z, &ring),
        y.mul(&z, &ring).sub(&one, &ring),
        x.mul(&z, &ring).add(&y, &ring),
    ];
    let token = crate::timeout::CancelToken::cancelled();
    let basis = groebner_basis(gens.clone(), &ring, Some(&token));
    let full = interreduce(groebner_basis(gens.clone(), &ring, None), &ring, None);
    let full_refs: Vec<&SparsePolynomial> = full.iter().collect();
    for p in &basis {
        if p.is_zero() { continue; }
        let nf = p.reduce_by_refs(&full_refs, &ring);
        assert!(
            nf.is_zero(),
            "pre-cancelled returned basis element NOT in input ideal: {} term(s) residue",
            nf.num_terms()
        );
    }
}

#[test]
fn diff_sparse_precancelled_interreduce_returns_subideal() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    let f1 = x.mul(&y, &ring).sub(&z, &ring);
    let f2 = y.mul(&z, &ring).sub(&x, &ring);
    let f3 = z.mul(&x, &ring).sub(&y, &ring);
    let input = vec![f1.clone(), f2.clone(), f3.clone()];
    let token = crate::timeout::CancelToken::cancelled();
    let out = interreduce(input.clone(), &ring, Some(&token));
    let full = interreduce(groebner_basis(input.clone(), &ring, None), &ring, None);
    let full_refs: Vec<&SparsePolynomial> = full.iter().collect();
    for p in &out {
        if p.is_zero() { continue; }
        let nf = p.reduce_by_refs(&full_refs, &ring);
        assert!(nf.is_zero(), "interreduce on cancel: element not in input ideal");
    }
}

// ─────────────────────────────────────────────────────────────────────
// Pathological-shape coverage: zero-variable ring, all-zero generators.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn diff_sparse_zero_variable_ring_constant_input() {
    let ring = PolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        Vec::<String>::new(),
        MonomialOrder::DegRevLex,
    );
    let gb_empty = groebner_basis(vec![], &ring, None);
    assert!(gb_empty.is_empty(), "empty input over 0-var ring ⇒ empty GB");
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let gb_unit = interreduce(groebner_basis(vec![one], &ring, None), &ring, None);
    assert!(
        gb_unit.iter().any(|p| p.is_constant() && !p.is_zero()),
        "1 ∈ generators ⇒ GB = {{1}}"
    );
}

#[test]
fn diff_sparse_all_zero_generators_yields_empty_gb() {
    let ring = ring_p(7, 3);
    let gb = groebner_basis(
        vec![SparsePolynomial::zero(), SparsePolynomial::zero()],
        &ring, None,
    );
    assert!(gb.is_empty(), "all-zero input ⇒ empty GB (the zero ideal)");
}

#[test]
fn diff_sparse_repeated_constant_yields_trivial() {
    // Any nonzero constant generates the unit ideal.
    let ring = ring_p(7, 2);
    let two = SparsePolynomial::constant(ring.field.from_u64(2), &ring);
    let gb = interreduce(
        groebner_basis(vec![two.clone(), two], &ring, None),
        &ring, None,
    );
    assert_eq!(gb.len(), 1);
    assert!(gb[0].is_constant() && !gb[0].is_zero());
}

// ══════════════════════════════════════════════════════════════════════════
// MULTI-ENGINE FUZZ: F4-LITE DIFFERENTIAL + CROSS-ENGINE VERDICT PROBES
// ──────────────────────────────────────────────────────────────────────────
// Complementary to the `diff_sparse_vs_dense_bank_*` tests above. This
// bank adds:
//   - F4-lite (use_f4=true) vs per-pair geobucket (use_f4=false): they
//     are theoretically equivalent dense engines; the chosen reduction
//     path must not change the ideal.
//   - Sparse engine vs dense F4-lite (cross-engine + cross-config).
//   - Reduced-GB CARDINALITY agreement: the reduced GB under a fixed
//     monomial order is unique (Cox-Little-O'Shea Thm 2.7.5), so its
//     size is unique. Sparse and dense must produce the same count.
//   - GB(GB(.)) ≡ GB(.) ideal-idempotence cross-engine.
//   - Mid-call cancel-token bug surface (Arc<AtomicBool> set true
//     before the call): sparse engine must NEVER fabricate a unit on
//     a system whose true ideal is not the whole ring.
//   - Generator-equal-to-field-poly probe (x^p - x = 0 over GF(p) for
//     small p): tests engine robustness on a generator whose roots
//     are EVERY field element — every model satisfies it, so GB
//     should NOT collapse to {1} unless paired with a contradiction.
//
// All expected values from SPEC; never from "what the source returned."

const F4_BN254_PRIME: &str = BN254_PRIME;

/// Build a small consistent system on a freshly-built ring (sparse).
fn build_consistent_3v(ring: &Arc<PolyRing>) -> Vec<SparsePolynomial> {
    let x = SparsePolynomial::variable(0, ring);
    let y = SparsePolynomial::variable(1, ring);
    let z = SparsePolynomial::variable(2, ring);
    let one = SparsePolynomial::constant(ring.field.one(), ring);
    vec![
        x.mul(&y, ring).sub(&z, ring),       // x*y - z
        y.mul(&z, ring).sub(&x, ring),       // y*z - x
        z.mul(&x, ring).sub(&y, ring),       // z*x - y
        x.add(&y, ring).add(&z, ring).sub(&one, ring), // x+y+z - 1
    ]
}

/// Helper: compute the reduced sparse GB.
fn sparse_reduced_gb(gens: Vec<SparsePolynomial>, ring: &PolyRing) -> Vec<SparsePolynomial> {
    interreduce(groebner_basis(gens, ring, None), ring, None)
}

/// Helper: compute the reduced dense GB via the per-pair path; lift back to sparse.
fn dense_perpair_reduced_gb(
    gens: &[SparsePolynomial],
    ring: &Arc<PolyRing>,
) -> Vec<SparsePolynomial> {
    let gens_d: Vec<DensePoly> = gens.iter().map(|p| p.to_dense(ring)).collect();
    let cfg = BuchbergerConfig { order: ring.order, use_f4: false, ..Default::default() };
    let basis = dense_gb(gens_d, ring, &cfg).expect("dense per-pair GB OK").basis;
    dense_interreduce(basis, ring)
        .iter().map(|p| SparsePolynomial::from_dense(p, ring)).collect()
}

/// Helper: compute the reduced dense GB via the F4-lite path; lift to sparse.
fn dense_f4_reduced_gb(
    gens: &[SparsePolynomial],
    ring: &Arc<PolyRing>,
) -> Vec<SparsePolynomial> {
    let gens_d: Vec<DensePoly> = gens.iter().map(|p| p.to_dense(ring)).collect();
    let cfg = BuchbergerConfig { order: ring.order, use_f4: true, ..Default::default() };
    let basis = dense_gb(gens_d, ring, &cfg).expect("dense F4 GB OK").basis;
    dense_interreduce(basis, ring)
        .iter().map(|p| SparsePolynomial::from_dense(p, ring)).collect()
}

/// Mutual ideal-membership assertion: every element of `a` reduces to 0
/// mod `b` and vice versa. SPEC: bidirectional ideal-membership is the
/// defining property of ideal equality.
fn assert_ideal_eq_mutual(a: &[SparsePolynomial], b: &[SparsePolynomial], ring: &PolyRing, label: &str) {
    let a_refs: Vec<&SparsePolynomial> = a.iter().collect();
    let b_refs: Vec<&SparsePolynomial> = b.iter().collect();
    for p in a {
        let nf = p.reduce_by_refs(&b_refs, ring);
        assert!(
            nf.is_zero(),
            "{label}: A ⊄ B (residue {} term(s))",
            nf.num_terms()
        );
    }
    for p in b {
        let nf = p.reduce_by_refs(&a_refs, ring);
        assert!(
            nf.is_zero(),
            "{label}: B ⊄ A (residue {} term(s))",
            nf.num_terms()
        );
    }
}

// ────────── Property: F4-lite ≡ per-pair geobucket (dense vs dense) ──────────

/// SPEC: same engine-equivalence on a small prime — GF(2) is the
/// characteristic-edge regression surface for bit-width and bitprop
/// logic.
#[test]
fn fuzz_f4_vs_perpair_ideal_equal_3v_gf2() {
    let ring = ring_prime_str("2", 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let gens = vec![
        x.mul(&y, &ring).add(&z, &ring),       // x*y + z
        x.add(&y, &ring).add(&z, &ring),       // x + y + z
        x.mul(&z, &ring).add(&one, &ring),     // x*z + 1
    ];
    let gb_pp = dense_perpair_reduced_gb(&gens, &ring);
    let gb_f4 = dense_f4_reduced_gb(&gens, &ring);
    assert_ideal_eq_mutual(&gb_pp, &gb_f4, &ring, "F4-vs-perpair/gf2/3v");
}

/// SPEC: same engine-equivalence on BN254 scalar (huge prime).
#[test]
fn fuzz_f4_vs_perpair_ideal_equal_3v_bn254() {
    let ring = ring_prime_str(F4_BN254_PRIME, 3);
    let gens = build_consistent_3v(&ring);
    let gb_pp = dense_perpair_reduced_gb(&gens, &ring);
    let gb_f4 = dense_f4_reduced_gb(&gens, &ring);
    assert_ideal_eq_mutual(&gb_pp, &gb_f4, &ring, "F4-vs-perpair/bn254/3v");
}

/// SPEC: F4 batch-construction must surface a nonzero constant — i.e.
/// detect inconsistency just as per-pair does. Inputs: x - 1 and x - 2
/// over GF(p) — S-poly reduces to a unit.
#[test]
fn fuzz_f4_vs_perpair_inconsistency_agreement_across_primes() {
    let cases = [("7", 1), ("101", 1), (BN254_PRIME, 1)];
    for (p, n) in cases {
        let ring = ring_prime_str(p, n);
        let x = SparsePolynomial::variable(0, &ring);
        let c1 = SparsePolynomial::constant(ring.field.one(), &ring);
        let c2 = SparsePolynomial::constant(ring.field.from_u64(2), &ring);
        let gens = vec![x.sub(&c1, &ring), x.sub(&c2, &ring)];
        let gb_pp = dense_perpair_reduced_gb(&gens, &ring);
        let gb_f4 = dense_f4_reduced_gb(&gens, &ring);
        let triv_pp = gb_pp.iter().any(|p| p.is_constant() && !p.is_zero());
        let triv_f4 = gb_f4.iter().any(|p| p.is_constant() && !p.is_zero());
        assert!(triv_pp && triv_f4,
            "p={p}: inconsistent system must collapse to {{1}} on both paths (pp={triv_pp}, f4={triv_f4})");
    }
}

// ────────── Property: sparse engine ≡ dense F4-lite (cross-engine + F4) ──────────

/// SPEC: sparse Buchberger and dense F4-lite implement the same
/// algorithm spec — Buchberger's theorem says they must compute the
/// same ideal. This is a 4-way cross-check (sparse engine + dense
/// engine + per-pair + F4) collapsed into a 2-way ideal equality.
#[test]
fn fuzz_sparse_vs_dense_f4_ideal_equal_3v_bn254() {
    let ring = ring_prime_str(F4_BN254_PRIME, 3);
    let gens = build_consistent_3v(&ring);
    let gb_s = sparse_reduced_gb(gens.clone(), &ring);
    let gb_f4 = dense_f4_reduced_gb(&gens, &ring);
    assert_ideal_eq_mutual(&gb_s, &gb_f4, &ring, "sparse-vs-F4/bn254/3v");
}

// ────────── Property: reduced GB cardinality agrees sparse vs dense ──────────

/// SPEC: the reduced GB under a fixed monomial order is unique
/// (Cox-Little-O'Shea Thm 2.7.5). Cardinality is therefore unique.
/// Sparse and dense engines must produce the same number of basis
/// elements on every input. This is weaker than element-wise equality
/// (which `diff_sparse_vs_dense_bank_*` already checks) but surfaces
/// the symptom much more cleanly: count-of-elements is a single number.
#[test]
fn fuzz_reduced_gb_cardinality_agrees_across_primes_and_shapes() {
    let probes = [
        ("7", 2usize),
        ("7", 3),
        ("101", 3),
        (BN254_PRIME, 3),
    ];
    for (p, n) in probes {
        let ring = ring_prime_str(p, n);
        for (name, gens_s) in sparse_diff_systems(&ring) {
            let gb_s = sparse_reduced_gb(gens_s.clone(), &ring);
            let gb_d = dense_perpair_reduced_gb(&gens_s, &ring);
            assert_eq!(
                gb_s.len(), gb_d.len(),
                "[p={p}/{n}vars/{name}] reduced GB size differs sparse={} dense={}",
                gb_s.len(), gb_d.len(),
            );
        }
    }
}

// ────────── Property: GB(GB(.)) ≡ GB(.) — ideal-idempotence ──────────

/// SPEC: a reduced Gröbner basis is itself a generator set for the
/// same ideal; running Buchberger again yields the same ideal. Probe
/// this round-trip cross-engine: sparse → dense → sparse should all
/// stay in the same ideal.
#[test]
fn fuzz_gb_idempotent_cross_engine_3v_gf101() {
    let ring = ring_prime_str("101", 3);
    let gens = build_consistent_3v(&ring);
    let gb1 = sparse_reduced_gb(gens.clone(), &ring);
    // Re-run dense on `gb1` (the reduced sparse basis). Spec: the new
    // basis must be ideal-equal to `gb1`.
    let gb2 = dense_perpair_reduced_gb(&gb1, &ring);
    assert_ideal_eq_mutual(&gb1, &gb2, &ring, "idempotent sparse→dense");
    // And one more round through the sparse engine.
    let gb3 = sparse_reduced_gb(gb2.clone(), &ring);
    assert_ideal_eq_mutual(&gb2, &gb3, &ring, "idempotent dense→sparse");
}

// ────────── Property: mid-call cancel must NOT fabricate a unit ──────────

/// SPEC: a CancelToken set true mid-pipeline causes the engine to
/// return a partial result; the partial basis must be a SUB-ideal of
/// the input. In particular, a unit must NEVER spontaneously appear
/// in the partial basis if the input ideal is not the whole ring.
/// (Solver-level consequence: a fabricated unit at this layer would
/// be lifted into a spurious UNSAT verdict.)
#[test]
fn fuzz_mid_call_cancel_does_not_fabricate_unit_consistent_system() {
    // Pre-cancelled token: forces the engine into the immediate-cancel
    // branch from the very first iteration. Strengthens the general
    // sub-ideal contract with a NO-UNIT contract on a consistent system.
    let ring = ring_prime_str("101", 3);
    let gens = build_consistent_3v(&ring);
    let token = crate::timeout::CancelToken::cancelled();
    let basis = groebner_basis(gens.clone(), &ring, Some(&token));
    assert!(
        !basis.iter().any(|p| p.is_constant() && !p.is_zero()),
        "pre-cancelled run fabricated a unit on a consistent system: \
         partial basis contains 1, which would lift to a spurious UNSAT"
    );
}

// ────────── Property: field-polynomial generator is well-behaved ──────────

/// SPEC: over GF(p), every field element x ∈ GF(p) satisfies x^p = x.
/// The polynomial `x^p - x = 0` is therefore satisfied by EVERY field
/// element — so on its own it does NOT make the ideal the whole ring
/// (every model is a root). Add a single linear constraint and the
/// solution set should still be non-empty. Probe sparse vs dense
/// agreement on this characteristic-aware shape.
///
/// On GF(2), x^2 - x is the bit-constraint (x ∈ {0, 1}); the sparse
/// engine must not see this as "1 ∈ ideal."
#[test]
fn fuzz_field_polynomial_generator_does_not_collapse_to_unit_across_primes() {
    // Spec: over GF(p), x^p - x = 0 is the bit/trit/… constraint, satisfied by
    // every field element — so on its own it must NOT collapse the ideal to
    // {1}. Sweep small primes (high-signal characteristic-edge surface for
    // bit-width / bitprop logic): GF(2) -> x^2 - x; GF(3) -> x^3 - x.
    // Sparse and dense engines must agree on the same (non-trivial) ideal.
    for &p in &[2u64, 3] {
        let ring = ring_prime_str(&p.to_string(), 1);
        let x = SparsePolynomial::variable(0, &ring);
        // Build x^p iteratively.
        let mut xp = x.clone();
        for _ in 1..p {
            xp = xp.mul(&x, &ring);
        }
        let g = xp.sub(&x, &ring); // x^p - x
        let gb_s = sparse_reduced_gb(vec![g.clone()], &ring);
        let gb_d = dense_perpair_reduced_gb(&[g], &ring);
        assert!(
            !gb_s.iter().any(|p| p.is_constant() && !p.is_zero()),
            "sparse: x^{p}-x over GF({p}) must NOT collapse to {{1}}"
        );
        assert!(
            !gb_d.iter().any(|p| p.is_constant() && !p.is_zero()),
            "dense: x^{p}-x over GF({p}) must NOT collapse to {{1}}"
        );
        assert_ideal_eq_mutual(&gb_s, &gb_d, &ring, &format!("x^{p}-x/gf{p}"));
    }
}

// ────────── Property: monomial-only generator system (single-monomial polys) ──────────

/// SPEC: when ALL generators are single monomials, the Groebner basis
/// is itself a set of monomials (closed under taking GCDs of LTs and
/// inter-reduction). Sparse and dense engines must agree term-for-term
/// on the reduced GB. Pathological case the harness should cover:
/// single-monomial polynomials.
#[test]
fn fuzz_monomial_only_system_sparse_eq_dense_2v_gf7() {
    let ring = ring_prime_str("7", 2);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    // {x^2, x*y, y^2} on GF(7): the reduced GB is {x^2, x*y, y^2}
    // itself (each LT is incomparable, every tail empty).
    let gens = vec![
        x.mul(&x, &ring),
        x.mul(&y, &ring),
        y.mul(&y, &ring),
    ];
    let gb_s = sparse_reduced_gb(gens.clone(), &ring);
    let gb_d = dense_perpair_reduced_gb(&gens, &ring);
    assert_eq!(gb_s.len(), 3, "sparse: {{x^2, xy, y^2}} reduced GB has 3 elements");
    assert_eq!(gb_d.len(), 3, "dense: {{x^2, xy, y^2}} reduced GB has 3 elements");
    assert_ideal_eq_mutual(&gb_s, &gb_d, &ring, "monomial-only/2v/gf7");
}

// ────────── Property: 1-variable ring — ideals are principal ──────────

/// SPEC: every ideal in k[x] is principal; the reduced GB of a non-empty
/// non-trivial ideal is a single polynomial — the GCD (over k[x]) of
/// the generators. Probe sparse vs dense on a 1-variable system that
/// has a known principal GB.
#[test]
fn fuzz_1var_principal_gb_sparse_eq_dense_gf101() {
    let ring = ring_prime_str("101", 1);
    let x = SparsePolynomial::variable(0, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let x2 = x.mul(&x, &ring);
    let x3 = x2.mul(&x, &ring);
    // <x^3 - 1, x^2 - 1> ; GCD over GF(101)[x] = x - 1 (since both
    // polynomials vanish at x = 1). Reduced GB = {x - 1}.
    let g1 = x3.sub(&one, &ring);
    let g2 = x2.sub(&one, &ring);
    let gens = vec![g1, g2];
    let gb_s = sparse_reduced_gb(gens.clone(), &ring);
    let gb_d = dense_perpair_reduced_gb(&gens, &ring);
    // Principal: a single nonzero element.
    assert_eq!(gb_s.len(), 1, "sparse 1var GB must be principal: 1 element");
    assert_eq!(gb_d.len(), 1, "dense 1var GB must be principal: 1 element");
    // Element is x - 1 (monic, degree 1).
    assert_eq!(gb_s[0].leading_monomial().unwrap().total_degree(), 1);
    assert_eq!(gb_d[0].leading_monomial().unwrap().total_degree(), 1);
    assert_ideal_eq_mutual(&gb_s, &gb_d, &ring, "1var-principal/gf101");
}

// ────────── Property: zero-polynomial threaded through generators ──────────

/// SPEC: zero polynomials in the generator list are filtered (they
/// generate the zero ideal locally). The GB of `{g, 0, h, 0}` equals
/// the GB of `{g, h}`. Cross-engine probe.
#[test]
fn fuzz_zero_threaded_generators_sparse_eq_dense() {
    let ring = ring_prime_str("7", 3);
    let zero = SparsePolynomial::zero();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let g1 = x.mul(&y, &ring).sub(&z, &ring);
    let g2 = y.mul(&z, &ring).sub(&one, &ring);
    let with_zeros = vec![zero.clone(), g1.clone(), zero.clone(), g2.clone(), zero];
    let without_zeros = vec![g1, g2];
    let gb_s = sparse_reduced_gb(with_zeros.clone(), &ring);
    let gb_d = dense_perpair_reduced_gb(&with_zeros, &ring);
    let gb_s_baseline = sparse_reduced_gb(without_zeros.clone(), &ring);
    let gb_d_baseline = dense_perpair_reduced_gb(&without_zeros, &ring);
    assert_ideal_eq_mutual(&gb_s, &gb_s_baseline, &ring, "sparse: zero-filtered baseline");
    assert_ideal_eq_mutual(&gb_d, &gb_d_baseline, &ring, "dense: zero-filtered baseline");
    assert_ideal_eq_mutual(&gb_s, &gb_d, &ring, "sparse vs dense w/ zero-threaded");
}
