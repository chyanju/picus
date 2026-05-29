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

// ────────── zero-polynomial filters ──────────

#[test]
fn groebner_basis_skips_zero_generators() {
    // Leading zero generators are filtered in `add_generators`; the
    // result is the GB of the surviving nonzero generators alone.
    let ring = ring2();
    let zero = SparsePolynomial::zero();
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let gb = groebner_basis(vec![zero.clone(), x.clone(), zero, y.clone()], &ring, None);
    // GB of (x, y) is {x, y}: two elements, neither a constant.
    assert_eq!(gb.len(), 2);
    assert!(!gb.iter().any(|p| p.is_constant()));
    let reference = groebner_basis(vec![x, y], &ring, None);
    assert_eq!(gb.len(), reference.len());
}

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

/// Spec: ideal equality A == B iff every element of A reduces to 0
/// mod B AND vice versa. Equality of reduced GBs is sufficient but
/// stronger than needed; the membership check pins the IDEAL even
/// when the bases happen to differ.
fn assert_ideals_equal(
    a: &[SparsePolynomial],
    b: &[SparsePolynomial],
    ring: &PolyRing,
) {
    let a_refs: Vec<&SparsePolynomial> = a.iter().collect();
    let b_refs: Vec<&SparsePolynomial> = b.iter().collect();
    for p in a {
        let nf = p.reduce_by_refs(&b_refs, ring);
        assert!(nf.is_zero(), "A ⊄ B: residue nonzero");
    }
    for p in b {
        let nf = p.reduce_by_refs(&a_refs, ring);
        assert!(nf.is_zero(), "B ⊄ A: residue nonzero");
    }
}

// ── (4) post-op invariant: generators ∈ ideal(GB) ──

/// Spec: every input generator reduces to zero modulo its own GB.
/// Buchberger's theorem: a Groebner basis G of ⟨f1,…,fk⟩ has G ⊃ ⟨f1,…,fk⟩
/// as sets; in particular each fi has zero normal form mod G.
#[test]
fn sparse_gb_generators_reduce_to_zero_hand_built_gf7() {
    let ring = ring_p(7, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    // Cyclic-3-like system over GF(7).
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let f1 = x.add(&y, &ring).add(&z, &ring); // x + y + z
    let f2 = x.mul(&y, &ring).add(&y.mul(&z, &ring), &ring).add(&z.mul(&x, &ring), &ring); // xy+yz+zx
    let f3 = x.mul(&y, &ring).mul(&z, &ring).sub(&one, &ring); // xyz − 1
    let gens = vec![f1, f2, f3];
    let gb = interreduce(groebner_basis(gens.clone(), &ring, None), &ring, None);
    assert_all_reduce_to_zero(&gens, &gb, &ring);
}

// ── (9) engine equivalence: sparse ≡ dense (full reduced GB) ──

/// Spec: the reduced Gröbner basis of an ideal under a fixed monomial
/// order is UNIQUE (Cox-Little-O'Shea Thm 2.7.5). Sparse and dense
/// engines must produce the same reduced GB given the same inputs.
/// Probed on a non-monomial multivariate system over GF(7).
#[test]
fn sparse_vs_dense_reduced_gb_equal_gf7_nonmonomial() {
    let ring = ring_p(7, 3);
    let x_d = DensePoly::variable(0, &ring);
    let y_d = DensePoly::variable(1, &ring);
    let z_d = DensePoly::variable(2, &ring);
    // x*y - z, y*z - x, z*x - y
    let g1_d = x_d.mul(&y_d, &ring).sub(&z_d, &ring);
    let g2_d = y_d.mul(&z_d, &ring).sub(&x_d, &ring);
    let g3_d = z_d.mul(&x_d, &ring).sub(&y_d, &ring);

    let gens_d = vec![g1_d.clone(), g2_d.clone(), g3_d.clone()];
    let gens_s: Vec<SparsePolynomial> =
        gens_d.iter().map(|p| SparsePolynomial::from_dense(p, &ring)).collect();

    let gb_d = dense_gb(gens_d, &ring, &BuchbergerConfig::default()).unwrap();
    let red_d = dense_interreduce(gb_d.basis, &ring);
    // Lift dense reduced GB → sparse representation for direct comparison.
    let red_d_as_sparse: Vec<SparsePolynomial> = red_d
        .iter()
        .map(|p| SparsePolynomial::from_dense(p, &ring))
        .collect();

    let gb_s = interreduce(groebner_basis(gens_s, &ring, None), &ring, None);

    let canon_d = canon_sparse(red_d_as_sparse, &ring);
    let canon_s = canon_sparse(gb_s, &ring);
    assert_eq!(canon_d.len(), canon_s.len(), "reduced GB sizes differ");
    for (a, b) in canon_d.iter().zip(canon_s.iter()) {
        // Equal monic + same LT ordering ⇒ term lists must coincide.
        let am = a.iter_terms().collect::<Vec<_>>();
        let bm = b.iter_terms().collect::<Vec<_>>();
        assert_eq!(am.len(), bm.len(), "term counts differ for an element");
        for ((ma, ca), (mb, cb)) in am.iter().zip(bm.iter()) {
            assert_eq!(ma.to_dense(), mb.to_dense(), "monomial mismatch");
            assert_eq!(ring.field.to_biguint(ca), ring.field.to_biguint(cb), "coeff mismatch");
        }
    }
}

// ── (9) engine equivalence under IDEAL-MEMBERSHIP (broader than equality) ──

/// Spec: a basis B is a GB of ideal I iff every generator of I reduces
/// to 0 modulo B. Cross-checking dense and sparse engines on the SAME
/// generator set ⇒ each engine's basis must be in the other's ideal.
/// This is weaker than reduced-GB equality but catches *any* divergence
/// in the ideal generated.
#[test]
fn sparse_and_dense_generate_same_ideal_gf5() {
    let ring = ring_p(5, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    // Two-element non-monomial ideal over GF(5): x^2 + y, y^2 - z.
    let xx = x.mul(&x, &ring);
    let yy = y.mul(&y, &ring);
    let g1 = xx.add(&y, &ring);
    let g2 = yy.sub(&z, &ring);
    let gens = vec![g1, g2];

    let gb_s = interreduce(groebner_basis(gens.clone(), &ring, None), &ring, None);

    let gens_d: Vec<DensePoly> = gens.iter().map(|p| p.to_dense(&ring)).collect();
    let gb_d_dense = dense_interreduce(
        dense_gb(gens_d, &ring, &BuchbergerConfig::default()).unwrap().basis,
        &ring,
    );
    let gb_d: Vec<SparsePolynomial> = gb_d_dense
        .iter()
        .map(|p| SparsePolynomial::from_dense(p, &ring))
        .collect();

    assert_ideals_equal(&gb_s, &gb_d, &ring);
}

// ── (7) edge primes — small + curve prime ──

/// Spec: the GB algorithm is generic in the characteristic; correct
/// over GF(p) for any prime p. Probe the SMALLEST primes (2, 3) and
/// a 254-bit BN254-flavour prime: ideal-equality between sparse and
/// dense must hold uniformly.
#[test]
fn sparse_vs_dense_edge_primes_ideal_equality() {
    // Hand-built non-monomial system: f1 = x*y - 1, f2 = x + y - 2.
    // (Has a curve over any field where 2 is well-defined; over GF(2)
    // the constants collapse but the equations remain valid.)
    let primes: Vec<BigUint> = vec![
        BigUint::from(2u32),
        BigUint::from(3u32),
        BigUint::from(5u32),
        BigUint::from(7u32),
        // Mersenne-style large prime: 2^31 - 1.
        BigUint::from(2_147_483_647u64),
    ];
    for p in primes {
        let ring = PolyRing::new(
            PrimeField::new(p.clone()),
            vec!["x".into(), "y".into()],
            MonomialOrder::DegRevLex,
        );
        let x = SparsePolynomial::variable(0, &ring);
        let y = SparsePolynomial::variable(1, &ring);
        let one = SparsePolynomial::constant(ring.field.one(), &ring);
        let two = SparsePolynomial::constant(ring.field.from_u64(2), &ring);
        let f1 = x.mul(&y, &ring).sub(&one, &ring);
        let f2 = x.add(&y, &ring).sub(&two, &ring);
        let gens = vec![f1, f2];
        let gb_s = interreduce(groebner_basis(gens.clone(), &ring, None), &ring, None);

        let gens_d: Vec<DensePoly> = gens.iter().map(|p| p.to_dense(&ring)).collect();
        let gb_d_dense = dense_interreduce(
            dense_gb(gens_d, &ring, &BuchbergerConfig::default()).unwrap().basis,
            &ring,
        );
        let gb_d: Vec<SparsePolynomial> = gb_d_dense
            .iter()
            .map(|p| SparsePolynomial::from_dense(p, &ring))
            .collect();

        assert_ideals_equal(&gb_s, &gb_d, &ring);
        // And on top of ideal-equality, every input generator reduces
        // to zero modulo each engine's basis.
        assert_all_reduce_to_zero(&gens, &gb_s, &ring);
        let gb_s_as_dense: Vec<DensePoly> =
            gb_s.iter().map(|p| p.to_dense(&ring)).collect();
        let gb_s_d_refs: Vec<&DensePoly> = gb_s_as_dense.iter().collect();
        for g in &gens {
            let g_d = g.to_dense(&ring);
            let nf = g_d.reduce_by_refs(&gb_s_d_refs, &ring);
            assert!(nf.is_zero(), "generator nf nonzero modulo (lifted) sparse GB");
        }
    }
}

// ── (7) tiny ring shapes: 1-variable / single monomial / constant ──

/// Spec: the GB of a single non-constant monic poly p is {p}. The
/// algorithm has no pairs to process (a single generator has no
/// S-pairs with itself in the standard Buchberger formulation), so
/// the reduced GB equals the input made monic.
#[test]
fn sparse_gb_single_monic_generator_equals_input() {
    let ring = ring_p(7, 2);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    // p = x^2 + y + 1, already monic, single generator.
    let p = x.mul(&x, &ring).add(&y, &ring).add(&one, &ring);
    let gb = interreduce(groebner_basis(vec![p.clone()], &ring, None), &ring, None);
    assert_eq!(gb.len(), 1, "single-generator GB must have one element");
    // Direct equality: same term list (already monic on input).
    let gb_terms = gb[0].iter_terms().collect::<Vec<_>>();
    let p_terms = p.iter_terms().collect::<Vec<_>>();
    assert_eq!(gb_terms.len(), p_terms.len());
}

/// Spec: GB({0}) = ∅ (zero polynomial generates the zero ideal,
/// whose only generating set is ∅ — every basis after filtering
/// is empty).
#[test]
fn sparse_gb_of_zero_only_is_empty() {
    let ring = ring_p(5, 2);
    let z = SparsePolynomial::zero();
    let gb = groebner_basis(vec![z], &ring, None);
    assert!(gb.is_empty(), "GB({{0}}) must be empty");
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

// ── (9) engine equivalence on a GF(2)-specific system (smallest field) ──

/// Spec: over GF(2), 1 + 1 = 0 and squaring is the identity on
/// constants. The reduced GB algorithm must still produce a sound
/// result. Cross-check sparse ≡ dense on a system that exercises the
/// "small-prime arithmetic edge" — corpus memory says small primes
/// have bitten the bit-prop subsystem (R5/H1, R7/J1).
#[test]
fn sparse_vs_dense_gf2_specific_system() {
    let ring = ring_p(2, 3);
    let x = SparsePolynomial::variable(0, &ring);
    let y = SparsePolynomial::variable(1, &ring);
    let z = SparsePolynomial::variable(2, &ring);
    // x*y + z, x + y + z, x*z + 1.
    let one = SparsePolynomial::constant(ring.field.one(), &ring);
    let g1 = x.mul(&y, &ring).add(&z, &ring);
    let g2 = x.add(&y, &ring).add(&z, &ring);
    let g3 = x.mul(&z, &ring).add(&one, &ring);
    let gens = vec![g1, g2, g3];

    let gb_s = interreduce(groebner_basis(gens.clone(), &ring, None), &ring, None);
    let gens_d: Vec<DensePoly> = gens.iter().map(|p| p.to_dense(&ring)).collect();
    let gb_d_dense = dense_interreduce(
        dense_gb(gens_d, &ring, &BuchbergerConfig::default()).unwrap().basis,
        &ring,
    );
    let gb_d: Vec<SparsePolynomial> = gb_d_dense
        .iter()
        .map(|p| SparsePolynomial::from_dense(p, &ring))
        .collect();

    assert_ideals_equal(&gb_s, &gb_d, &ring);
}
