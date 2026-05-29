use super::*;
use crate::ff::field::PrimeField;
use crate::frontend::bitprop::BitProp;
use crate::gb::ideal::Ideal;
use num_bigint::BigUint;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

/// Evaluate `p` at the given point. Local copy mirroring
/// `tests::eval_poly` (helpers stay duplicated rather than shared via
/// `pub(super)` to keep the source mod free of test-only items).
fn eval_poly(pr: &FfPolyRing, p: &Poly, point: &[FieldElem]) -> FieldElem {
    let ring = &pr.ring;
    let fp = &pr.field();
    let mut acc = fp.zero();
    for (c, m) in ring.terms(p) {
        let mut t = fp.clone_el(c);
        for v in 0..pr.n_vars() {
            let e = ring.exponent_at(&m, v);
            for _ in 0..e {
                t = fp.mul_ref(&t, &point[v]);
            }
        }
        fp.add_assign(&mut acc, t);
    }
    acc
}

// =============================================================================
// HARD-PROBE TESTS — split-gb-orchestration risk surface
// =============================================================================
//
// These tests are spec-driven and engineered to FAIL if a bug hides in the
// multi-partition orchestration: differential against monolithic Buchberger,
// cancellation determinism, edge primes (BN128, curve25519), and pathological
// partition shapes (single partition, constants-only, disconnected components).
//
// Spec sources:
//   * Ideal theory: a system is SAT in GF(p) iff there exists a common
//     zero in GF(p)^n; the ideal is the whole ring iff 1 ∈ I.
//   * Split-GB soundness contract: split_find_zero returns SAT iff a model
//     exists; UNSAT iff (and only if) exhaustive search proved no model;
//     Unknown otherwise. SAT models MUST satisfy every original generator.
//   * Cancellation contract: a pre-cancelled CancelToken means split_find_zero
//     MUST NOT return Sat or Unsat (those are verdicts requiring real work).
//   * Partition admissibility (`admit`): partition 0 admits deg≤1; partition 1
//     admits deg≤1 ∧ terms≤2; partition idx≥2 is never admitted (but ideals can
//     still hold higher-degree generators in their basis).

/// BN128 / BN254 scalar field prime (~2^254). Used as a real ZK use case.
fn bn128_field() -> PrimeField {
    PrimeField::new(
        BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap(),
    )
}

/// Curve25519 base field prime (2^255 - 19).
fn curve25519_field() -> PrimeField {
    PrimeField::new(
        BigUint::parse_bytes(
            b"57896044618658097711785492504343953926634992332820282019728792003956564819949",
            10,
        )
        .unwrap(),
    )
}

/// Build a monolithic ideal (single basis containing every original
/// generator). Used as the spec oracle in differential tests against
/// split-GB.
fn monolithic_is_whole_ring(pr: &FfPolyRing, generators: Vec<Poly>) -> bool {
    let ideal = Ideal::new(pr, generators);
    ideal.is_whole_ring()
}

// -----------------------------------------------------------------------------
// (d) Single-partition: split_gb on k=1 must agree with monolithic Buchberger.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: a one-partition split-GB returns a basis whose
/// `is_whole_ring` disagrees with the monolithic Buchberger verdict.
/// SPEC: `Ideal::new` and `split_gb(k=1, gens)` ideal-theoretically build
/// the SAME ideal; their `is_whole_ring()` must match.
#[test]
fn hard_single_partition_unsat_matches_monolithic() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    // x = 1 ∧ x = 2 over GF(7) → UNSAT.
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![vec![pr.clone_poly(&g1), pr.clone_poly(&g2)]],
        &mut bp,
    );
    let split_whole = basis.iter().any(|b| b.is_whole_ring());
    let mono_whole = monolithic_is_whole_ring(&pr, vec![g1, g2]);
    assert_eq!(
        split_whole, mono_whole,
        "split_gb(k=1) whole-ring verdict must match monolithic Buchberger"
    );
}

/// HYPOTHESIS: a one-partition SAT system causes split_gb to spuriously
/// declare whole-ring.
/// SPEC: a system with at least one common zero in GF(p) is NOT the whole
/// ring (since 1 cannot vanish at that zero).
#[test]
fn hard_single_partition_sat_not_whole_ring() {
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let f = pr.field();
    // x = 2 ∧ y = 3 over GF(5) → SAT (unique point).
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let g2 = pr.sub(pr.var(1), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        !basis.iter().any(|b| b.is_whole_ring()),
        "SAT single-partition cannot reduce to whole ring"
    );
}

// -----------------------------------------------------------------------------
// (a) Multi-partition differential: split-GB whole-ring iff monolithic GB
// is whole-ring (the soundness invariant).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_gb on a SAT system with multiple partitions
/// spuriously detects UNSAT (whole ring).
/// SPEC: x = 1 in partition 0 (linear), and x·y - 1 = 0 with y = 1 in
/// partition 1 (nonlinear), is jointly SAT with model (1, 1); monolithic
/// Buchberger must NOT be whole ring; therefore split_gb must NOT have any
/// whole-ring partition.
#[test]
fn hard_multi_partition_sat_matches_monolithic() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g_x = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let xy = pr.mul(pr.var(0), pr.var(1));
    let g_xy = pr.sub(xy, pr.constant(f.one()));
    let g_y = pr.sub(pr.var(1), pr.constant(f.from_int(1)));

    let all = vec![
        pr.clone_poly(&g_x),
        pr.clone_poly(&g_xy),
        pr.clone_poly(&g_y),
    ];
    let mono_whole = monolithic_is_whole_ring(&pr, all);

    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g_x, g_y], vec![g_xy]], &mut bp);
    let split_whole = basis.iter().any(|b| b.is_whole_ring());
    assert_eq!(
        split_whole, mono_whole,
        "split_gb whole-ring verdict must match monolithic Buchberger"
    );
    assert!(
        !split_whole,
        "joint system has model (1,1) ⇒ not whole ring"
    );
}

/// HYPOTHESIS: multi-partition GF(p)-UNSAT system is correctly detected by
/// the orchestrator's exhaustive search.
/// SPEC: x + y = 0 ∧ x·y - 1 = 0 over GF(7) forces x² = -1 = 6, a
/// non-residue mod 7 (QRs are {1, 2, 4}). Joint system has no solution
/// in GF(7), so split_find_zero (which runs an exhaustive small-prime
/// search) must return Unsat. NOTE: monolithic Buchberger on the raw
/// {x+y, x·y-1} (without field polynomials) does NOT collapse to {1};
/// the system has roots in F_49 ⊃ GF(7). The whole-ring comparison only
/// makes sense after adding field polys x^7-x, y^7-y; we skip it.
#[test]
fn hard_multi_partition_unsat_matches_monolithic() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g_lin = pr.add(pr.var(0), pr.var(1));
    let g_nl = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
    let mut bp = BitProp::new(&pr);
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![pr.clone_poly(&g_lin)]),
        Ideal::from_gb(&pr, vec![pr.clone_poly(&g_nl)]),
    ];
    let outcome = split_find_zero(&pr, split_basis, &mut bp);
    match outcome {
        SplitFindZeroOutcome::Unsat => {}
        other => panic!(
            "split_find_zero on GF(7)-UNSAT system must return Unsat, got {:?}",
            other
        ),
    }
}

// -----------------------------------------------------------------------------
// (e) Partition containing only constants / pathological edge shapes.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: a partition whose initial basis contains 1 (already whole
/// ring) is not detected as UNSAT.
/// SPEC: any basis containing a nonzero constant is the whole ring; the
/// orchestrator must return Unsat without exploring.
#[test]
fn hard_partition_with_one_already_whole_ring() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let mut bp = BitProp::new(&pr);
    // Partition 1 already has the constant 1 ⇒ whole ring from the start.
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![]),
        Ideal::from_gb(&pr, vec![pr.one()]),
    ];
    // The split_find_zero contract on a system with a whole-ring partition
    // and no completing original constraints: the first-frame fast path
    // returns NoZero{exhaustive:true} (Unsat). Sound because 1 ∈ basis
    // means the ideal is the whole ring.
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Unsat => {}
        other => panic!(
            "whole-ring partition (basis = {{1}}) must yield Unsat, got {:?}",
            other
        ),
    }
}

/// HYPOTHESIS: a partition containing only the zero polynomial (which is
/// the trivial ideal {0}) is mishandled.
/// SPEC: zero generators define the ZERO ideal; {0} is NOT the whole ring
/// and trivially has every point of GF(p)^n as a zero, so an empty-input
/// system over k vars must return SAT.
#[test]
fn hard_partition_zero_generators_not_whole_ring() {
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![], vec![]], &mut bp);
    assert_eq!(basis.len(), 2);
    for b in &basis {
        assert!(
            !b.is_whole_ring(),
            "zero ideal {{0}} is NOT the whole ring"
        );
    }
    // SAT contract: every point is a zero of {0}, so split_find_zero must
    // return some SAT model.
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => assert_eq!(pt.len(), 2),
        other => panic!(
            "empty-ideal system must be SAT (every point is a zero), got {:?}",
            other
        ),
    }
}

/// HYPOTHESIS: a system where partition 1 (the nonlinear partition) is
/// empty while partition 0 carries every constraint is mishandled.
/// SPEC: the union of bases is the original ideal; partition shape MUST
/// NOT affect verdict.
#[test]
fn hard_all_constraints_in_one_partition_other_empty() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    // x = 3 (deg-1, single term — admitted by partition 0).
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![pr.clone_poly(&g)], vec![]], &mut bp);
    // Partition 0 should have the constraint; partition 1 is empty.
    assert!(
        !basis.iter().any(|b| b.is_whole_ring()),
        "consistent single-constraint system is not whole ring"
    );
    // SAT verdict with x = 3 from split_find_zero.
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(3u32));
        }
        other => panic!("expected SAT(x=3), got {:?}", other),
    }
}

// -----------------------------------------------------------------------------
// (b) Pre-cancelled CancelToken → must NOT return Sat or Unsat.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_find_zero_cancel with a pre-cancelled token still
/// returns a verdict (Sat or Unsat). That would be UNSOUND — a verdict
/// requires search work.
/// SPEC: pre-cancelled token MUST yield Err(Cancelled).
#[test]
fn hard_pre_cancelled_yields_cancelled_not_verdict() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    // Concrete SAT system: x = 3. Without cancel, this is Sat.
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let split_basis: SplitGb = vec![Ideal::from_gb(&pr, vec![g])];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "pre-cancelled token MUST yield Err(Cancelled), not a verdict"
    );
}

/// HYPOTHESIS: pre-cancelled token on a multi-partition SAT system still
/// yields Sat. Spec: pre-cancelled → Cancelled.
#[test]
fn hard_pre_cancelled_multi_partition_yields_cancelled() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let g2 = pr.sub(pr.var(1), pr.constant(f.from_int(3)));
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![g1]),
        Ideal::from_gb(&pr, vec![g2]),
    ];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "pre-cancelled multi-partition SAT must yield Cancelled"
    );
}

/// HYPOTHESIS: pre-cancelled token on a UNSAT system still yields Unsat.
/// SPEC: pre-cancelled → Cancelled.
#[test]
fn hard_pre_cancelled_unsat_still_cancelled() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let split_basis: SplitGb = vec![Ideal::from_gb(&pr, vec![g1, g2])];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "pre-cancelled UNSAT input must yield Cancelled, not Unsat"
    );
}

// -----------------------------------------------------------------------------
// (c) Mid-pipeline cancel: fire AFTER add_generators (split_gb_cancel returns)
//     but BEFORE split_find_zero_cancel; the next phase must report Cancelled.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: cancellation set between split_gb_cancel and
/// split_find_zero_cancel is ignored by the search phase.
/// SPEC: a cancel-aware API MUST honor cancellation on entry.
#[test]
fn hard_mid_pipeline_cancel_between_extend_and_search() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(4)));
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::new();
    // Phase 1: build the split GB with a non-fired cancel token.
    let split_basis =
        split_gb_cancel(&pr, vec![vec![g]], &mut bp, &cancel).expect("phase 1 should complete");
    // Phase 2: fire cancel BEFORE search.
    cancel.cancel();
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "mid-pipeline cancel (fired between phases) must be honored, got {:?}",
        out
    );
}

/// HYPOTHESIS: cancellation set between extend_cancel returning and the
/// next call to extend_cancel is ignored.
/// SPEC: cancel-aware APIs honor cancellation on every call entry.
#[test]
fn hard_mid_pipeline_cancel_between_two_extend_calls() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::new();
    let starting: SplitGb = vec![Ideal::from_gb(&pr, vec![])];
    // First extend completes successfully.
    let mid = split_gb_extend_cancel(&pr, starting, vec![vec![g1]], &mut bp, &cancel)
        .expect("first extend should succeed");
    // Cancel before the second extend.
    cancel.cancel();
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let out = split_gb_extend_cancel(&pr, mid, vec![vec![g2]], &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "second extend after mid-pipeline cancel must return Cancelled"
    );
}

// -----------------------------------------------------------------------------
// Big primes — BN128 / curve25519. Historically big-prime arithmetic edge
// cases harbor bugs (cf. round 5 H1 bitprop bit-cache, round 7 J1 bit-width
// guard). Probe both with concrete SAT and UNSAT systems whose verdict is
// fixed by elementary number theory.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_gb on a trivial concrete SAT system over BN128 fails
/// (returns Unsat or whole-ring on the input ideal).
/// SPEC: {x - 7, y - 11} over GF(BN128) is jointly SAT with the unique
/// model (7, 11). The basis MUST NOT be whole ring.
#[test]
fn hard_bn128_concrete_sat_not_whole_ring() {
    let pr = FfPolyRing::new(bn128_field(), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(7)));
    let g2 = pr.sub(pr.var(1), pr.constant(f.from_int(11)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        !basis.iter().any(|b| b.is_whole_ring()),
        "BN128 SAT system must not be whole ring"
    );
}

/// HYPOTHESIS: split_gb on a concrete BN128 UNSAT system fails to detect
/// UNSAT (no whole-ring partition).
/// SPEC: {x - 7, x - 13} over GF(BN128) is UNSAT (7 ≠ 13 mod the prime);
/// monolithic Buchberger reduces to the constant (7 - 13) = -6 ≠ 0.
#[test]
fn hard_bn128_concrete_unsat_matches_monolithic() {
    let pr = FfPolyRing::new(bn128_field(), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(7)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(13)));
    let all = vec![pr.clone_poly(&g1), pr.clone_poly(&g2)];
    assert!(
        monolithic_is_whole_ring(&pr, all),
        "spec: monolithic BN128 must detect this UNSAT"
    );
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        basis.iter().any(|b| b.is_whole_ring()),
        "split_gb on BN128 UNSAT must produce a whole-ring partition"
    );
}

/// HYPOTHESIS: curve25519 prime arithmetic in the multi-partition flow
/// flips a SAT verdict.
/// SPEC: {x - 42} over GF(curve25519) with partition split: linear
/// partition holds the constraint; the basis must not be whole ring.
#[test]
fn hard_curve25519_concrete_sat_not_whole_ring() {
    let pr = FfPolyRing::new(curve25519_field(), vec!["x".into()]);
    let f = pr.field();
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(42)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g]], &mut bp);
    assert!(
        !basis.iter().any(|b| b.is_whole_ring()),
        "curve25519 SAT must not produce a whole-ring basis"
    );
}

/// HYPOTHESIS: curve25519 UNSAT detection is broken in multi-partition.
/// SPEC: {x - 1, x - 99} over GF(curve25519): UNSAT (1 ≠ 99 mod p).
#[test]
fn hard_curve25519_concrete_unsat_detected() {
    let pr = FfPolyRing::new(curve25519_field(), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(99)));
    let all = vec![pr.clone_poly(&g1), pr.clone_poly(&g2)];
    assert!(
        monolithic_is_whole_ring(&pr, all),
        "spec: monolithic curve25519 must detect this UNSAT"
    );
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        basis.iter().any(|b| b.is_whole_ring()),
        "split_gb on curve25519 UNSAT must produce a whole-ring partition"
    );
}

/// HYPOTHESIS: a multi-partition BN128 SAT system returns Sat but the
/// returned model fails to satisfy every original generator (most likely
/// a subtle "model from one partition" bug).
/// SPEC: a SAT verdict's model MUST zero EVERY original generator
/// (across all partitions, before the partition split was applied).
#[test]
fn hard_bn128_multi_partition_sat_model_satisfies_all_originals() {
    let pr = FfPolyRing::new(bn128_field(), vec!["x".into(), "y".into()]);
    let f = pr.field();
    // Cross-partition constraints: x = 5 (linear, partition 0),
    // x·y = 35 ⇒ y = 7 once x = 5 (nonlinear, partition 1).
    let g_x = pr.sub(pr.var(0), pr.constant(f.from_int(5)));
    let g_xy =
        pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.from_int(35)));
    let all_originals = vec![pr.clone_poly(&g_x), pr.clone_poly(&g_xy)];

    let mut bp = BitProp::new(&pr);
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![pr.clone_poly(&g_x)]),
        Ideal::from_gb(&pr, vec![pr.clone_poly(&g_xy)]),
    ];
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Sat(model) => {
            assert_eq!(model.len(), 2);
            for g in &all_originals {
                let v = eval_poly(&pr, g, &model);
                assert!(
                    pr.field().is_zero(&v),
                    "SAT model must zero every original generator"
                );
            }
        }
        // Unknown is permitted on big primes if the brancher cannot complete
        // enumeration; this test is about SOUNDNESS of any SAT it does return.
        SplitFindZeroOutcome::Unknown => {}
        SplitFindZeroOutcome::Unsat => panic!(
            "system has model (5, 7) — must not return Unsat"
        ),
    }
}

// -----------------------------------------------------------------------------
// "Many partitions": stress the orchestrator with k > 2 (forcing the
// `(0..k)` loops in the fixpoint body to actually iterate).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: the orchestrator's `(0..k)` loops are silently wrong for k > 2
/// (where k > 2 partitions are constructed manually — the default builder
/// uses k = 2). Each partition holds independent constraints whose
/// conjunction has a known SAT verdict.
/// SPEC: {x - 1, y - 2, z - 3} distributed across k = 3 partitions has the
/// unique model (1, 2, 3) in GF(7); no partition becomes whole ring.
#[test]
fn hard_many_partitions_sat_no_partition_whole_ring() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into(), "z".into()]);
    let f = pr.field();
    let g_x = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g_y = pr.sub(pr.var(1), pr.constant(f.from_int(2)));
    let g_z = pr.sub(pr.var(2), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    // Note: `admit` only admits partition indices 0, 1; partitions ≥ 2 are
    // never admitted via cross-partition propagation. But the
    // `split_gb_cancel` builder still EXTENDS every partition with its OWN
    // new_polys (the per-i `extend_with_cancel` call). So extra partitions
    // hold their own initial generators correctly.
    let basis = split_gb(
        &pr,
        vec![vec![g_x], vec![g_y], vec![g_z]],
        &mut bp,
    );
    assert_eq!(basis.len(), 3);
    for (i, b) in basis.iter().enumerate() {
        assert!(
            !b.is_whole_ring(),
            "partition {} on SAT input must not be whole ring",
            i
        );
    }
}

/// HYPOTHESIS: a system distributed across 3 partitions where partition 2
/// holds the only inconsistent pair fails to be detected as UNSAT.
/// SPEC: x = 1 ∧ x = 2 in partition 2 (over GF(5)) makes partition 2
/// whole-ring after its own extend. Cross-partition propagation isn't
/// needed because the per-partition extend handles each partition
/// independently. The disjunction `any(is_whole_ring)` MUST fire.
#[test]
fn hard_many_partitions_unsat_in_third_partition_detected() {
    let pr = FfPolyRing::new(ff(5), vec!["x".into()]);
    let f = pr.field();
    let g_a = pr.sub(pr.var(0), pr.constant(f.from_int(0)));
    let g_b = pr.sub(pr.var(0), pr.constant(f.from_int(0))); // dup
    let g_inc1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g_inc2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![vec![g_a], vec![g_b], vec![g_inc1, g_inc2]],
        &mut bp,
    );
    assert_eq!(basis.len(), 3);
    assert!(
        basis.iter().any(|b| b.is_whole_ring()),
        "intra-partition UNSAT in partition 2 must produce whole-ring"
    );
}

// -----------------------------------------------------------------------------
// Repeated / duplicate generators (idempotence).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: adding the same generator twice changes the verdict.
/// SPEC: ideals are sets; duplicates make no semantic difference.
#[test]
fn hard_duplicate_generators_preserve_verdict() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(4)));
    let mut bp1 = BitProp::new(&pr);
    let basis_one = split_gb(&pr, vec![vec![pr.clone_poly(&g)]], &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis_dup = split_gb(
        &pr,
        vec![vec![pr.clone_poly(&g), pr.clone_poly(&g), pr.clone_poly(&g)]],
        &mut bp2,
    );
    assert_eq!(
        basis_one.iter().any(|b| b.is_whole_ring()),
        basis_dup.iter().any(|b| b.is_whole_ring()),
        "duplicate generators must not change the whole-ring verdict"
    );
    // Both must agree the SAT model is x = 4.
    let out1 = split_find_zero(&pr, basis_one, &mut bp1);
    let out2 = split_find_zero(&pr, basis_dup, &mut bp2);
    for (i, out) in [&out1, &out2].iter().enumerate() {
        match out {
            SplitFindZeroOutcome::Sat(pt) => {
                assert_eq!(
                    pr.field().to_biguint(&pt[0]),
                    BigUint::from(4u32),
                    "outcome {} must be x = 4",
                    i
                );
            }
            other => panic!("outcome {}: expected SAT(x=4), got {:?}", i, other),
        }
    }
}

// -----------------------------------------------------------------------------
// Disconnected partition components: 4 independent univariate constraints
// in disjoint variable sets stress the orchestration's many-partition
// extend loop without cross-partition propagation interactions.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: the orchestrator's multi-partition extend mishandles fully
/// disjoint variable sets (each constraint touches a unique variable, so
/// there's no cross-partition propagation; the verdict comes solely from
/// independent per-partition GB).
/// SPEC: 4 disjoint linear constraints {x0 = 0, x1 = 1, x2 = 2, x3 = 3}
/// in GF(5)^4 has the unique point (0, 1, 2, 3) ⇒ SAT and not whole-ring.
#[test]
fn hard_disconnected_components_sat() {
    let pr = FfPolyRing::new(
        ff(5),
        vec!["x0".into(), "x1".into(), "x2".into(), "x3".into()],
    );
    let f = pr.field();
    let g = |i: usize, v: i64| pr.sub(pr.var(i), pr.constant(f.from_int(v)));
    let mut bp = BitProp::new(&pr);
    // 4 partitions, each with one independent constraint.
    let basis = split_gb(
        &pr,
        vec![vec![g(0, 0)], vec![g(1, 1)], vec![g(2, 2)], vec![g(3, 3)]],
        &mut bp,
    );
    assert_eq!(basis.len(), 4);
    for (i, b) in basis.iter().enumerate() {
        assert!(
            !b.is_whole_ring(),
            "disjoint constraint in partition {} ⇒ not whole ring",
            i
        );
    }
}

// -----------------------------------------------------------------------------
// admit() partition-index boundary on big primes.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: the `admit` partition-index guard fires differently on big
/// primes (it shouldn't — the predicate is purely structural).
/// SPEC: admit(_, idx ≥ 2, _) = false regardless of the polynomial or
/// the prime, since it doesn't depend on the field at all.
#[test]
fn hard_admit_idx_ge_2_rejects_on_big_primes() {
    let pr_bn128 = FfPolyRing::new(bn128_field(), vec!["x".into()]);
    let lin = pr_bn128.var(0);
    assert!(!admit(&pr_bn128, 2, &lin), "BN128: idx=2 never admits");
    assert!(!admit(&pr_bn128, 7, &lin), "BN128: idx=7 never admits");

    let pr_25519 = FfPolyRing::new(curve25519_field(), vec!["x".into()]);
    let lin2 = pr_25519.var(0);
    assert!(!admit(&pr_25519, 2, &lin2), "curve25519: idx=2 never admits");
}

// -----------------------------------------------------------------------------
// Edge primes — GF(2), GF(3): smallest possible fields.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: GF(2) tiny-prime corner case is mishandled.
/// SPEC: over GF(2), x = 1 is SAT with unique model x = 1. Verifying the
/// split_find_zero pipeline on the smallest prime.
#[test]
fn hard_gf2_sat_single_var() {
    let pr = FfPolyRing::new(ff(2), vec!["x".into()]);
    let f = pr.field();
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g]], &mut bp);
    assert!(!basis.iter().any(|b| b.is_whole_ring()));
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(1u32));
        }
        other => panic!("GF(2): expected SAT(x=1), got {:?}", other),
    }
}

/// HYPOTHESIS: GF(3) tiny-prime UNSAT is not detected.
/// SPEC: x = 1 ∧ x = 2 over GF(3) is UNSAT (1 ≠ 2 mod 3 ⇒ 1 ∈ I).
#[test]
fn hard_gf3_unsat_single_var() {
    let pr = FfPolyRing::new(ff(3), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        basis.iter().any(|b| b.is_whole_ring()),
        "GF(3): {{x-1, x-2}} reduces to gcd = 1 ⇒ whole ring"
    );
}

// -----------------------------------------------------------------------------
// Differential: split_find_zero verdict matches Buchberger whole-ring
// verdict on a curated UNSAT/SAT corpus across multiple primes.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_find_zero verdict for a small-prime UNSAT system
/// disagrees with the monolithic Buchberger whole-ring oracle.
/// SPEC: split_find_zero returns Unsat iff exhaustive search proves no
/// model exists; for small primes (round-robin is exhaustive), this is
/// equivalent to monolithic Buchberger declaring whole-ring.
#[test]
fn hard_differential_split_vs_monolithic_corpus() {
    // Each case: (prime, vars, generators, expected_sat).
    let cases: Vec<(PrimeField, Vec<String>, Vec<(usize, i64)>, bool)> = vec![
        // GF(5): x = 2 ∧ y = 3 → SAT (unique).
        (ff(5), vec!["x".into(), "y".into()], vec![(0, 2), (1, 3)], true),
        // GF(7): x = 1 ∧ x = 2 → UNSAT.
        (ff(7), vec!["x".into()], vec![(0, 1), (0, 2)], false),
        // GF(11): x = 5 ∧ y = 7 → SAT.
        (
            ff(11),
            vec!["x".into(), "y".into()],
            vec![(0, 5), (1, 7)],
            true,
        ),
        // GF(257): x = 100 ∧ x = 200 → UNSAT.
        (ff(257), vec!["x".into()], vec![(0, 100), (0, 200)], false),
        // GF(1009): x = 500 → SAT.
        (ff(1009), vec!["x".into()], vec![(0, 500)], true),
    ];
    for (idx, (field, var_names, eqs, expect_sat)) in cases.into_iter().enumerate() {
        let pr = FfPolyRing::new(field, var_names);
        let f = pr.field();
        let mut gens: Vec<Poly> = Vec::new();
        for (var, val) in &eqs {
            let g = pr.sub(pr.var(*var), pr.constant(f.from_int(*val)));
            gens.push(g);
        }
        let all_for_mono: Vec<Poly> = gens.iter().map(|g| pr.clone_poly(g)).collect();
        let mono_whole = monolithic_is_whole_ring(&pr, all_for_mono);
        assert_eq!(
            mono_whole, !expect_sat,
            "case {} monolithic oracle disagrees with expected",
            idx
        );

        let mut bp = BitProp::new(&pr);
        let split_basis: SplitGb =
            vec![Ideal::from_gb(&pr, gens), Ideal::from_gb(&pr, vec![])];
        let outcome = split_find_zero(&pr, split_basis, &mut bp);
        match (outcome, expect_sat) {
            (SplitFindZeroOutcome::Sat(_), true) => {}
            (SplitFindZeroOutcome::Unsat, false) => {}
            (other, _) => panic!(
                "case {}: split_find_zero outcome {:?} disagrees with expected_sat={}",
                idx, other, expect_sat
            ),
        }
    }
}

// -----------------------------------------------------------------------------
// `build_partitions` sanity (the default partition layout shared by
// conjunctive and cached build paths).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: `build_partitions` returns provenance not parallel to its
/// gens (this would be a silent invariant break).
/// SPEC: every per-basis (gens, provenance) pair has equal length.
#[test]
fn hard_build_partitions_provenance_parallel_to_gens() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    // 3 originals: one degree-1-single-term (admitted everywhere),
    // one degree-1-3-term (admitted by partition 0 only), one nonlinear.
    let p0 = pr.var(0);
    let p1 = pr.add(
        pr.add(pr.var(0), pr.var(1)),
        pr.constant(f.from_int(2)),
    ); // 3 terms, deg 1
    let p2 = pr.mul(pr.var(0), pr.var(1)); // deg 2
    let originals = vec![pr.clone_poly(&p0), pr.clone_poly(&p1), pr.clone_poly(&p2)];
    let bitsums: Vec<Poly> = vec![];
    let (gens, prov) = build_partitions(&pr, &originals, &bitsums);
    assert_eq!(gens.len(), 2, "default layout has 2 partitions");
    assert_eq!(prov.len(), 2);
    for (i, (g_i, p_i)) in gens.iter().zip(prov.iter()).enumerate() {
        assert_eq!(
            g_i.len(),
            p_i.len(),
            "partition {} provenance length must match gens length",
            i
        );
    }
    // Spec: partition 1 holds ALL originals (in order); partition 0 holds
    // only originals admitted as deg≤1.
    assert_eq!(
        gens[1].len(),
        originals.len(),
        "partition 1 (nonlinear) holds all originals"
    );
    // partition 0 admits p0 (1 term, deg 1) and p1 (3 terms, deg 1) but
    // not p2 (deg 2).
    assert_eq!(
        gens[0].len(),
        2,
        "partition 0 (linear) holds the deg-1 originals"
    );
}

// -----------------------------------------------------------------------------
// Cancellation during a long-running multi-partition extend: cancel
// before the extend call and after the partition has many generators.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: cancellation set before the very first iteration of
/// run_fixpoint inside `split_gb_extend_cancel` is dropped.
/// SPEC: pre-cancelled extend → Err(Cancelled), regardless of how
/// nontrivial the starting basis is.
#[test]
fn hard_extend_cancel_pre_cancelled_with_nontrivial_starting() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let g2 = pr.sub(pr.var(1), pr.constant(f.from_int(4)));
    let mut bp = BitProp::new(&pr);
    // Build a nontrivial starting basis with a never-firing token.
    let starting =
        split_gb_cancel(&pr, vec![vec![g1, g2]], &mut bp, &CancelToken::none())
            .expect("phase 1 ok");
    // Now extend with a fresh, pre-cancelled token.
    let new_g = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.from_int(12)));
    let out = split_gb_extend_cancel(
        &pr,
        starting,
        vec![vec![pr.clone_poly(&new_g)]],
        &mut bp,
        &CancelToken::cancelled(),
    );
    assert!(
        matches!(out, Err(Cancelled)),
        "pre-cancelled extend with nontrivial starting basis must return Cancelled"
    );
}

// -----------------------------------------------------------------------------
// Symmetry: the split-GB whole-ring verdict must be invariant under
// permutation of partitions (which partition gets which generator).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: the verdict of split_gb depends on which partition holds
/// each linear constraint.
/// SPEC: for two linear constraints whose conjunction is UNSAT, swapping
/// which partition gets each must not change the whole-ring detection.
#[test]
fn hard_partition_swap_invariance_unsat() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let make_g = || {
        let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
        let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
        (g1, g2)
    };
    let mut bp1 = BitProp::new(&pr);
    let (a1, b1) = make_g();
    let basis_ab = split_gb(&pr, vec![vec![a1], vec![b1]], &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let (a2, b2) = make_g();
    let basis_ba = split_gb(&pr, vec![vec![b2], vec![a2]], &mut bp2);
    // Both must detect UNSAT (some partition is whole ring).
    assert!(
        basis_ab.iter().any(|b| b.is_whole_ring())
            && basis_ba.iter().any(|b| b.is_whole_ring()),
        "partition swap must not change UNSAT detection"
    );
}

// -----------------------------------------------------------------------------
// Cross-engine: split_find_zero verdict matches monolithic
// `gb::model::find_zero_cancel` whole-ring/Sat verdict on a tiny
// zero-dimensional system.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_find_zero returns SAT but the SAT model contradicts
/// what an independent monolithic finder would produce.
/// SPEC: for a unique-solution zero-dim system, the SAT model is unique
/// up to GF semantics; both the split path and a monolithic Ideal::new
/// followed by an is_whole_ring check must agree the system is NOT whole-ring.
#[test]
fn hard_zero_dim_unique_sat_split_agrees_with_mono() {
    let pr = FfPolyRing::new(ff(13), vec!["x".into(), "y".into()]);
    let f = pr.field();
    // x = 5 ∧ y = 7 → unique SAT model.
    let g_x = pr.sub(pr.var(0), pr.constant(f.from_int(5)));
    let g_y = pr.sub(pr.var(1), pr.constant(f.from_int(7)));
    let mono = Ideal::new(
        &pr,
        vec![pr.clone_poly(&g_x), pr.clone_poly(&g_y)],
    );
    assert!(!mono.is_whole_ring(), "spec: SAT system is not whole ring");
    assert!(mono.is_zero_dim(), "spec: pinned system is zero-dim");

    let mut bp = BitProp::new(&pr);
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![g_x]),
        Ideal::from_gb(&pr, vec![g_y]),
    ];
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(5u32));
            assert_eq!(pr.field().to_biguint(&pt[1]), BigUint::from(7u32));
        }
        other => panic!("expected unique SAT(5, 7), got {:?}", other),
    }
}
