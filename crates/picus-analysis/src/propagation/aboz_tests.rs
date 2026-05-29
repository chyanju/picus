//! Unit tests for the ABOZ propagation lemma.
//!
//! Spec (from the file-top doc):
//!   pattern: `x*y0 = 0`, `x*y1 = 0`, `x + y0 + y1 + c = 0` with `x`
//!   known and `c` (some other wire) known.
//!   conclusion: if range proves `x ≠ 0` then `y0`, `y1` are uniquely
//!   determined (mark them known). Otherwise the rule must NOT promote
//!   them; it may optionally push (entailed) zero-product disjunctions
//!   when `aboz_emit_disjunctions` is on (default).

use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;
use picus_core::config::ConfigGuard;
use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};
use picus_smt::poly_ir::r1cs_to_poly_ir;

use super::*;
use crate::propagation::lemma::{PropagationCtx, PropagationLemma};
use crate::propagation::range::RangeValue;

// ── helpers ────────────────────────────────────────────────────────

fn block(pairs: &[(u32, u32)]) -> ConstraintBlock {
    let wire_ids: Vec<u32> = pairs.iter().map(|&(w, _)| w).collect();
    let factors: Vec<BigUint> = pairs.iter().map(|&(_, f)| BigUint::from(f)).collect();
    ConstraintBlock {
        nnz: wire_ids.len() as u32,
        wire_ids,
        factors,
    }
}

fn empty_block() -> ConstraintBlock {
    ConstraintBlock {
        nnz: 0,
        wire_ids: vec![],
        factors: vec![],
    }
}

/// GF(7) ABOZ-shape system mirroring the prose:
///   sel*y0 = 0,  sel*y1 = 0,  (y0 + sel + c_extra + y1)*1 = 0
/// Wires: 0 = one, 1 = y0 (output), 2 = sel (input), 3 = c_extra (input),
///        4 = y1 (output).
fn aboz_shape_r1cs() -> R1csFile {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 5,
        n_pub_out: 2,
        n_pub_in: 2,
        n_prv_in: 0,
        n_labels: 5,
        m_constraints: 3,
    };
    let constraints = vec![
        // sel * y0 = 0
        Constraint {
            a: block(&[(2, 1)]),
            b: block(&[(1, 1)]),
            c: empty_block(),
        },
        // sel * y1 = 0
        Constraint {
            a: block(&[(2, 1)]),
            b: block(&[(4, 1)]),
            c: empty_block(),
        },
        // (y0 + sel + c_extra + y1) * 1 = 0
        Constraint {
            a: block(&[(1, 1), (2, 1), (3, 1), (4, 1)]),
            b: block(&[(0, 1)]),
            c: empty_block(),
        },
    ];
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1, 2, 3, 4],
        },
        inputs: vec![0, 2, 3],
        outputs: vec![1, 4],
    }
}

/// Build a fresh `RangeValue::Values` containing the given small values.
fn vals(items: &[u32]) -> RangeValue {
    let set: HashSet<BigUint> = items.iter().map(|&v| BigUint::from(v)).collect();
    RangeValue::Values(set)
}

// ── tests ──────────────────────────────────────────────────────────

/// Spec: lemma is registered in the inventory under name `"aboz"`.
#[test]
fn prop_aboz_lemma_name_is_aboz() {
    let lemma = AbozLemma::default();
    assert_eq!(lemma.name(), "aboz");
}

/// Spec: ABOZ requires at least two bilinear-zero products. With no
/// equalities, there is nothing to match; the lemma must NOT report
/// progress.
#[test]
fn prop_aboz_no_progress_on_empty_ir() {
    // Use a trivial single-constraint R1CS so the IR is well-formed, then
    // clear equalities to leave the lemma nothing to match.
    let r1cs = aboz_shape_r1cs();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");
    ir.equalities.clear();
    let mut lemma = AbozLemma::default();
    let mut known_set: HashSet<usize> = known.clone();
    let mut unknown: HashSet<usize> = HashSet::new();
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut ctx = PropagationCtx {
        known: &mut known_set,
        unknown: &mut unknown,
        ranges: &mut ranges,
        learned: &mut learned,
        learned_disjunctions: &mut learned_disj,
    };
    assert!(!lemma.run(&ir, &mut ctx));
    assert!(ctx.learned_disjunctions.is_empty());
}

/// Spec: when the selector `sel` has a range that excludes zero AND
/// `sel` and at least one partner are already known, the lemma must
/// promote `y0`, `y1` from unknown to known.
#[test]
fn prop_aboz_promotes_when_selector_excludes_zero() {
    let r1cs = aboz_shape_r1cs();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    // Wires: 1 = y0, 2 = sel, 3 = c_extra, 4 = y1. Mark sel and c_extra
    // known; mark y0, y1 unknown; pin sel ∈ {1, ...} so range excludes 0.
    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(2);
    known_set.insert(3);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(4);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    ranges.insert(2, vals(&[1, 2, 3]));
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = AbozLemma::default();
    let progress = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    assert!(progress, "aboz should report progress on sel-nonzero shape");
    assert!(known_set.contains(&1), "y0 must be promoted to known");
    assert!(known_set.contains(&4), "y1 must be promoted to known");
    assert!(!unknown.contains(&1));
    assert!(!unknown.contains(&4));
}

/// Soundness gate: when the selector's range INCLUDES zero (or is
/// absent), `y0`/`y1` are NOT uniquely determined and must NOT be
/// promoted. (This is the bug the synthetic-trap test in
/// `tests/soundness.rs` regression-guards at the DPVL level — here we
/// pin it at the lemma level.)
#[test]
fn prop_aboz_does_not_promote_when_selector_can_be_zero() {
    // Disable disjunction emission so we observe ONLY the promote/no-promote
    // decision; otherwise progress may be true via disjunction emission.
    let _guard = ConfigGuard::with_override(|c| {
        c.aboz_emit_disjunctions = false;
    });

    let r1cs = aboz_shape_r1cs();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(2);
    known_set.insert(3);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(4);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    // sel ∈ {0, 1} — includes zero, so the gate must REMAIN closed.
    ranges.insert(2, vals(&[0, 1]));
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = AbozLemma::default();
    let progress = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "aboz must not promote when selector includes 0");
    assert!(unknown.contains(&1), "y0 must stay unknown");
    assert!(unknown.contains(&4), "y1 must stay unknown");
    assert!(!known_set.contains(&1));
    assert!(!known_set.contains(&4));
}

/// Soundness gate (Bottom range = unconstrained). With no recorded
/// range for `sel`, the lemma cannot prove `sel ≠ 0`; it must NOT
/// promote.
#[test]
fn prop_aboz_does_not_promote_when_selector_range_is_bottom() {
    let _guard = ConfigGuard::with_override(|c| {
        c.aboz_emit_disjunctions = false;
    });

    let r1cs = aboz_shape_r1cs();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(2);
    known_set.insert(3);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(4);
    // No range entry for wire 2 = Bottom (excludes_zero ⇒ false).
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = AbozLemma::default();
    let progress = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    // With aboz_emit_disjunctions=false (we set it above), the lemma
    // takes neither the promote nor the emit branch — progress stays
    // false and unknown wires stay unknown.
    assert!(!progress, "aboz must not report progress without sel non-zero proof");
    assert!(unknown.contains(&1));
    assert!(unknown.contains(&4));
    assert!(learned_disj.is_empty());
}

/// Spec: even when `sel` is provably non-zero, the lemma requires a
/// `known partner` distinct from x/y0/y1 in the linear sum. With
/// `c_extra` (wire 3) NOT known, no `has_known_partner` exists, so
/// the lemma must NOT promote.
#[test]
fn prop_aboz_requires_known_linear_partner() {
    let _guard = ConfigGuard::with_override(|c| {
        c.aboz_emit_disjunctions = false;
    });

    let r1cs = aboz_shape_r1cs();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(2); // sel known
    // wire 3 (c_extra) intentionally NOT known
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(3);
    unknown.insert(4);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    ranges.insert(2, vals(&[1, 2, 3]));
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = AbozLemma::default();
    let progress = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "no known partner in the linear sum ⇒ no progress");
    assert!(unknown.contains(&1));
    assert!(unknown.contains(&4));
}

/// Spec (disjunction path): when sel can be zero, with
/// `aboz_emit_disjunctions = true` the lemma emits the entailed
/// `(sel = 0) ∨ (y_i = 0)` clauses for both y0 and y1, and for both
/// copies (orig + alt). For each (s, o) pair that is 2 clauses; with
/// two pairs that's 4 disjunctions total.
#[test]
fn prop_aboz_emits_disjunctions_when_gate_closed() {
    let _guard = ConfigGuard::with_override(|c| {
        c.aboz_emit_disjunctions = true;
    });

    let r1cs = aboz_shape_r1cs();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(2);
    known_set.insert(3);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(4);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    ranges.insert(2, vals(&[0, 1])); // includes zero ⇒ gate closed
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = AbozLemma::default();
    let progress = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    assert!(progress, "should report progress via disjunction emission");
    // No promotion — gate is closed.
    assert!(unknown.contains(&1));
    assert!(unknown.contains(&4));
    // Disjunction count: 2 pairs × 2 copies = 4 clauses.
    assert_eq!(
        learned_disj.len(),
        4,
        "expected 4 disjunctions (2 pairs × orig+alt copies), got {}",
        learned_disj.len()
    );
    // Each clause is a 2-element `(var, var)` disjunction.
    for clause in &learned_disj {
        assert_eq!(clause.len(), 2);
    }
}

/// Spec (dedup): re-running the lemma to a fixed point must not flood
/// `learned_disjunctions` with duplicates of already-emitted (s, o)
/// pairs.
#[test]
fn prop_aboz_dedup_across_repeat_runs() {
    let _guard = ConfigGuard::with_override(|c| {
        c.aboz_emit_disjunctions = true;
    });

    let r1cs = aboz_shape_r1cs();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(2);
    known_set.insert(3);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(4);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    ranges.insert(2, vals(&[0, 1]));
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = AbozLemma::default();

    let _ = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    let after_first = learned_disj.len();

    // Second run with the same lemma instance: nothing new.
    let progress2 = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress2, "second run must not report progress (dedup)");
    assert_eq!(
        learned_disj.len(),
        after_first,
        "second run must not append duplicates"
    );
}

/// Coverage: with no linear sum in the IR, even with two bilinear
/// products the lemma cannot fire.
#[test]
fn test_aboz_no_progress_without_linear_sum() {
    // Drop the third constraint (the linear sum) by constructing a
    // 2-constraint R1CS.
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 5,
        n_pub_out: 2,
        n_pub_in: 2,
        n_prv_in: 0,
        n_labels: 5,
        m_constraints: 2,
    };
    let constraints = vec![
        Constraint {
            a: block(&[(2, 1)]),
            b: block(&[(1, 1)]),
            c: empty_block(),
        },
        Constraint {
            a: block(&[(2, 1)]),
            b: block(&[(4, 1)]),
            c: empty_block(),
        },
    ];
    let r1cs = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1, 2, 3, 4],
        },
        inputs: vec![0, 2, 3],
        outputs: vec![1, 4],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(2);
    known_set.insert(3);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(4);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    ranges.insert(2, vals(&[1, 2, 3]));
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = AbozLemma::default();
    let progress = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "no linear sum ⇒ no progress");
}

/// Soundness: `collect_bilinear_zero` rejects polynomials that contain
/// any term beyond a single bilinear monomial. A `x*x = 0` (univariate
/// squared) must NOT register, since exponent > 1 disqualifies the
/// term per `match_bilinear`'s `e > 1` rejection.
#[test]
fn prop_aboz_bilinear_rejects_squared_term() {
    // x_1^2 = 0 (NOT x_1 * x_2): wire 1 squared. The lemma must see
    // this as no bilinear-zero candidate.
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 3,
        n_pub_out: 1,
        n_pub_in: 1,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(1, 1)]),
        c: empty_block(),
    }];
    let r1cs = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1, 2],
        },
        inputs: vec![0, 1],
        outputs: vec![2],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 2).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(1);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(2);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    ranges.insert(1, vals(&[1, 2, 3]));
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = AbozLemma::default();
    let progress = {
        let mut ctx = PropagationCtx {
            known: &mut known_set,
            unknown: &mut unknown,
            ranges: &mut ranges,
            learned: &mut learned,
            learned_disjunctions: &mut learned_disj,
        };
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "x^2 = 0 alone is not an ABOZ shape");
}
