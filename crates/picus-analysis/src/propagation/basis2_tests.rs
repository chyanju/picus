//! Unit tests for `basis2` propagation lemma.
//!
//! Spec pinned (from the basis2 module doc):
//!   * Matches `target + sum_i (-2^i) * bit_i = 0` (equivalently
//!     `target = sum_i 2^i * bit_i`) only when:
//!       - target coefficient is ±1,
//!       - the remaining coefficients are a contiguous power-of-2 sequence
//!         `2^0 .. 2^{n-1}` (no duplicates, no gaps),
//!       - every monomial is linear (no constants, no products, no squares).
//!   * Soundness gate: only fires when every bit is already pinned to
//!     `{0, 1}` AND (`2^n <= p` OR a companion proves `Σ 2^j b_j < p`).
//!   * When target is known and gate passes, marks every bit known.
//!   * `is_power_of_2(n)` ↔ `n != 0 && n & (n-1) == 0`.

use super::*;
use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;
use num_traits::{One, Zero};

use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};
use picus_smt::poly_ir::r1cs_to_poly_ir;

use crate::propagation::range::RangeValue;

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

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
    ConstraintBlock { nnz: 0, wire_ids: vec![], factors: vec![] }
}

/// Build an R1CS over GF(`p`) with `n_wires` total wires, the given
/// constraints, and the listed `inputs` (must include wire 0).
fn r1cs(
    p: u64,
    n_wires: u32,
    constraints: Vec<Constraint>,
    inputs: Vec<usize>,
    outputs: Vec<usize>,
) -> R1csFile {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(p),
        n_wires,
        n_pub_out: outputs.len() as u32,
        n_pub_in: (inputs.len() as u32).saturating_sub(1), // wire 0 is the one-wire
        n_prv_in: 0,
        n_labels: n_wires as u64,
        m_constraints: constraints.len() as u32,
    };
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: (0..n_wires as u64).collect() },
        inputs,
        outputs,
    }
}

/// Build an R1CS encoding `(b0 + 2 b1 + ... + 2^{k-1} b_{k-1}) * 1 = target`
/// together with `b_i (b_i - 1) = 0` for every bit.  Wire 0 is the
/// one-wire; bits are wires 1..=k; target is wire k+1.
fn basis2_r1cs(p: u64, k: usize, target_is_input: bool) -> R1csFile {
    let p_minus_1 = (p - 1) as u32;
    let weights: Vec<(u32, u32)> = (0..k).map(|i| ((i + 1) as u32, 1u32 << i)).collect();
    let target_wire = (k + 1) as u32;

    let mut constraints = Vec::new();
    // C0: weighted sum = target
    constraints.push(Constraint {
        a: block(&weights),
        b: block(&[(0, 1)]),
        c: block(&[(target_wire, 1)]),
    });
    // binary pins
    for i in 0..k {
        let w = (i + 1) as u32;
        constraints.push(Constraint {
            a: block(&[(w, 1)]),
            b: block(&[(w, 1), (0, p_minus_1)]),
            c: empty_block(),
        });
    }

    let inputs = if target_is_input {
        vec![0, target_wire as usize]
    } else {
        // outputs but no public input besides one-wire
        vec![0]
    };
    let outputs: Vec<usize> = (1..=k).map(|i| i).collect();
    r1cs(p, (k + 2) as u32, constraints, inputs, outputs)
}

// ---------------------------------------------------------------------------
// is_power_of_2 — math axiom
// ---------------------------------------------------------------------------

#[test]
fn prop_is_power_of_2_zero_is_false() {
    assert!(!is_power_of_2(&BigUint::zero()));
}

#[test]
fn prop_is_power_of_2_one_is_true() {
    // 1 = 2^0
    assert!(is_power_of_2(&BigUint::one()));
}

#[test]
fn prop_is_power_of_2_powers_up_to_128() {
    for k in 0..=128usize {
        let n: BigUint = BigUint::one() << k;
        assert!(is_power_of_2(&n), "2^{} should be a power of 2", k);
    }
}

#[test]
fn prop_is_power_of_2_non_powers_rejected() {
    for n in [3u32, 5, 6, 7, 9, 10, 12, 15, 1000].iter() {
        assert!(!is_power_of_2(&BigUint::from(*n)), "{} is not a power of 2", n);
    }
}

#[test]
fn prop_is_power_of_2_large_power_minus_one() {
    // (2^64 - 1) is all-ones binary — never a power of 2.
    let n = (BigUint::one() << 64usize) - BigUint::one();
    assert!(!is_power_of_2(&n));
}

// ---------------------------------------------------------------------------
// match_decomp — structural matcher
// ---------------------------------------------------------------------------

/// Returns the first equality in `ir` that `match_decomp` accepts as
/// `target = Σ 2^k bit_k`, normalised to (target_wire, sorted bit wires).
fn first_decomp(ir: &picus_smt::poly_ir::PolyIR) -> Option<(usize, Vec<usize>, usize)> {
    for poly in &ir.equalities {
        if let Some(d) = match_decomp(ir, poly) {
            let target = ir.var_to_wire(d.target_var);
            let bits: Vec<usize> = d.bits.iter().map(|&v| ir.var_to_wire(v)).collect();
            return Some((target, bits.clone(), bits.len()));
        }
    }
    None
}

#[test]
fn prop_match_decomp_finds_target_and_ordered_bits() {
    // 4-bit decomposition over GF(101): 2^4 = 16 <= 101. The lemma
    // recognises the equality; bits[k] is the weight-2^k wire.
    let r = basis2_r1cs(101, 4, /*target_is_input=*/ true);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");

    let (target, bits, count) = first_decomp(&ir).expect("decomposition matched");
    assert_eq!(target, 5, "target wire is k+1");
    assert_eq!(count, 4);
    // bits[0] is the weight-1 bit, etc. (wire 1 is the LSB by construction).
    assert_eq!(bits, vec![1, 2, 3, 4]);
}

#[test]
fn prop_match_decomp_rejects_missing_weight() {
    // Skip the weight-2 bit: coefficients become {1, 4, 8}. The matcher
    // requires CONTIGUOUS weights 0..n-1, so this must NOT match.
    let p = 101u64;
    let constraints = vec![
        Constraint {
            // (1*b0 + 4*b2 + 8*b3) * 1 = target
            a: block(&[(1, 1), (2, 4), (3, 8)]),
            b: block(&[(0, 1)]),
            c: block(&[(4, 1)]),
        },
    ];
    let r = r1cs(p, 5, constraints, vec![0, 4], vec![1, 2, 3]);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    // Even though every coefficient is a power of two, the weight set
    // {0, 2, 3} is non-contiguous → reject.
    assert!(first_decomp(&ir).is_none(), "non-contiguous weights must not match");
}

#[test]
fn prop_match_decomp_rejects_non_power_of_two_coefficient() {
    // (1*b0 + 3*b1) — 3 is not a power of two.
    let p = 101u64;
    let constraints = vec![Constraint {
        a: block(&[(1, 1), (2, 3)]),
        b: block(&[(0, 1)]),
        c: block(&[(3, 1)]),
    }];
    let r = r1cs(p, 4, constraints, vec![0, 3], vec![1, 2]);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    assert!(first_decomp(&ir).is_none());
}

#[test]
fn prop_match_decomp_rejects_duplicate_weights() {
    // (1*b0 + 1*b1) — both bits have weight 2^0.
    let p = 101u64;
    let constraints = vec![Constraint {
        a: block(&[(1, 1), (2, 1)]),
        b: block(&[(0, 1)]),
        c: block(&[(3, 1)]),
    }];
    let r = r1cs(p, 4, constraints, vec![0, 3], vec![1, 2]);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    // Two terms with the SAME weight — `match_decomp` must reject.
    // Note: the constructed equality is `b0 + b1 - target = 0`. Choosing
    // target as the ±1 candidate leaves bits {b0, b1} both at weight 0.
    assert!(first_decomp(&ir).is_none());
}

#[test]
fn prop_match_decomp_needs_at_least_two_terms() {
    // Single-variable equality `b0 = 0` (from b0 * 1 = 0 lowered).
    // After removing the target candidate there are zero bits, so
    // `terms.len() < 2` → None.
    let p = 7u64;
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: empty_block(),
    }];
    let r = r1cs(p, 2, constraints, vec![0], vec![1]);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    assert!(first_decomp(&ir).is_none());
}

// ---------------------------------------------------------------------------
// Basis2Lemma::run — end-to-end propagation behaviour
// ---------------------------------------------------------------------------

/// Construct a default PropagationCtx for `n_wires` wires with the
/// given binary-set on `bit_wires` (mirroring what binary01 produces)
/// and the given known-wire set.
fn ctx_state(
    n_wires: usize,
    binary_wires: &[usize],
    known: &[usize],
) -> (HashSet<usize>, HashSet<usize>, HashMap<usize, RangeValue>, Vec<picus_core::poly::IrPoly>, Vec<Vec<picus_core::poly::IrPoly>>)
{
    let known_set: HashSet<usize> = known.iter().copied().collect();
    let unknown_set: HashSet<usize> = (0..n_wires).filter(|w| !known_set.contains(w)).collect();
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let binary_set: HashSet<BigUint> =
        [BigUint::zero(), BigUint::one()].into_iter().collect();
    for &w in binary_wires {
        ranges.insert(w, RangeValue::Values(binary_set.clone()));
    }
    (known_set, unknown_set, ranges, Vec::new(), Vec::new())
}

#[test]
fn prop_basis2_promotes_bits_when_target_known_and_gate_passes() {
    // 4-bit decomposition over GF(101); 2^4 = 16 < 101 — gate passes.
    // Bits are pinned binary, target is known → every bit promoted.
    let r = basis2_r1cs(101, 4, /*target_is_input=*/ true);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let (mut known, mut unknown, mut ranges, mut learned, mut learned_disj) =
        ctx_state(ir.n_wires, &[1, 2, 3, 4], &[0, 5]);
    let mut lemma = Basis2Lemma::default();
    let mut ctx = PropagationCtx {
        known: &mut known,
        unknown: &mut unknown,
        ranges: &mut ranges,
        learned: &mut learned,
        learned_disjunctions: &mut learned_disj,
    };
    let progress = lemma.run(&ir, &mut ctx);
    assert!(progress, "expected basis2 to make progress");
    for w in 1..=4 {
        assert!(known.contains(&w), "wire {} should be known", w);
        assert!(!unknown.contains(&w), "wire {} should leave unknown", w);
    }
}

#[test]
fn prop_basis2_does_not_promote_when_target_unknown() {
    // Same setup but target wire (5) NOT in `known`. Bits stay unknown.
    let r = basis2_r1cs(101, 4, /*target_is_input=*/ false);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let (mut known, mut unknown, mut ranges, mut learned, mut learned_disj) =
        ctx_state(ir.n_wires, &[1, 2, 3, 4], &[0]);
    let mut lemma = Basis2Lemma::default();
    let mut ctx = PropagationCtx {
        known: &mut known,
        unknown: &mut unknown,
        ranges: &mut ranges,
        learned: &mut learned,
        learned_disjunctions: &mut learned_disj,
    };
    let progress = lemma.run(&ir, &mut ctx);
    assert!(!progress, "no progress when target unknown");
    for w in 1..=4 {
        assert!(!known.contains(&w), "wire {} must NOT be promoted", w);
    }
}

#[test]
fn prop_basis2_does_not_promote_when_bits_not_pinned_binary() {
    // Target known, but bits not pinned to {0, 1} (no binary range
    // entries). Lemma must NOT fire — its precondition is unmet.
    let r = basis2_r1cs(101, 4, /*target_is_input=*/ true);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let (mut known, mut unknown, mut ranges, mut learned, mut learned_disj) =
        ctx_state(ir.n_wires, /* no bits marked binary */ &[], &[0, 5]);
    let mut lemma = Basis2Lemma::default();
    let mut ctx = PropagationCtx {
        known: &mut known,
        unknown: &mut unknown,
        ranges: &mut ranges,
        learned: &mut learned,
        learned_disjunctions: &mut learned_disj,
    };
    let progress = lemma.run(&ir, &mut ctx);
    assert!(!progress, "must not propagate without binary range");
    for w in 1..=4 {
        assert!(!known.contains(&w));
    }
}

#[test]
fn prop_basis2_soundness_gate_blocks_when_two_pow_n_exceeds_prime_no_companion() {
    // GF(11), 4 bits → 2^4 = 16 > 11. With no companion, the gate
    // MUST stay closed even when target is known and bits are binary.
    // This is the unit-level mirror of the integration soundness test
    // `bug_basis2_does_not_overreport_when_bitwidth_exceeds_prime`.
    let r = basis2_r1cs(11, 4, /*target_is_input=*/ true);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let (mut known, mut unknown, mut ranges, mut learned, mut learned_disj) =
        ctx_state(ir.n_wires, &[1, 2, 3, 4], &[0, 5]);
    let mut lemma = Basis2Lemma::default();
    let mut ctx = PropagationCtx {
        known: &mut known,
        unknown: &mut unknown,
        ranges: &mut ranges,
        learned: &mut learned,
        learned_disjunctions: &mut learned_disj,
    };
    let progress = lemma.run(&ir, &mut ctx);
    assert!(!progress, "gate must block: 2^4 > 11 and no companion");
    for w in 1..=4 {
        assert!(!known.contains(&w), "wire {} must NOT be promoted past gate", w);
    }
}

#[test]
fn prop_basis2_gate_open_when_two_pow_n_equals_prime_bound() {
    // GF(17), 4 bits → 2^4 = 16 <= 17. The gate uses `2^n <= p`
    // (strict `>` blocks), so the boundary `<=` permits propagation.
    let r = basis2_r1cs(17, 4, /*target_is_input=*/ true);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let (mut known, mut unknown, mut ranges, mut learned, mut learned_disj) =
        ctx_state(ir.n_wires, &[1, 2, 3, 4], &[0, 5]);
    let mut lemma = Basis2Lemma::default();
    let mut ctx = PropagationCtx {
        known: &mut known,
        unknown: &mut unknown,
        ranges: &mut ranges,
        learned: &mut learned,
        learned_disjunctions: &mut learned_disj,
    };
    let progress = lemma.run(&ir, &mut ctx);
    assert!(progress, "2^n == p+? boundary should still pass the gate");
    for w in 1..=4 {
        assert!(known.contains(&w));
    }
}

#[test]
fn prop_basis2_name_is_stable() {
    // The lemma name is the public CLI identifier; downstream config
    // matches against it. Locking it down here surfaces an accidental
    // rename in review.
    let l = Basis2Lemma::default();
    assert_eq!(l.name(), "basis2");
}

#[test]
fn prop_basis2_idempotent_when_already_known() {
    // Bits already in `known` (e.g., promoted by an earlier iteration).
    // The lemma must NOT report progress on a no-op run.
    let r = basis2_r1cs(101, 4, /*target_is_input=*/ true);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let (mut known, mut unknown, mut ranges, mut learned, mut learned_disj) =
        ctx_state(ir.n_wires, &[1, 2, 3, 4], &[0, 1, 2, 3, 4, 5]);
    let mut lemma = Basis2Lemma::default();
    let mut ctx = PropagationCtx {
        known: &mut known,
        unknown: &mut unknown,
        ranges: &mut ranges,
        learned: &mut learned,
        learned_disjunctions: &mut learned_disj,
    };
    let progress = lemma.run(&ir, &mut ctx);
    assert!(!progress, "no progress when every bit already known");
}

#[test]
fn prop_basis2_lemma_set_includes_basis2() {
    // basis2 must register with the inventory so DPVL discovers it.
    // Bare structural assertion: the live registry lists "basis2".
    use crate::propagation::all_names;
    assert!(all_names().iter().any(|n| *n == "basis2"));
}
