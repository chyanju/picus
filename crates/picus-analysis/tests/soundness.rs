//! Soundness regression tests for propagation lemmas. Each test
//! constructs a synthetic R1CS where a previously-overzealous lemma
//! would have falsely concluded uniqueness, and asserts that
//! propagation alone (no SMT backend) does NOT report `Safe`.
//!
//! Backend-assisted `Unsafe` discovery for the same cases is covered
//! by the `#[ignore]`d tests at the bottom: they currently fail
//! because `NativeFfBackend` hard-codes `add_field_polys: false`,
//! making it incomplete on small primes (≤ 1000). Phase 4 fixes
//! that knob; un-ignore these tests then.

use num_bigint::BigUint;
use picus_analysis::dpvl::{run_dpvl, DpvlConfig, DpvlResult, LemmaSet};
use picus_analysis::selector::SelectorKind;
use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};
use picus_smt::{SolverKind, Theory};

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

fn propagation_only_config() -> DpvlConfig {
    DpvlConfig {
        solver: SolverKind::None,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 5000,
        lemmas: LemmaSet::all(),
        dump_smt: None,
    }
}

fn native_ff_config() -> DpvlConfig {
    DpvlConfig {
        solver: SolverKind::Native,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 5000,
        lemmas: LemmaSet::all(),
        dump_smt: None,
    }
}

/// Synthetic ABOZ trap: with `sel = 0` the bilinear products vanish
/// and the linear sum admits multiple `(y0, y1)` pairs.
fn aboz_trap_r1cs() -> R1csFile {
    // GF(7). Wires:
    //   x_0 = one,
    //   x_1 = y0  (public output),
    //   x_2 = sel (public input),
    //   x_3 = c_extra (public input),
    //   x_4 = y1  (internal).
    //
    // Constraints:
    //   C1: sel * y0 = 0
    //   C2: sel * y1 = 0
    //   C3: (y0 + sel + c_extra + y1) * 1 = 0
    //
    // Witnesses with sel = c_extra = 0:
    //   W1: y0 = 0, y1 = 0
    //   W2: y0 = 1, y1 = 6  (1 + 6 ≡ 0 mod 7)
    // A pre-fix aboz would mark y0 / y1 known and return Safe; the
    // fix gates on `sel ≠ 0`, so the lemma must skip.
    let p = BigUint::from(7u32);
    let header = HeaderSection {
        field_size: 32,
        prime_number: p,
        n_wires: 5,
        n_pub_out: 1,
        n_pub_in: 2,
        n_prv_in: 0,
        n_labels: 5,
        m_constraints: 3,
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
        outputs: vec![1],
    }
}

/// Synthetic basis2 trap: GF(11) with 4 bits, where `2^4 = 16 > 11`
/// admits two distinct bit decompositions of the same target.
fn basis2_trap_r1cs() -> R1csFile {
    // GF(11). Wires:
    //   x_0 = one,
    //   x_1..x_4 = b0..b3 (public outputs),
    //   x_5 = target (public input).
    //
    // Constraints:
    //   C1: (b0 + 2 b1 + 4 b2 + 8 b3) * 1 = target
    //   C2..C5: b_i * (b_i - 1) = 0
    //
    // With target = 4:
    //   W1: (b0,b1,b2,b3) = (0,0,1,0)        sum 4
    //   W2: (b0,b1,b2,b3) = (1,1,1,1)        sum 15 ≡ 4 mod 11
    let p = BigUint::from(11u32);
    let p_minus_1 = 10u32;
    let header = HeaderSection {
        field_size: 32,
        prime_number: p,
        n_wires: 6,
        n_pub_out: 4,
        n_pub_in: 1,
        n_prv_in: 0,
        n_labels: 6,
        m_constraints: 5,
    };
    let mk_bin = |w: u32| Constraint {
        a: block(&[(w, 1)]),
        b: block(&[(w, 1), (0, p_minus_1)]),
        c: empty_block(),
    };
    let constraints = vec![
        Constraint {
            a: block(&[(1, 1), (2, 2), (3, 4), (4, 8)]),
            b: block(&[(0, 1)]),
            c: block(&[(5, 1)]),
        },
        mk_bin(1),
        mk_bin(2),
        mk_bin(3),
        mk_bin(4),
    ];
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1, 2, 3, 4, 5],
        },
        inputs: vec![0, 5],
        outputs: vec![1, 2, 3, 4],
    }
}

#[test]
fn aboz_does_not_overreport_when_selector_can_be_zero() {
    let r1cs = aboz_trap_r1cs();
    let result = run_dpvl(&r1cs, &propagation_only_config()).expect("DPVL should not error");
    assert!(
        !matches!(result, DpvlResult::Safe),
        "aboz must not promote y0/y1 when selector can be zero; got {:?}",
        result
    );
}

#[test]
fn basis2_does_not_overreport_when_bitwidth_exceeds_prime() {
    let r1cs = basis2_trap_r1cs();
    let result = run_dpvl(&r1cs, &propagation_only_config()).expect("DPVL should not error");
    assert!(
        !matches!(result, DpvlResult::Safe),
        "basis2 must not promote bits when 2^n > p; got {:?}",
        result
    );
}

/// End-to-end: with the native FF backend the analyzer must find the
/// two distinct witnesses and report `Unsafe`. Currently blocked by
/// `NativeFfBackend`'s hard-coded `add_field_polys: false`, which
/// makes GB on small primes incomplete. Un-ignore after Phase 4.
#[test]
#[ignore = "blocked by native_ff add_field_polys hard-code; fix in Phase 4"]
fn aboz_native_ff_finds_counterexample() {
    let r1cs = aboz_trap_r1cs();
    let result = run_dpvl(&r1cs, &native_ff_config()).expect("DPVL should not error");
    assert!(
        matches!(result, DpvlResult::Unsafe(_)),
        "expected Unsafe from native_ff, got {:?}",
        result
    );
}

#[test]
#[ignore = "blocked by native_ff add_field_polys hard-code; fix in Phase 4"]
fn basis2_native_ff_finds_counterexample() {
    let r1cs = basis2_trap_r1cs();
    let result = run_dpvl(&r1cs, &native_ff_config()).expect("DPVL should not error");
    assert!(
        matches!(result, DpvlResult::Unsafe(_)),
        "expected Unsafe from native_ff, got {:?}",
        result
    );
}
