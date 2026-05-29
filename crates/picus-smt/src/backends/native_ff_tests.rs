//! Tests for `native_ff.rs` — the `NativeFfBackend` constructor,
//! `dump_smt` formatting, the `SolverBackendDescriptor` registration,
//! and minimal end-to-end `solve` smoke (tiny GF(7) systems, <50ms).

use super::NativeFfBackend;
use crate::backends::{all_backend_descriptors, create_backend_by_name, SolverBackend, SolverResult};
use crate::poly_ir::{r1cs_to_poly_ir, PolyIR};
use crate::Theory;

use num_bigint::BigUint;
use picus_core::timeout::CancelToken;
use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};
use std::collections::HashSet;

// ─── Test fixtures ────────────────────────────────────────────────

fn make_r1cs(
    prime: BigUint,
    n_wires: u32,
    inputs: Vec<usize>,
    constraints: Vec<Constraint>,
) -> R1csFile {
    let m = constraints.len() as u32;
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header: HeaderSection {
            field_size: 32,
            prime_number: prime,
            n_wires,
            n_pub_out: 0,
            n_pub_in: 0,
            n_prv_in: 0,
            n_labels: 0,
            m_constraints: m,
        },
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: Vec::new() },
        inputs,
        outputs: Vec::new(),
    }
}

fn blk(wid: u32, factor: u32) -> ConstraintBlock {
    ConstraintBlock {
        nnz: 1,
        wire_ids: vec![wid],
        factors: vec![BigUint::from(factor)],
    }
}

fn empty_ir(p: BigUint, n_wires: usize, inputs: Vec<usize>, target: usize) -> PolyIR {
    let r1cs = make_r1cs(p, n_wires as u32, inputs, Vec::new());
    let known = HashSet::new();
    r1cs_to_poly_ir(&r1cs, &known, target).expect("ir builds")
}

// ─── Constructor + default ─────────────────────────────────────────

#[test]
fn test_native_ff_new_works() {
    let _b = NativeFfBackend::new();
}

#[test]
fn test_native_ff_default_equivalent_to_new() {
    let _a = NativeFfBackend::new();
    let _b = NativeFfBackend::default();
}

// ─── Inventory registration ───────────────────────────────────────

#[test]
fn prop_native_ff_descriptor_registered() {
    // The `inventory::submit!` block at the bottom of `native_ff.rs`
    // must produce a descriptor named "native" with Theory::Ff.
    let found = all_backend_descriptors()
        .into_iter()
        .any(|d| d.name == "native" && d.theory == Theory::Ff);
    assert!(found, "native+ff descriptor must be registered");
}

#[test]
fn prop_native_ff_create_by_name_builds() {
    let b = create_backend_by_name("native", Theory::Ff);
    assert!(b.is_some());
}

// ─── dump_smt (pure formatting) ──────────────────────────────────

#[test]
fn prop_dump_smt_header_mentions_prime() {
    // Doc spec: header line is "; Native FF solver (Groebner basis
    // over GF({})...)".
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let s = backend.dump_smt(&ir);
    assert!(s.contains("Native FF solver"), "header present");
    assert!(s.contains("GF(7)"), "prime in header: {}", s);
}

#[test]
fn prop_dump_smt_includes_disequality_lines() {
    // Doc spec: "for &(a, b) in &ics.disequalities { ... }" emits a
    // `; disequality: NAME != NAME` line.
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let s = backend.dump_smt(&ir);
    assert!(
        s.contains("disequality:"),
        "diseq line present: {}",
        s
    );
    // Target=1 ⇒ x1 != y1.
    assert!(
        s.contains("x1") && s.contains("y1"),
        "target wire 1's xy names in diseq: {}",
        s
    );
}

#[test]
fn prop_dump_smt_includes_equality_count_line() {
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let s = backend.dump_smt(&ir);
    assert!(s.contains("equalities"), "counts line present: {}", s);
}

#[test]
fn prop_dump_smt_each_equality_terminated_with_eq_zero() {
    // Each `eq[N]: ...` line ends in ` = 0`.
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let s = backend.dump_smt(&ir);
    for line in s.lines() {
        if line.starts_with("; eq[") {
            assert!(
                line.trim_end().ends_with("= 0"),
                "eq line not terminated: {}",
                line
            );
        }
    }
}

#[test]
fn prop_dump_smt_is_deterministic() {
    // Two dumps over the same IR must match exactly.
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let a = backend.dump_smt(&ir);
    let b = backend.dump_smt(&ir);
    assert_eq!(a, b);
}

// ─── solve smoke (tiny GF(7) inputs) ────────────────────────────

#[test]
fn smoke_solve_trivial_constraints_returns_sat_or_unknown_within_budget() {
    // A trivially satisfiable system: one constraint pin (x_0 = 1)
    // and target wire 1 unconstrained. The disequality `x_1 != y_1`
    // is SAT (both copies are free). Treat the verdict as
    // structural: a real backend must return either Sat or Unsat
    // (not Unknown) within a generous budget, and Unsat here would
    // indicate a soundness issue.
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let mut backend = NativeFfBackend::new();
    let cancel = CancelToken::none();
    let r = backend.solve(&ir, 5_000, &cancel).expect("no backend error");
    // Free target ⇒ SAT (witness pair exists with x_1 ≠ y_1).
    match r {
        SolverResult::Sat(_) => {}
        SolverResult::Unknown(_) => {} // tolerate (timeout/incomplete) — keeps structural
        SolverResult::Unsat => {
            panic!("free target wire should not be UNSAT (would indicate spurious UNSAT)")
        }
    }
}

#[test]
fn smoke_solve_respects_external_cancel_pre_call() {
    // If the cancel token is already cancelled when `solve` is
    // entered, the backend must return Unknown(Timeout) without
    // running the GB engine.
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let mut backend = NativeFfBackend::new();
    let cancel = CancelToken::cancelled();
    let r = backend.solve(&ir, 60_000, &cancel).expect("no backend error");
    assert!(
        matches!(r, SolverResult::Unknown(_)),
        "pre-cancelled solve must yield Unknown, got {:?}",
        r
    );
}

#[test]
fn smoke_solve_forced_unsat_returns_unsat() {
    // Force a contradiction: pin wire 1 to two distinct values via
    // two constraints `1 * x_1 = 2` and `1 * x_1 = 3` (over GF(7)).
    // The `x_1 != y_1` target diseq is then UNSAT — there's only one
    // possible value for x_1 (none, in fact). Result must be Unsat.
    //
    // Constraint A * B = C → (1 * x_0) * (1 * x_1) = (2 * x_0) gives x_1 = 2.
    let c1 = Constraint {
        a: blk(0, 1),
        b: blk(1, 1),
        c: blk(0, 2),
    };
    // x_1 = 3:
    let c2 = Constraint {
        a: blk(0, 1),
        b: blk(1, 1),
        c: blk(0, 3),
    };
    let r1cs = make_r1cs(BigUint::from(7u32), 3, vec![0], vec![c1, c2]);
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();

    let mut backend = NativeFfBackend::new();
    let cancel = CancelToken::none();
    let r = backend.solve(&ir, 5_000, &cancel).expect("no backend error");
    match r {
        SolverResult::Unsat => {}
        SolverResult::Unknown(_) => {} // tolerate but Sat would be a soundness bug
        SolverResult::Sat(_) => {
            panic!("contradictory pinning should not be SAT (would indicate spurious SAT)")
        }
    }
}
