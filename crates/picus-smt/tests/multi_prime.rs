//! Multi-prime smoke test. Builds an R1CS over GF(7), runs it through
//! the PolyIR lowering and the native FF backend, and verifies both
//! consume the prime carried in the binary header.

use std::collections::HashSet;

use num_bigint::BigUint;
use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};
use picus_smt::backends::{SolverBackend, SolverResult};
use picus_smt::poly_ir::r1cs_to_poly_ir;

/// Build a synthetic R1CS over GF(7) encoding the trivial constraint
/// `x_1 * x_1 = x_2` over 3 wires (wire 0 is the one-wire, wire 1 is
/// the input, wire 2 is the output `x_1^2`). Two distinct witnesses
/// only exist if there are *two* preimages of `x_2`, which over GF(7)
/// happens for any non-zero `x_2`. The test then asks whether wire 2
/// is uniquely determined by wire 1 — it is (squaring is a function),
/// so the verdict on wire 2 should be UNSAT.
fn build_x1_squared_eq_x2() -> R1csFile {
    let p = BigUint::from(7u32);
    let header = HeaderSection {
        field_size: 32,
        prime_number: p.clone(),
        n_wires: 3,
        n_pub_out: 1,
        n_pub_in: 1,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    // constraint: x_1 * x_1 = x_2
    //   a = [x_1] (wire 1, coeff 1)
    //   b = [x_1]
    //   c = [x_2]
    let constraint = Constraint {
        a: ConstraintBlock {
            nnz: 1,
            wire_ids: vec![1],
            factors: vec![BigUint::from(1u32)],
        },
        b: ConstraintBlock {
            nnz: 1,
            wire_ids: vec![1],
            factors: vec![BigUint::from(1u32)],
        },
        c: ConstraintBlock {
            nnz: 1,
            wire_ids: vec![2],
            factors: vec![BigUint::from(1u32)],
        },
    };
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection {
            constraints: vec![constraint],
        },
        w2l: W2lSection { labels: vec![0, 1, 2] },
        // Inputs: wire 0 (one) + wire 2 (the public output's "input"
        // side under Ecne convention — istart=2+1=3 for n_pub_out=1,
        // which is past iend with no public inputs ⇒ inputs = [0])
        // For the test we treat wire 1 as input (private) and wire 2
        // as output.
        inputs: vec![0, 1],
        outputs: vec![2],
    }
}

#[test]
fn poly_ir_lowering_honours_non_bn128_prime() {
    let r1cs = build_x1_squared_eq_x2();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 2).expect("lowering should succeed");

    // Ring prime matches the R1CS header.
    assert_eq!(
        ir.ring.field().prime(),
        &BigUint::from(7u32),
        "ring prime should be 7, not BN128"
    );
    // Variable layout: 2 * n_wires = 6 (x0..x2, y0..y2).
    assert_eq!(ir.ring.var_names().len(), 6);
    // Equalities: 1 orig + 1 alt + x_0 = 1 pin = 3.
    assert_eq!(ir.equalities.len(), 3);
}

#[test]
fn native_ff_solves_over_gf7() {
    let r1cs = build_x1_squared_eq_x2();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 2).expect("lowering should succeed");
    ir.set_target(2);

    let mut backend = picus_smt::backends::native_ff::NativeFfBackend::new();
    let cancel = picus_core::timeout::CancelToken::none();
    let outcome = backend
        .solve(&ir, 5000, &cancel)
        .expect("native_ff backend should not error on GF(7)");
    // x_1^2 uniquely determines x_2 (function), so target wire 2's
    // disequality is UNSAT.
    assert!(
        matches!(outcome, SolverResult::Unsat),
        "expected UNSAT for x^2 over GF(7), got {:?}",
        outcome
    );
}

/// Lower the GF(7) system, target wire 2, and inject a benign
/// always-true disjunction `(x0 = 1) ∨ (x2 = 5)`. Wire 0 is pinned to
/// 1, so the clause holds unconditionally — the verdict must stay UNSAT,
/// but a non-empty `disjunctions` forces the backend off the plain GB
/// path. For native this is the CDCL(T) route; for cvc5 it is a real
/// `(or ...)` assertion.
fn ir_with_benign_disjunction() -> picus_smt::poly_ir::PolyIR {
    let r1cs = build_x1_squared_eq_x2();
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 2).expect("lowering should succeed");
    ir.set_target(2);
    // (x0 - 1 = 0) ∨ (x2 - 5 = 0)
    let one = ir.constant(&BigUint::from(1u32));
    let five = ir.constant(&BigUint::from(5u32));
    let x0_minus_1 = ir.ring.sub(ir.ring.var(0), one);
    let x2_minus_5 = ir.ring.sub(ir.ring.var(2), five);
    ir.disjunctions.push(vec![x0_minus_1, x2_minus_5]);
    assert!(!ir.disjunctions.is_empty(), "disjunction must be present");
    ir
}

#[test]
fn native_ff_disjunction_path_agrees_with_gb() {
    let ir = ir_with_benign_disjunction();
    let mut backend = picus_smt::backends::native_ff::NativeFfBackend::new();
    let cancel = picus_core::timeout::CancelToken::none();
    let outcome = backend
        .solve(&ir, 5000, &cancel)
        .expect("native_ff CDCL(T) path should not error");
    assert!(
        matches!(outcome, SolverResult::Unsat),
        "benign disjunction must not change the verdict (expected UNSAT), got {:?}",
        outcome
    );
}

#[cfg(feature = "cvc5")]
#[test]
fn cvc5_ff_consumes_disjunction() {
    let ir = ir_with_benign_disjunction();
    let mut backend = picus_smt::backends::cvc5_ff::Cvc5FfBackend::new();
    let cancel = picus_core::timeout::CancelToken::none();
    let outcome = backend
        .solve(&ir, 5000, &cancel)
        .expect("cvc5_ff should accept the (or ...) assertion");
    assert!(
        matches!(outcome, SolverResult::Unsat),
        "benign disjunction must not change the verdict (expected UNSAT), got {:?}",
        outcome
    );
}
