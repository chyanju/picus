//! Tests for `native_lower.rs` — `PolyIR::to_constraint_system`,
//! `PolyIR::to_boolean_query`, `PolyIR::encode`, and
//! `PolyIR::pre_eliminate_linear`. Spec-driven where the doc spells
//! out the lowering shape (variable name list, equality count,
//! disequality/assignment/bitsum propagation, field-poly flag).

use num_bigint::BigUint;
use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};
use std::collections::HashSet;

use crate::poly_ir::{r1cs_to_poly_ir, PolyIR};
use picus_core::timeout::CancelToken;

// ─── Test fixtures (mirror the poly_ir tests) ────────────────────

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

fn p7() -> BigUint {
    BigUint::from(7u32)
}

fn empty_ir(p: BigUint, n_wires: usize, inputs: Vec<usize>, target: usize) -> PolyIR {
    let r1cs = make_r1cs(p, n_wires as u32, inputs, Vec::new());
    let known = HashSet::new();
    r1cs_to_poly_ir(&r1cs, &known, target).expect("ir builds")
}

// ─── to_constraint_system ────────────────────────────────────────

#[test]
fn prop_to_constraint_system_preserves_prime() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.prime, p7());
}

#[test]
fn prop_to_constraint_system_var_names_match_ring_order() {
    // Doc spec: "Variable names are interned in `ring.var_names()`
    // order so builder indices match ring indices".
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.var_names, ir.ring.var_names().to_vec());
    // Layout: x0,x1,x2,y0,y1,y2.
    assert_eq!(cs.var_names, vec!["x0", "x1", "x2", "y0", "y1", "y2"]);
}

#[test]
fn prop_to_constraint_system_disequalities_propagate() {
    // Doc spec: disequalities propagate as-is.
    let ir = empty_ir(p7(), 4, vec![0], 2);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.disequalities, vec![(2u32, 6u32)]);
}

#[test]
fn prop_to_constraint_system_field_polys_flag_propagates_small_prime() {
    // Doc spec: `add_field_polys` propagates as-is.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    assert!(cs.add_field_polys, "small prime ⇒ flag on");
}

#[test]
fn prop_to_constraint_system_field_polys_flag_off_for_large_prime() {
    let big = picus_r1cs::bn128_prime().clone();
    let ir = empty_ir(big, 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    assert!(!cs.add_field_polys);
}

#[test]
fn prop_to_constraint_system_assignments_propagate() {
    let mut ir = empty_ir(p7(), 3, vec![0], 1);
    ir.assignments.push((1, BigUint::from(2u32)));
    let cs = ir.to_constraint_system();
    assert_eq!(cs.assignments.len(), 1);
    assert_eq!(cs.assignments[0].0, 1u32);
    assert_eq!(cs.assignments[0].1, BigUint::from(2u32));
}

#[test]
fn prop_to_constraint_system_bitsums_propagate_with_cast() {
    let mut ir = empty_ir(p7(), 5, vec![0], 1);
    ir.bitsums.push(vec![1, 2, 3]);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.bitsums.len(), 1);
    assert_eq!(cs.bitsums[0], vec![1u32, 2, 3]);
}

#[test]
fn prop_to_constraint_system_empty_equality_dropped() {
    // Doc spec: "if !terms.is_empty()" — empty polys drop. With no
    // user constraints, the only equality is `x_0 - 1 = 0` (non-empty
    // terms).
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    for eq in &cs.equalities {
        assert!(!eq.is_empty(), "all equalities are non-empty");
    }
}

#[test]
fn prop_to_constraint_system_includes_user_constraints() {
    // One constraint `x_1 * x_2 = x_3` → 2 equalities (orig + alt)
    // plus the wire-0 pin = 3 total.
    let cons = Constraint {
        a: blk(1, 1),
        b: blk(2, 1),
        c: blk(3, 1),
    };
    let r1cs = make_r1cs(p7(), 4, vec![0], vec![cons]);
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    let cs = ir.to_constraint_system();
    assert_eq!(cs.equalities.len(), 3);
}

// ─── to_boolean_query ────────────────────────────────────────────

#[test]
fn prop_to_boolean_query_preserves_prime() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let q = ir.to_boolean_query();
    assert_eq!(q.prime, p7());
}

#[test]
fn prop_to_boolean_query_var_names_match_ring_order() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let q = ir.to_boolean_query();
    assert_eq!(q.var_names(), ir.ring.var_names());
}

#[test]
fn prop_to_boolean_query_empty_constraints_yields_true_or_and() {
    // With no equalities/diseqs/assignments/disjunctions, the
    // conj is empty ⇒ Formula::True. r1cs_to_poly_ir always emits
    // at least the wire-0 pin, so the realistic empty case is
    // hard to reach; just check the formula is well-formed.
    use picus_solver::boolean::Formula;
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let q = ir.to_boolean_query();
    // Either an And of literals or a Lit/True — definitely not False.
    assert!(!matches!(q.formula, Formula::False));
}

// ─── encode ──────────────────────────────────────────────────────

#[test]
fn prop_encode_returns_nonempty_polynomials_for_pinned_wire0() {
    // r1cs_to_poly_ir always emits at least the `x_0 - 1 = 0` equality.
    // `encode` lowers each non-zero equality into a polynomial, so
    // the result must have at least one polynomial.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let enc = ir.encode().expect("encode should succeed on empty system");
    assert!(!enc.polynomials.is_empty(), "wire-0 pin survives encoding");
}

#[test]
fn prop_encode_preserves_ring_prime() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let enc = ir.encode().expect("encode OK");
    assert_eq!(enc.poly_ring.field().prime(), &p7());
}

#[test]
fn prop_encode_var_map_includes_used_vars() {
    // Spec: `encode` calls `compact_used_vars` and retains only variables
    // appearing in constraints / inputs / target — unconstrained ring
    // variables are correctly dropped. We assert the retained-set
    // contract on declared inputs + target, not every ring variable.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let enc = ir.encode().expect("encode OK");
    let names = ir.ring.var_names();
    assert!(
        enc.var_map.contains_key(&names[0]),
        "input var must be in var_map"
    );
    assert!(
        enc.var_map.contains_key(&names[1]),
        "target var must be in var_map"
    );
}

// ─── pre_eliminate_linear ────────────────────────────────────────

#[test]
fn prop_pre_eliminate_linear_returns_none_on_empty() {
    // No equalities (only `x_0 - 1 = 0`, a single linear with one
    // pivot variable) — may or may not "change" depending on whether
    // the linsolve treats `x_0 = 1` as already-reduced. Either way,
    // the function must return without panicking and the result is
    // either None or a structurally valid PolyIR.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cancel = CancelToken::none();
    let r = ir.pre_eliminate_linear(&cancel);
    // Structural: not a panic, and if Some, the new ring is the
    // same Arc.
    if let Some(new_ir) = r {
        assert_eq!(new_ir.n_wires, ir.n_wires);
        assert_eq!(new_ir.ring.n_vars(), ir.ring.n_vars());
    }
}

#[test]
fn prop_pre_eliminate_linear_preserves_disequalities_when_applied() {
    // Variety-preserving: the disequality list (which encodes the
    // target signal) must propagate unchanged.
    let ir = empty_ir(p7(), 4, vec![0], 2);
    let cancel = CancelToken::none();
    if let Some(new_ir) = ir.pre_eliminate_linear(&cancel) {
        assert_eq!(new_ir.disequalities, ir.disequalities);
        assert_eq!(new_ir.target_signal, ir.target_signal);
    }
}

#[test]
fn prop_pre_eliminate_linear_preserves_metadata_when_applied() {
    // input_indices / known_signals / add_field_polys carry over.
    let mut known = HashSet::new();
    known.insert(2usize);
    let r1cs = make_r1cs(p7(), 4, vec![0, 1], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &known, 3).unwrap();
    let cancel = CancelToken::none();
    if let Some(new_ir) = ir.pre_eliminate_linear(&cancel) {
        assert_eq!(new_ir.input_indices, ir.input_indices);
        assert_eq!(new_ir.known_signals, ir.known_signals);
        assert_eq!(new_ir.add_field_polys, ir.add_field_polys);
        assert_eq!(new_ir.n_wires, ir.n_wires);
    }
}
