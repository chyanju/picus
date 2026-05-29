//! Tests for `poly_ir.rs` — `PolyIR` construction, accessors, and
//! lowering from R1CS. Spec-driven where the doc comment is explicit
//! (variable layout, copy symmetry, wire-0 pinning, set_target panic
//! on input wires); structural elsewhere.

use super::*;
use num_bigint::BigUint;
use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};
use std::collections::HashSet;
use std::sync::Arc;

// ─── Test fixtures ────────────────────────────────────────────────

/// Build a minimal in-memory R1csFile with the supplied prime, n_wires,
/// inputs, and constraints (each as triples of (a, b, c) blocks).
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

/// Single-term constraint block: `factor * x_wid`.
fn blk(wid: u32, factor: u32) -> ConstraintBlock {
    ConstraintBlock {
        nnz: 1,
        wire_ids: vec![wid],
        factors: vec![BigUint::from(factor)],
    }
}

/// Empty (zero) constraint block.
fn zero_blk() -> ConstraintBlock {
    ConstraintBlock {
        nnz: 0,
        wire_ids: vec![],
        factors: vec![],
    }
}

/// GF(7) prime.
fn p7() -> BigUint {
    BigUint::from(7u32)
}

/// Build a small PolyIR over GF(p) with `n_wires` wires, no constraints,
/// the inputs from `inputs`, and a target signal. Convenient for unit
/// tests of accessors that don't need constraint lowering.
fn empty_ir(p: BigUint, n_wires: usize, inputs: Vec<usize>, target: usize) -> PolyIR {
    let r1cs = make_r1cs(p, n_wires as u32, inputs, Vec::new());
    let known = HashSet::new();
    r1cs_to_poly_ir(&r1cs, &known, target).expect("empty ir builds")
}

// ─── orig_var / alt_var / var_to_wire ────────────────────────────

#[test]
fn prop_orig_var_is_wire_index() {
    // Doc spec: "Variable index `i` (for `i < n_wires`) is the original
    // copy `x_i`".
    let ir = empty_ir(p7(), 4, vec![0], 1);
    assert_eq!(ir.orig_var(0), 0);
    assert_eq!(ir.orig_var(1), 1);
    assert_eq!(ir.orig_var(3), 3);
}

#[test]
fn prop_alt_var_is_n_wires_plus_wire() {
    // Doc spec: "index `n_wires + i` is the alt copy `y_i`".
    let ir = empty_ir(p7(), 4, vec![0], 1);
    assert_eq!(ir.alt_var(0), 4);
    assert_eq!(ir.alt_var(1), 5);
    assert_eq!(ir.alt_var(3), 7);
}

#[test]
fn prop_var_to_wire_round_trips_both_copies() {
    // Doc spec: `var_to_wire(orig_var(w)) == w` and
    //          `var_to_wire(alt_var(w)) == w`.
    let ir = empty_ir(p7(), 4, vec![0], 1);
    for w in 0..4 {
        assert_eq!(ir.var_to_wire(ir.orig_var(w)), w);
        assert_eq!(ir.var_to_wire(ir.alt_var(w)), w);
    }
}

// ─── x_name / y_name ─────────────────────────────────────────────

#[test]
fn prop_x_name_y_name_match_layout() {
    // Doc spec: x_i / y_i are the canonical names. r1cs_to_poly_ir
    // pushes "x{i}" then "y{i}" in order.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    assert_eq!(ir.x_name(0), "x0");
    assert_eq!(ir.x_name(2), "x2");
    assert_eq!(ir.y_name(0), "y0");
    assert_eq!(ir.y_name(2), "y2");
}

// ─── set_target ──────────────────────────────────────────────────

#[test]
fn prop_set_target_updates_disequality() {
    // Doc spec: "Updates `target_signal` and rebuilds `disequalities`
    // to point at the new target's `(x, y)` pair."
    let mut ir = empty_ir(p7(), 4, vec![0], 1);
    ir.set_target(2);
    assert_eq!(ir.target_signal, 2);
    assert_eq!(ir.disequalities.len(), 1);
    let (a, b) = ir.disequalities[0];
    assert_eq!(a, ir.orig_var(2));
    assert_eq!(b, ir.alt_var(2));
}

#[test]
#[should_panic(expected = "uniqueness target must not be an input wire")]
fn prop_set_target_panics_on_input_wire() {
    // Doc spec: "guard the public API so a direct caller can't silently
    // get a false UNSAFE."
    let mut ir = empty_ir(p7(), 4, vec![0, 2], 1);
    ir.set_target(2); // wire 2 is an input ⇒ assert!
}

// ─── add_known_wire ─────────────────────────────────────────────

#[test]
fn prop_add_known_wire_emits_xy_equality_for_noninput() {
    // Doc spec: "Appends `x_w - y_w = 0` to `equalities`."
    let mut ir = empty_ir(p7(), 4, vec![0], 1);
    let before = ir.equalities.len();
    ir.add_known_wire(2);
    assert!(ir.known_signals.contains(&2));
    assert_eq!(ir.equalities.len(), before + 1, "x_2 - y_2 = 0 appended");
}

#[test]
fn prop_add_known_wire_no_equality_for_input() {
    // Doc spec: "Input wires reuse `x_i` across both copies at
    // lowering, so only non-input wires need a fresh `x_w - y_w = 0`."
    let mut ir = empty_ir(p7(), 4, vec![0, 3], 1);
    let before = ir.equalities.len();
    ir.add_known_wire(3); // input ⇒ no new equality
    assert!(ir.known_signals.contains(&3));
    assert_eq!(ir.equalities.len(), before, "no equality for input wire");
}

#[test]
fn prop_add_known_wire_idempotent() {
    // Second call with the same wire should not push a second equality
    // (HashSet::insert returns false).
    let mut ir = empty_ir(p7(), 4, vec![0], 1);
    ir.add_known_wire(2);
    let mid = ir.equalities.len();
    ir.add_known_wire(2);
    assert_eq!(ir.equalities.len(), mid, "second add is a no-op");
}

// ─── linear_term / constant ─────────────────────────────────────

#[test]
fn test_linear_term_constructs_nonzero_poly() {
    // Structural: builds without panicking and the result is non-zero.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let t = ir.linear_term(&BigUint::from(3u32), 1);
    assert!(!ir.ring.is_zero(&t));
}

#[test]
fn test_linear_term_zero_coeff_is_zero_poly() {
    // 0 * x_1 = 0 in GF(7).
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let t = ir.linear_term(&BigUint::from(0u32), 1);
    assert!(ir.ring.is_zero(&t));
}

#[test]
fn test_linear_term_coeff_reduced_mod_p() {
    // In GF(7), 7 ≡ 0; the term 7*x_1 must equal 0.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let t = ir.linear_term(&BigUint::from(7u32), 1);
    assert!(ir.ring.is_zero(&t), "7*x_1 over GF(7) should be 0");
}

#[test]
fn test_constant_zero_is_zero_poly() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let c = ir.constant(&BigUint::from(0u32));
    assert!(ir.ring.is_zero(&c));
}

#[test]
fn test_constant_nonzero() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let c = ir.constant(&BigUint::from(3u32));
    assert!(!ir.ring.is_zero(&c));
}

// ─── poly_terms / poly_terms_idx (consistency) ──────────────────

#[test]
fn prop_poly_terms_and_idx_agree_on_term_count() {
    // Spec: both iterators yield one entry per nonzero term.
    let ir = empty_ir(p7(), 4, vec![0], 1);
    let a = ir.linear_term(&BigUint::from(2u32), 1);
    let b = ir.linear_term(&BigUint::from(3u32), 2);
    let poly = ir.ring.add(a, b);
    let n_named: usize = ir.poly_terms(&poly).count();
    let n_idx: usize = ir.poly_terms_idx(&poly).count();
    assert_eq!(n_named, n_idx);
    assert!(n_named >= 1);
}

#[test]
fn prop_poly_terms_idx_constant_has_empty_var_list() {
    // Doc spec: "a constant term yields an empty `Vec`".
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let c = ir.constant(&BigUint::from(5u32));
    let terms: Vec<_> = ir.poly_terms_idx(&c).collect();
    assert_eq!(terms.len(), 1);
    let (coeff, vars) = &terms[0];
    assert_eq!(coeff, &BigUint::from(5u32));
    assert!(vars.is_empty(), "constant term has empty var list");
}

#[test]
fn prop_poly_terms_idx_linear_has_single_var_degree_one() {
    // Doc spec: linear monomial `x` yields `[(x_idx, 1)]`.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let t = ir.linear_term(&BigUint::from(2u32), 1);
    let terms: Vec<_> = ir.poly_terms_idx(&t).collect();
    assert_eq!(terms.len(), 1);
    let (_, vars) = &terms[0];
    assert_eq!(vars.len(), 1);
    let (idx, exp) = vars[0];
    assert_eq!(idx, 1);
    assert_eq!(exp, 1);
}

#[test]
fn prop_poly_terms_named_for_quadratic_expands_each_degree() {
    // Doc spec for `poly_terms`: "`x*x` ⇒ `["x", "x"]`".
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let x1 = ir.linear_term(&BigUint::from(1u32), 1);
    let sq = ir.ring.mul(ir.ring.clone_poly(&x1), x1);
    let terms: Vec<_> = ir.poly_terms(&sq).collect();
    assert_eq!(terms.len(), 1);
    let (_, atoms) = &terms[0];
    assert_eq!(atoms.len(), 2, "x_1*x_1 ⇒ two atoms");
    assert_eq!(atoms[0], atoms[1]);
}

// ─── r1cs_to_poly_ir ────────────────────────────────────────────

#[test]
fn prop_r1cs_to_poly_ir_target_out_of_bounds_returns_err() {
    // Doc spec: target_signal ≥ n_wires must return WireOutOfBounds.
    let r1cs = make_r1cs(p7(), 3, vec![0], Vec::new());
    let r = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 3);
    assert!(matches!(r, Err(LowerError::WireOutOfBounds { .. })));
}

#[test]
fn prop_r1cs_to_poly_ir_target_equal_n_wires_is_err() {
    // Edge: equality is OOB (wires are 0-indexed up to n_wires-1).
    let r1cs = make_r1cs(p7(), 2, vec![0], Vec::new());
    assert!(r1cs_to_poly_ir(&r1cs, &HashSet::new(), 2).is_err());
}

#[test]
fn prop_r1cs_to_poly_ir_ring_has_2n_vars() {
    // Doc spec: "the ring carries `2 * n_wires` variables".
    let r1cs = make_r1cs(p7(), 5, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    assert_eq!(ir.ring.n_vars(), 10);
}

#[test]
fn prop_r1cs_to_poly_ir_var_names_layout() {
    // First `n_wires` are `xN`, then `n_wires` are `yN`.
    let r1cs = make_r1cs(p7(), 3, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    let names = ir.ring.var_names();
    assert_eq!(names, &["x0", "x1", "x2", "y0", "y1", "y2"]);
}

#[test]
fn prop_r1cs_to_poly_ir_emits_wire0_pinned_to_one() {
    // Doc spec: "Wire 0 pinned to 1. … backends still observe `x_0`
    // as a ring variable and need an equality to pin it." Even with
    // no source constraints, an `x_0 - 1 = 0` equality must appear.
    let r1cs = make_r1cs(p7(), 3, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(
        !ir.equalities.is_empty(),
        "must emit at least the x_0 = 1 pin"
    );
}

#[test]
fn prop_r1cs_to_poly_ir_disequality_at_target() {
    // Doc spec: "the general-purpose GB query fields" populate a
    // single disequality `(target_x_idx, target_y_idx)`.
    let r1cs = make_r1cs(p7(), 4, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 2).unwrap();
    assert_eq!(ir.disequalities, vec![(2, 6)]);
}

#[test]
fn prop_r1cs_to_poly_ir_small_prime_enables_field_polys() {
    // Doc spec: "field polys enabled iff the prime is small" — gate
    // is `prime <= 1000`. GF(7) is small.
    let r1cs = make_r1cs(p7(), 3, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(ir.add_field_polys, "GF(7) ≤ 1000 ⇒ add_field_polys=true");
}

#[test]
fn prop_r1cs_to_poly_ir_big_prime_disables_field_polys() {
    // Boundary: BN128 prime is way above 1000.
    let big = picus_r1cs::bn128_prime().clone();
    let r1cs = make_r1cs(big, 3, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(
        !ir.add_field_polys,
        "BN128 > 1000 ⇒ add_field_polys=false"
    );
}

#[test]
fn prop_r1cs_to_poly_ir_threshold_at_1000() {
    // Exact boundary: prime == 1000 must satisfy `prime <= 1000` and
    // enable field polys (note 1000 is not prime, but the gate uses
    // BigUint comparison, not primality). Test just verifies the
    // `<=` direction.
    let p = BigUint::from(1000u32);
    let r1cs = make_r1cs(p, 3, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(ir.add_field_polys, "1000 ≤ 1000 boundary");
}

#[test]
fn prop_r1cs_to_poly_ir_above_threshold_disables_field_polys() {
    // 1001 exceeds the gate.
    let p = BigUint::from(1001u32);
    let r1cs = make_r1cs(p, 3, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(!ir.add_field_polys, "1001 > 1000 boundary");
}

#[test]
fn prop_r1cs_to_poly_ir_inputs_propagated() {
    let r1cs = make_r1cs(p7(), 5, vec![0, 1, 3], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 2).unwrap();
    for w in [0usize, 1, 3] {
        assert!(ir.input_indices.contains(&w), "wire {} is an input", w);
    }
    assert!(!ir.input_indices.contains(&2));
    assert!(!ir.input_indices.contains(&4));
}

#[test]
fn prop_r1cs_to_poly_ir_known_signals_seeded_from_argument() {
    let mut known = HashSet::new();
    known.insert(3usize);
    let r1cs = make_r1cs(p7(), 5, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &known, 2).unwrap();
    assert!(ir.known_signals.contains(&3));
}

#[test]
fn prop_r1cs_to_poly_ir_copy_symmetry_emits_two_constraints_per_block() {
    // Doc spec (copy-symmetry invariant): "every R1CS constraint is
    // lowered into BOTH copies below". For one non-input constraint
    // we must see at least two equalities (orig + alt) above the
    // wire-0 pin.
    //
    // Build: (1 * x_1) * (1 * x_2) = (1 * x_3) over wires {0..4}
    let cons = Constraint {
        a: blk(1, 1),
        b: blk(2, 1),
        c: blk(3, 1),
    };
    let r1cs = make_r1cs(p7(), 4, vec![0], vec![cons]);
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    // wire-0 pin (1) + orig (1) + alt (1) = 3
    assert!(
        ir.equalities.len() >= 3,
        "expected ≥3 equalities (orig + alt + pin), got {}",
        ir.equalities.len()
    );
}

#[test]
fn prop_r1cs_to_poly_ir_zero_constraint_dropped() {
    // 0 * 0 = 0 lowers to the zero polynomial; `constraint_to_poly`
    // returns Ok(None) so it should NOT be appended.
    let cons = Constraint {
        a: zero_blk(),
        b: zero_blk(),
        c: zero_blk(),
    };
    let r1cs = make_r1cs(p7(), 3, vec![0], vec![cons]);
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    // Only the wire-0 pin should be present.
    assert_eq!(
        ir.equalities.len(),
        1,
        "zero constraint dropped, only x_0 = 1 remains"
    );
}

#[test]
fn prop_r1cs_to_poly_ir_out_of_bounds_wire_id_returns_err() {
    // `block_to_linear` must reject `wid >= n_wires`. Build a
    // constraint referencing wire 99 when only 3 wires exist.
    let cons = Constraint {
        a: blk(99, 1),
        b: blk(1, 1),
        c: zero_blk(),
    };
    let r1cs = make_r1cs(p7(), 3, vec![0], vec![cons]);
    let r = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1);
    assert!(matches!(r, Err(LowerError::WireOutOfBounds { .. })));
}

#[test]
fn prop_r1cs_to_poly_ir_assignments_and_bitsums_empty_after_lowering() {
    // Doc spec: R1CS lowering does NOT populate assignments / bitsums
    // (those are for SMT2/CDCL(T) producers).
    let r1cs = make_r1cs(p7(), 3, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(ir.assignments.is_empty());
    assert!(ir.bitsums.is_empty());
    assert!(ir.disjunctions.is_empty());
}

#[test]
fn prop_r1cs_to_poly_ir_n_wires_recorded() {
    let r1cs = make_r1cs(p7(), 7, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap();
    assert_eq!(ir.n_wires, 7);
}

#[test]
fn prop_r1cs_to_poly_ir_target_signal_recorded() {
    let r1cs = make_r1cs(p7(), 5, vec![0], Vec::new());
    let ir = r1cs_to_poly_ir(&r1cs, &HashSet::new(), 3).unwrap();
    assert_eq!(ir.target_signal, 3);
}

// Sweep small primes — field arithmetic invariants hold for any prime.
#[test]
fn prop_constant_reduces_modulo_prime_across_primes() {
    for &p in &[2u32, 7, 101] {
        let ir = empty_ir(BigUint::from(p), 3, vec![0], 1);
        // p ≡ 0 mod p, so `constant(p)` must be zero.
        let c = ir.constant(&BigUint::from(p));
        assert!(ir.ring.is_zero(&c), "p={} mod p ≠ 0?", p);
        // p+1 ≡ 1 (nonzero) mod p.
        let c1 = ir.constant(&BigUint::from(p + 1));
        assert!(!ir.ring.is_zero(&c1), "p={} ⇒ (p+1) mod p = 1", p);
    }
}
