//! Unit tests for the BIM (Big Integer Multiply) propagation lemma.
//!
//! Spec (from the file-top doc):
//!   Collects every linear, homogeneous, constant-free equality.
//!   If the variables form a square invertible system over GF(p) AND
//!   every variable is currently unknown, mark each variable known.
//!
//! Notes from the doc:
//!   * R1CS-lowered input is normally inert here: both copies map to the
//!     same wire under `var_to_wire`, producing duplicate rows ⇒
//!     singular matrix ⇒ no promotion.
//!   * Variable count must MATCH equation count (square system).
//!   * Determinant zero ⇒ no promotion.

use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;
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

// ── tests ──────────────────────────────────────────────────────────

/// Spec: lemma is registered in the inventory under name `"bim"`.
#[test]
fn prop_bim_lemma_name_is_bim() {
    let lemma = BimLemma::default();
    assert_eq!(lemma.name(), "bim");
}

/// Spec: empty IR ⇒ no progress (nothing to collect).
#[test]
fn prop_bim_no_progress_on_empty_equalities() {
    // Build any trivial R1CS, then clear equalities.
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
        c: block(&[(2, 1)]),
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
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 2).expect("lowering should succeed");
    ir.equalities.clear();

    let mut lemma = BimLemma::default();
    let mut known_set: HashSet<usize> = HashSet::new();
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
}

/// Spec note (from the doc): "R1CS-lowered input is effectively inert
/// here" — the orig+alt copies produce identical wire-keyed rows after
/// var_to_wire collapse, and a square matrix with duplicate rows has
/// det = 0. So even on a system that LOOKS like it should fire (square
/// linear-homogeneous over both copies), it must NOT.
#[test]
fn prop_bim_inert_on_r1cs_lowered_input() {
    // x_1 + x_2 = 0  AND  x_1 - x_2 = 0  (over GF(7)).
    // Both rows duplicated by lowering ⇒ singular ⇒ no progress.
    let p_minus_1 = 6u32; // -1 mod 7
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 2,
    };
    let constraints = vec![
        // (x_1 + x_2) * 1 = 0
        Constraint {
            a: block(&[(1, 1), (2, 1)]),
            b: block(&[(0, 1)]),
            c: empty_block(),
        },
        // (x_1 - x_2) * 1 = 0  (i.e. coefficient 6 on x_2 mod 7 = -1)
        Constraint {
            a: block(&[(1, 1), (2, p_minus_1)]),
            b: block(&[(0, 1)]),
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
            labels: vec![0, 1, 2],
        },
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(2);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    // Doc says: "A square system with duplicate rows is singular
    // (det = 0 below), so the lemma declines."
    assert!(
        !progress,
        "BIM must decline on R1CS-lowered input (duplicate rows ⇒ det=0)"
    );
    assert!(unknown.contains(&1));
    assert!(unknown.contains(&2));
}

/// Spec: linear-homogeneous polynomials with a non-zero CONSTANT are
/// filtered out by `collect_linear_homogeneous`. A system that would be
/// square-invertible if not for a stray constant must NOT fire.
#[test]
fn prop_bim_rejects_nonzero_constant_term() {
    // (x_1) * 1 = 1: this is `x_1 - 1 = 0`, which contains a non-zero
    // constant. `collect_linear_homogeneous` drops it → no rows → no fire.
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 2,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 2,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: block(&[(0, 1)]),
    }];
    let r1cs = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1],
        },
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(!progress, "non-zero constant term must disqualify the equality");
    assert!(unknown.contains(&1));
}

/// Spec: nonlinear (degree ≥ 2) terms exclude an equality from the
/// linear-homogeneous collection.
#[test]
fn prop_bim_rejects_nonlinear_equality() {
    // x_1 * x_1 = x_2 has a quadratic term ⇒ not linear-homogeneous.
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
        c: block(&[(2, 1)]),
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
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(!progress, "nonlinear equality must NOT contribute to BIM matrix");
}

/// Spec: BIM only fires when EVERY variable in the collected equations
/// is currently unknown. If even one is already known, the system is
/// not "purely unknown" and the lemma must decline.
#[test]
fn prop_bim_declines_when_some_var_already_known() {
    // Build a non-R1CS-lowered IR by directly mutating equalities. Use
    // a simple base R1CS to bootstrap a ring, then push a single
    // invertible linear equality `x_1 + x_2 = 0` into equalities.
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
    // Trivial constraint just to give us a ring; we'll overwrite equalities.
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: block(&[(2, 1)]),
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
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 2).expect("lowering should succeed");

    // Construct a 1x1 invertible system: just `x_1 = 0` (the polynomial
    // `x_1`). collect_linear_homogeneous accepts it; n=1 and det=1; BUT
    // we mark wire 1 as already KNOWN, so the gate `unknown.contains` fails.
    ir.equalities.clear();
    let x1 = ir.ring.var(1); // x_1 polynomial
    ir.equalities.push(x1);

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    known_set.insert(1); // wire 1 already known
    let mut unknown: HashSet<usize> = HashSet::new();
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(
        !progress,
        "BIM must decline when any matrix variable is already known"
    );
}

/// Spec: square invertible system (n equations in n unknown wires)
/// over GF(p) ⇒ every wire promoted to known.
///
/// We bypass the R1CS-lowering duplicate-rows issue by directly
/// constructing a fresh, non-duplicated, linear-homogeneous system in
/// the IR's `equalities`. Take `x_1 = 0`: 1 equation, 1 unknown wire,
/// det = 1 ≠ 0 ⇒ wire 1 must be promoted.
#[test]
fn prop_bim_promotes_invertible_singleton_system() {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 2,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 2,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: empty_block(),
    }];
    let r1cs = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1],
        },
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    // Replace lowered equalities with a single `x_1 = 0` polynomial so
    // the R1CS duplicate-rows issue does not apply.
    ir.equalities.clear();
    let x1 = ir.ring.var(1);
    ir.equalities.push(x1);

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(progress, "1×1 invertible system must fire");
    assert!(known_set.contains(&1));
    assert!(!unknown.contains(&1));
}

/// Spec: square 2×2 invertible system over GF(7). System
///   x_1 + x_2 = 0
///   x_1 + 2 x_2 = 0
/// Determinant = 1·2 - 1·1 = 1 ≠ 0 ⇒ promote both wires.
#[test]
fn prop_bim_promotes_2x2_invertible_system() {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
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
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    // Replace with x_1 + x_2 = 0 and x_1 + 2 x_2 = 0.
    ir.equalities.clear();
    let two = ir.constant(&BigUint::from(2u32));
    let eq1 = ir.ring.add(ir.ring.var(1), ir.ring.var(2));
    let eq2 = ir.ring.add(ir.ring.var(1), ir.ring.mul(two, ir.ring.var(2)));
    ir.equalities.push(eq1);
    ir.equalities.push(eq2);

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(2);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(progress, "2×2 invertible system must fire");
    assert!(known_set.contains(&1));
    assert!(known_set.contains(&2));
    assert!(!unknown.contains(&1));
    assert!(!unknown.contains(&2));
}

/// Spec: rectangular system (more equations than variables) — variable
/// count != equation count ⇒ no fire. Conversely, more variables than
/// equations — also no fire.
#[test]
fn prop_bim_declines_when_not_square() {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 4,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 4,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: empty_block(),
    }];
    let r1cs = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1, 2, 3],
        },
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    // One equation `x_1 + x_2 + x_3 = 0`, three unknown wires ⇒ n=3,
    // eqs=1, not square.
    ir.equalities.clear();
    let mut eq = ir.ring.var(1);
    eq = ir.ring.add(eq, ir.ring.var(2));
    eq = ir.ring.add(eq, ir.ring.var(3));
    ir.equalities.push(eq);

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(2);
    unknown.insert(3);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(
        !progress,
        "non-square (eqs={}, vars=3) must NOT fire",
        ir.equalities.len()
    );
}

/// Spec: singular square system (det = 0 over GF(p)) ⇒ no fire.
///   x_1 + x_2 = 0
///   2 x_1 + 2 x_2 = 0   (linearly dependent ⇒ det = 0)
#[test]
fn prop_bim_declines_on_singular_square_system() {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
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
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    ir.equalities.clear();
    let two = ir.constant(&BigUint::from(2u32));
    let eq1 = ir.ring.add(ir.ring.var(1), ir.ring.var(2));
    let eq2 = ir.ring.add(
        ir.ring.mul(ir.constant(&BigUint::from(2u32)), ir.ring.var(1)),
        ir.ring.mul(two, ir.ring.var(2)),
    );
    ir.equalities.push(eq1);
    ir.equalities.push(eq2);

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(2);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(!progress, "singular square system must NOT promote");
    assert!(unknown.contains(&1));
    assert!(unknown.contains(&2));
}

/// Spec: small-prime sweep — the BIM matrix arithmetic is mod p, and
/// the lemma must remain sound across primes. Use the 1×1 invertible
/// `x_1 = 0` shape over multiple primes and check it fires every time.
#[test]
fn prop_bim_invertible_singleton_sweeps_small_primes() {
    for &p in &[2u32, 7, 101] {
        let header = HeaderSection {
            field_size: 32,
            prime_number: BigUint::from(p),
            n_wires: 2,
            n_pub_out: 0,
            n_pub_in: 0,
            n_prv_in: 0,
            n_labels: 2,
            m_constraints: 1,
        };
        let constraints = vec![Constraint {
            a: block(&[(1, 1)]),
            b: block(&[(0, 1)]),
            c: empty_block(),
        }];
        let r1cs = R1csFile {
            magic: *b"r1cs",
            version: 1,
            n_sections: 3,
            header,
            constraints: ConstraintSection { constraints },
            w2l: W2lSection {
                labels: vec![0, 1],
            },
            inputs: vec![0],
            outputs: vec![],
        };
        let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
        let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");
        ir.equalities.clear();
        let x1 = ir.ring.var(1);
        ir.equalities.push(x1);

        let mut known_set: HashSet<usize> = HashSet::new();
        known_set.insert(0);
        let mut unknown: HashSet<usize> = HashSet::new();
        unknown.insert(1);
        let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
        let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
        let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
        let mut lemma = BimLemma::default();
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
        assert!(progress, "BIM should fire on x_1=0 over GF({})", p);
        assert!(known_set.contains(&1), "wire 1 promoted over GF({})", p);
    }
}

// ── extra coverage: matrix_det_mod internals ───────────────────────

/// Coverage: pivot-swap sign-flip path in `matrix_det_mod`.
/// System:
///   x_1·0 + x_2·1 = 0   (row 0: leading column is zero)
///   x_1·1 + x_2·0 = 0   (row 1: leading column nonzero)
/// First column's pivot must be found at row 1 (not row 0) → swap →
/// `sign_flip = true`. Det = 1·1 = 1; after negation det = p-1 ≠ 0 ⇒
/// the system is invertible and both wires are promoted.
#[test]
fn test_bim_promotes_with_pivot_swap_sign_flip() {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: empty_block(),
    }];
    let r1cs = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1, 2] },
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    // The matrix-row order depends on hash iteration of `all_sigs`, so
    // build a system where the relative ordering forces a non-trivial
    // pivot search: x_2 = 0 (row references only x_2) and x_1 = 0 (row
    // references only x_1). For whichever ordering of (wire 1, wire 2)
    // ends up as columns 0/1, ONE of the two rows has a zero in col 0
    // and the matrix algorithm must scan for the nonzero pivot.
    ir.equalities.clear();
    let x1 = ir.ring.var(1);
    let x2 = ir.ring.var(2);
    ir.equalities.push(x2); // x_2 = 0
    ir.equalities.push(x1); // x_1 = 0

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(2);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(progress, "diagonal/anti-diagonal system must still be invertible");
    assert!(known_set.contains(&1));
    assert!(known_set.contains(&2));
}

/// Coverage: subtractive wrap-around branch in `matrix_det_mod`'s
/// Gauss step. System over GF(7):
///   x_1 + x_2 = 0
///   3 x_1 + x_2 = 0
/// Det = 1·1 - 3·1 = -2 ≡ 5 (mod 7) ≠ 0 ⇒ invertible.
/// During elimination on row 1: factor = 3, sub = 3·1 = 3 > m[1][1] = 1
/// for col 1 → the `m[row][j] >= sub` else-branch is taken (the
/// "subtract from p" wrap path).
#[test]
fn test_bim_promotes_via_wrap_subtraction_branch() {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: empty_block(),
    }];
    let r1cs = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1, 2] },
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    ir.equalities.clear();
    let three = ir.constant(&BigUint::from(3u32));
    let eq1 = ir.ring.add(ir.ring.var(1), ir.ring.var(2));
    let eq2 = ir.ring.add(ir.ring.mul(three, ir.ring.var(1)), ir.ring.var(2));
    ir.equalities.push(eq1);
    ir.equalities.push(eq2);

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(2);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(progress, "wrap-subtraction case must still report invertible");
    assert!(known_set.contains(&1));
    assert!(known_set.contains(&2));
}

/// Coverage: the m[row][col].is_zero() `continue` branch inside the
/// elimination loop. System with a leading 0 in row 2's column 0 of a
/// 3x3 system:
///   x_1 + x_2          = 0   (deps: 1, 2)
///   x_1 +       x_3    = 0   (deps: 1, 3)
///         x_2 +  x_3   = 0   (deps: 2, 3)
/// Det of [[1,1,0],[1,0,1],[0,1,1]] = -2 ≡ 5 mod 7 ≠ 0.
#[test]
fn test_bim_promotes_3x3_skips_zero_pivot_rows() {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires: 4,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 4,
        m_constraints: 1,
    };
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: empty_block(),
    }];
    let r1cs = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1, 2, 3] },
        inputs: vec![0],
        outputs: vec![],
    };
    let known: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let mut ir = r1cs_to_poly_ir(&r1cs, &known, 1).expect("lowering should succeed");

    ir.equalities.clear();
    let e1 = ir.ring.add(ir.ring.var(1), ir.ring.var(2));
    let e2 = ir.ring.add(ir.ring.var(1), ir.ring.var(3));
    let e3 = ir.ring.add(ir.ring.var(2), ir.ring.var(3));
    ir.equalities.push(e1);
    ir.equalities.push(e2);
    ir.equalities.push(e3);

    let mut known_set: HashSet<usize> = HashSet::new();
    known_set.insert(0);
    let mut unknown: HashSet<usize> = HashSet::new();
    unknown.insert(1);
    unknown.insert(2);
    unknown.insert(3);
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let mut learned: Vec<picus_core::poly::IrPoly> = Vec::new();
    let mut learned_disj: Vec<Vec<picus_core::poly::IrPoly>> = Vec::new();
    let mut lemma = BimLemma::default();
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
    assert!(progress, "3x3 sparse invertible system must fire");
    assert!(known_set.contains(&1));
    assert!(known_set.contains(&2));
    assert!(known_set.contains(&3));
}

/// Coverage: `matrix_det_mod` lines 128-129 — `if n == 0 || matrix[0].len() != n { return None; }`.
/// `Basis2Lemma::run` always feeds a square nxn matrix, so the only way
/// to exercise the non-square guard is to call `matrix_det_mod`
/// directly. Pass a 2×3 matrix and expect `None`.
#[test]
fn test_bim_matrix_det_mod_rejects_non_square() {
    use num_traits::Zero;
    let p = BigUint::from(7u32);
    // 2 rows × 3 cols — non-square.
    let m: Vec<Vec<BigUint>> = vec![
        vec![BigUint::from(1u32), BigUint::from(2u32), BigUint::from(3u32)],
        vec![BigUint::from(4u32), BigUint::from(5u32), BigUint::from(6u32)],
    ];
    assert!(matrix_det_mod(&m, &p).is_none(), "non-square matrix ⇒ None");

    // Empty matrix `n == 0` also hits the same guard via the `n == 0`
    // disjunct.
    let empty: Vec<Vec<BigUint>> = Vec::new();
    assert!(matrix_det_mod(&empty, &p).is_none(), "n==0 ⇒ None");

    // Sanity: a square invertible matrix is accepted (positive baseline).
    let square: Vec<Vec<BigUint>> = vec![
        vec![BigUint::from(1u32), BigUint::from(0u32)],
        vec![BigUint::from(0u32), BigUint::from(1u32)],
    ];
    let det = matrix_det_mod(&square, &p).expect("identity is invertible");
    assert!(!det.is_zero(), "det of identity must be nonzero");
}

/// Coverage: `matrix_det_mod` lines 137-138 (pivot row swap + sign
/// flip) and line 158 (`det = (p - &det) % p` when `sign_flip` is true,
/// then `Some(det)`). Matrix `[[0, 1], [1, 0]]` over GF(7):
///   col 0: pivot at row 1 (m[0][0] = 0), swap rows 0 and 1, sign_flip = true.
///   After swap: [[1, 0], [0, 1]]. det = 1; pivot_inv = 1. Inner row
///   has 0 at col 0 ⇒ inner-loop `continue` branch (line 143-145).
///   col 1: pivot at row 1, no swap. det = 1·1 = 1.
///   sign_flip is true ⇒ det = (7 - 1) % 7 = 6 ≠ 0.
#[test]
fn test_bim_matrix_det_mod_pivot_swap_sign_flip() {
    use num_traits::Zero;
    let p = BigUint::from(7u32);
    let m: Vec<Vec<BigUint>> = vec![
        vec![BigUint::zero(), BigUint::from(1u32)],
        vec![BigUint::from(1u32), BigUint::zero()],
    ];
    let det = matrix_det_mod(&m, &p).expect("anti-diagonal is invertible");
    // det of [[0,1],[1,0]] is -1, which mod 7 = 6.
    assert_eq!(
        det,
        BigUint::from(6u32),
        "sign-flip path must produce det = p - 1 = 6 mod 7"
    );
}
