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
