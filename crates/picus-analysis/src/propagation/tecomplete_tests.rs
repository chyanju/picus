//! Tests for the `tecomplete` twisted-Edwards complete-addition lemma.
//!
//! A GF(7) gadget mirrors the circomlib `BabyAdd` constraint shape with
//! configurable `(a, d)`. Over GF(7) the quadratic residues are {1, 2, 4}, so
//! `a = 1` (square) and `d = 3` (non-residue, `3³ = 6 = −1`) satisfy the
//! Bernstein–Lange certificate, while `d = 2` (a square) must not.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use num_bigint::BigUint;
use picus_core::ff::field::PrimeField;
use picus_core::poly::{FfPolyRing, IrPoly};
use picus_smt::poly_ir::PolyIR;

use crate::propagation::lemma::{PropagationCtx, PropagationLemma};
use crate::propagation::tecomplete::TecompleteLemma;
use crate::propagation::range::RangeValue;

const PRIME: u64 = 7;

fn make_ir(n_wires: usize, build: impl FnOnce(&Arc<FfPolyRing>) -> Vec<IrPoly>) -> PolyIR {
    let field = PrimeField::new(BigUint::from(PRIME));
    let mut names = Vec::with_capacity(2 * n_wires);
    for i in 0..n_wires {
        names.push(format!("x{}", i));
    }
    for i in 0..n_wires {
        names.push(format!("y{}", i));
    }
    let ring = Arc::new(FfPolyRing::new(field, names));
    let equalities = build(&ring);
    PolyIR {
        ring,
        n_wires,
        input_indices: HashSet::new(),
        equalities,
        disjunctions: Vec::new(),
        known_signals: HashSet::new(),
        target_signal: 0,
        disequalities: Vec::new(),
        assignments: Vec::new(),
        bitsums: Vec::new(),
        add_field_polys: false,
    }
}

struct CtxOwned {
    known: HashSet<usize>,
    unknown: HashSet<usize>,
    ranges: HashMap<usize, RangeValue>,
    learned: Vec<IrPoly>,
    learned_disjunctions: Vec<Vec<IrPoly>>,
}

impl CtxOwned {
    fn new(known: &[usize], unknown: &[usize]) -> Self {
        CtxOwned {
            known: known.iter().copied().collect(),
            unknown: unknown.iter().copied().collect(),
            ranges: HashMap::new(),
            learned: Vec::new(),
            learned_disjunctions: Vec::new(),
        }
    }
    fn ctx(&mut self) -> PropagationCtx<'_> {
        PropagationCtx {
            known: &mut self.known,
            unknown: &mut self.unknown,
            ranges: &mut self.ranges,
            learned: &mut self.learned,
            learned_disjunctions: &mut self.learned_disjunctions,
        }
    }
}

/// Wire layout: 1=xout, 2=yout, 3=x1, 4=y1, 5=x2, 6=y2, 7=β, 8=γ, 9=δ, 10=τ.
fn babyadd_gf7(a: i64, d: i64) -> PolyIR {
    make_ir(11, |ring| {
        let f = ring.field();
        let c = |n: i64| ring.constant(f.from_int(n));
        let v = |i| ring.var(i);
        // β = x1·y2
        let eq_beta = ring.sub(v(7), ring.mul(v(3), v(6)));
        // γ = y1·x2
        let eq_gamma = ring.sub(v(8), ring.mul(v(4), v(5)));
        // δ = (x2 + y2)(y1 − a·x1)
        let sum = ring.add(v(5), v(6));
        let diff = ring.sub(v(4), ring.mul(c(a), v(3)));
        let eq_delta = ring.sub(v(9), ring.mul(sum, diff));
        // τ = β·γ
        let eq_tau = ring.sub(v(10), ring.mul(v(7), v(8)));
        // xout·(1 + d·τ) = β + γ   →   d·x1·τ + x1 − β − γ
        let den1 = ring.mul(ring.mul(c(d), v(1)), v(10));
        let eq_xout = ring.sub(ring.sub(ring.add(den1, v(1)), v(7)), v(8));
        // yout·(1 − d·τ) = a·β − γ + δ   →   x2 − d·x2·τ − a·β + γ − δ
        let den2 = ring.mul(ring.mul(c(d), v(2)), v(10));
        let mut eq_yout = ring.sub(v(2), den2);
        eq_yout = ring.sub(eq_yout, ring.mul(c(a), v(7)));
        eq_yout = ring.add(eq_yout, v(8));
        eq_yout = ring.sub(eq_yout, v(9));
        vec![eq_beta, eq_gamma, eq_delta, eq_tau, eq_xout, eq_yout]
    })
}

const INPUTS: [usize; 4] = [3, 4, 5, 6];
const NON_INPUTS: [usize; 6] = [1, 2, 7, 8, 9, 10];

#[test]
fn tecomplete_promotes_both_outputs_when_inputs_known() {
    // a = 1 (square), d = 3 (non-residue) ⇒ certificate holds.
    let ir = babyadd_gf7(1, 3);
    let mut owned = CtxOwned::new(&INPUTS, &NON_INPUTS);
    let mut lemma = TecompleteLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(progress, "gadget with known inputs must promote");
    assert!(owned.known.contains(&1), "xout promoted to known");
    assert!(owned.known.contains(&2), "yout promoted to known");
    assert!(!owned.unknown.contains(&1) && !owned.unknown.contains(&2));
}

#[test]
fn tecomplete_sound_miss_when_d_is_a_square() {
    // d = 2 is a quadratic residue mod 7 ⇒ certificate fails ⇒ no promotion.
    let ir = babyadd_gf7(1, 2);
    let mut owned = CtxOwned::new(&INPUTS, &NON_INPUTS);
    let mut lemma = TecompleteLemma::default();
    let _ = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(!owned.known.contains(&1), "no promotion when d is a square");
    assert!(!owned.known.contains(&2), "no promotion when d is a square");
}

#[test]
fn tecomplete_no_promotion_when_inputs_unknown() {
    let ir = babyadd_gf7(1, 3);
    let mut owned = CtxOwned::new(&[], &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    let mut lemma = TecompleteLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "outputs must not promote while inputs are unknown");
    assert!(!owned.known.contains(&1) && !owned.known.contains(&2));
}
