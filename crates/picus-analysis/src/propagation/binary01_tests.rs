//! Tests for the `binary01` propagation lemma.
//!
//! Spec (from doc comments):
//!   - Recognises polynomial equalities of the form `c1*x^2 + c2*x = 0`
//!     with `c1 + c2 ≡ 0 mod p` (i.e. `c1 * (x^2 - x) = 0`). This pins
//!     wire-of-x to {0, 1}.
//!   - Once a wire's range collapses to a singleton (length-1 set), the
//!     wire is promoted from `unknown` to `known`. So {0,1} alone is
//!     NOT a promotion — it tightens the range; promotion happens only
//!     when the set collapses to one element.
//!   - Near-miss patterns (constant term, three terms, wrong exponents,
//!     two different variables, wrong coefficient relation) must NOT
//!     fire (soundness).
//!   - Wire is identified via `var_to_wire`, so y_w-based pattern still
//!     promotes wire w.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_core::ff::field::PrimeField;
use picus_core::poly::FfPolyRing;
use picus_smt::poly_ir::PolyIR;

use crate::propagation::binary01::Binary01Lemma;
use crate::propagation::lemma::{PropagationCtx, PropagationLemma};
use crate::propagation::range::RangeValue;

const PRIME: u64 = 7;

/// Build a `PolyIR` with `n_wires` wires and an explicit `equalities`
/// list built via the supplied closure.
fn make_ir(n_wires: usize, build: impl FnOnce(&Arc<FfPolyRing>) -> Vec<picus_core::poly::IrPoly>) -> PolyIR {
    let p = BigUint::from(PRIME);
    let field = PrimeField::new(p);
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

/// Build a fresh `PropagationCtx` view over caller-owned slots.
/// Convention: we pre-populate `unknown` so promotions become visible.
struct CtxOwned {
    known: HashSet<usize>,
    unknown: HashSet<usize>,
    ranges: HashMap<usize, RangeValue>,
    learned: Vec<picus_core::poly::IrPoly>,
    learned_disjunctions: Vec<Vec<picus_core::poly::IrPoly>>,
}

impl CtxOwned {
    fn new(unknown_wires: &[usize]) -> Self {
        CtxOwned {
            known: HashSet::new(),
            unknown: unknown_wires.iter().copied().collect(),
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

// ───── Positive tests: rule fires ───────────────────────────────

#[test]
fn prop_binary01_canonical_x_squared_minus_x_collapses_wire() {
    // x1^2 - x1 = 0 ⇒ x1 ∈ {0, 1}, wire 1 forced to {0, 1}.
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x1_sq = ring.mul(ring.clone_poly(&x1), ring.clone_poly(&x1));
        let neg_x1 = ring.neg(x1);
        vec![ring.add(x1_sq, neg_x1)]
    });
    let mut owned = CtxOwned::new(&[1]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    // Range for wire 1 must be {0, 1} ⇒ binary.
    let r = owned.ranges.get(&1).expect("wire 1 range was tightened");
    assert!(r.is_binary(), "wire 1 range must be binary, got {:?}", r);
    // Range has TWO elements, so it's not yet a singleton, so wire 1
    // is NOT promoted to known by binary01 alone.
    assert!(!r.is_singleton(), "x^2-x=0 has two roots, not a singleton");
    assert!(owned.known.is_empty(), "binary range alone is not a promotion");
}

#[test]
fn prop_binary01_promotes_when_range_already_collapsed_to_singleton() {
    // Pre-seed wire 1's range to {0}, then re-run with x^2-x=0 to fire
    // the rule. The intersection of {0} ∩ {0,1} = {0}, still a
    // singleton, so the wire is promoted from unknown → known.
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x1_sq = ring.mul(ring.clone_poly(&x1), ring.clone_poly(&x1));
        let neg_x1 = ring.neg(x1);
        vec![ring.add(x1_sq, neg_x1)]
    });
    let mut owned = CtxOwned::new(&[1]);
    owned
        .ranges
        .insert(1, RangeValue::Values([BigUint::zero()].into_iter().collect()));
    let mut lemma = Binary01Lemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(progress, "singleton-range wire must promote");
    assert!(owned.known.contains(&1), "wire 1 promoted to known");
    assert!(!owned.unknown.contains(&1), "wire 1 removed from unknown");
}

#[test]
fn prop_binary01_scaled_form_c_x_squared_minus_c_x_fires() {
    // 2*x1^2 + (p-2)*x1 = 0 ⇒ same root set {0, 1}; lemma should fire.
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x1_sq = ring.mul(ring.clone_poly(&x1), ring.clone_poly(&x1));
        let two = ring.field().from_u64(2);
        let neg_two = ring.field().from_u64(PRIME - 2);
        let t1 = ring.scale(two, x1_sq);
        let t2 = ring.scale(neg_two, x1);
        vec![ring.add(t1, t2)]
    });
    let mut owned = CtxOwned::new(&[1]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    let r = owned.ranges.get(&1).expect("wire 1 range tightened");
    assert!(r.is_binary());
}

#[test]
fn prop_binary01_alt_copy_y_wire_promotes_same_wire() {
    // y1^2 - y1 = 0 (idx n_wires+1). var_to_wire maps both to wire 1.
    let ir = make_ir(3, |ring| {
        let y1 = ring.var(4); // n_wires=3, so y1 = idx 4
        let y1_sq = ring.mul(ring.clone_poly(&y1), ring.clone_poly(&y1));
        let neg_y1 = ring.neg(y1);
        vec![ring.add(y1_sq, neg_y1)]
    });
    let mut owned = CtxOwned::new(&[1]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(
        owned.ranges.contains_key(&1),
        "y1 must promote wire 1's range"
    );
}

// ───── Negative tests: near-miss, rule does NOT fire ────────────

#[test]
fn prop_binary01_constant_term_rejects() {
    // x1^2 - x1 + 1 = 0 has three terms; pattern requires exactly two.
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x1_sq = ring.mul(ring.clone_poly(&x1), ring.clone_poly(&x1));
        let neg_x1 = ring.neg(x1);
        let one = ring.constant(ring.field().one());
        let with_const = ring.add(ring.add(x1_sq, neg_x1), one);
        vec![with_const]
    });
    let mut owned = CtxOwned::new(&[1]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(
        !owned.ranges.contains_key(&1),
        "three-term polynomial must not fire binary01"
    );
}

#[test]
fn prop_binary01_two_different_variables_rejects() {
    // x1*x2 - x1 = 0 has a degree-2 term but it's not x1^2.
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x2 = ring.var(2);
        let mixed = ring.mul(ring.clone_poly(&x1), x2);
        let neg_x1 = ring.neg(x1);
        vec![ring.add(mixed, neg_x1)]
    });
    let mut owned = CtxOwned::new(&[1, 2]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(owned.ranges.is_empty(), "mixed term must not fire binary01");
}

#[test]
fn prop_binary01_wrong_coefficient_sum_rejects() {
    // 2*x1^2 + x1 = 0: c1 + c2 = 3 ≠ 0 mod 7. Roots are 0 and (p-1)/2 - 1
    // mod 7 ≠ {0, 1}, so the rule must reject.
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x1_sq = ring.mul(ring.clone_poly(&x1), ring.clone_poly(&x1));
        let two = ring.field().from_u64(2);
        let one = ring.field().one();
        let t1 = ring.scale(two, x1_sq);
        let t2 = ring.scale(one, x1);
        vec![ring.add(t1, t2)]
    });
    let mut owned = CtxOwned::new(&[1]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(
        owned.ranges.is_empty(),
        "wrong coefficient relation must not fire binary01"
    );
}

#[test]
fn prop_binary01_quadratic_only_rejects() {
    // x1^2 = 0 has one term (degree 2). Pattern requires exactly two
    // terms (one quadratic, one linear).
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x1_sq = ring.mul(ring.clone_poly(&x1), x1);
        vec![x1_sq]
    });
    let mut owned = CtxOwned::new(&[1]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(
        owned.ranges.is_empty(),
        "single-term quadratic must not fire binary01"
    );
}

#[test]
fn prop_binary01_linear_only_rejects() {
    // x1 = 0 (single linear term). Pattern requires a quadratic term.
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        vec![x1]
    });
    let mut owned = CtxOwned::new(&[1]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(
        owned.ranges.is_empty(),
        "single linear term must not fire binary01"
    );
}

#[test]
fn prop_binary01_empty_ir_no_progress() {
    let ir = make_ir(3, |_| Vec::new());
    let mut owned = CtxOwned::new(&[1, 2]);
    let mut lemma = Binary01Lemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "empty IR cannot make progress");
    assert!(owned.ranges.is_empty());
}

#[test]
fn prop_binary01_lemma_name_is_stable() {
    let lemma = Binary01Lemma::default();
    assert_eq!(lemma.name(), "binary01");
}

// ── structural matcher near-misses ─────────────────────────────────

/// `x_1^2 - x_2 = 0` has both a quadratic term (in x_1) and a linear
/// term (in x_2). Pattern requires sq_exps[0].0 == lin_exps[0].0 (same
/// variable). Different variables ⇒ `match_x_squared_minus_x` returns
/// None at the variable-mismatch guard.
#[test]
fn test_binary01_rejects_quadratic_in_one_var_linear_in_another() {
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x2 = ring.var(2);
        let x1_sq = ring.mul(ring.clone_poly(&x1), x1);
        let neg_x2 = ring.neg(x2);
        vec![ring.add(x1_sq, neg_x2)]
    });
    let mut owned = CtxOwned::new(&[1, 2]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(
        owned.ranges.is_empty(),
        "x_1^2 - x_2 = 0 ties two different variables ⇒ NOT binary01"
    );
}

/// Two-term polynomial where BOTH terms are linear (no quadratic).
/// `sq_idx` stays None ⇒ pattern returns None.
#[test]
fn test_binary01_rejects_two_linear_terms() {
    // x_1 + x_2 = 0: two linear terms; no quadratic term.
    let ir = make_ir(3, |ring| {
        let p = ring.add(ring.var(1), ring.var(2));
        vec![p]
    });
    let mut owned = CtxOwned::new(&[1, 2]);
    let mut lemma = Binary01Lemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(owned.ranges.is_empty(), "two linear terms cannot match x^2-x");
}

/// Range singleton-promotion path when the range was tightened to `{1}`
/// (the other binary singleton).
#[test]
fn test_binary01_promotes_when_pre_range_pins_to_one() {
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x1_sq = ring.mul(ring.clone_poly(&x1), ring.clone_poly(&x1));
        let neg_x1 = ring.neg(x1);
        vec![ring.add(x1_sq, neg_x1)]
    });
    let mut owned = CtxOwned::new(&[1]);
    owned
        .ranges
        .insert(1, RangeValue::Values([BigUint::one()].into_iter().collect()));
    let mut lemma = Binary01Lemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(progress);
    assert!(owned.known.contains(&1));
    assert!(!owned.unknown.contains(&1));
}
