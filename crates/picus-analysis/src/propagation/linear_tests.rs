//! Tests for the `linear` propagation lemma.
//!
//! Spec (from doc comments in `linear.rs`):
//!   - For each polynomial constraint, a variable that occurs only in
//!     total-degree-1 terms (never in any total-degree ≥ 2 term) is
//!     "linear-only", and is derivable from the other wires in that
//!     constraint. The implication `deps(p, v) → wire(v)` is recorded.
//!   - The lemma applies the implications to a fixed point each call,
//!     promoting wires from `unknown` to `known` whenever every
//!     dependency wire is already known.
//!   - Empty dep set ⇒ wire promoted unconditionally (single-var
//!     constraint, or `x_w - y_w = 0` marker).
//!   - Near-miss: a variable that ALSO appears in a higher-degree term
//!     is `nonlinear` and is NOT linear-derivable from this constraint
//!     (e.g. `x + x*y = 0` does not directly give `x`).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use num_bigint::BigUint;
use picus_core::ff::field::PrimeField;
use picus_core::poly::FfPolyRing;
use picus_smt::poly_ir::PolyIR;

use crate::propagation::lemma::{PropagationCtx, PropagationLemma};
use crate::propagation::linear::LinearLemma;
use crate::propagation::range::RangeValue;

const PRIME: u64 = 7;

fn make_ir(
    n_wires: usize,
    build: impl FnOnce(&Arc<FfPolyRing>) -> Vec<picus_core::poly::IrPoly>,
) -> PolyIR {
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

struct CtxOwned {
    known: HashSet<usize>,
    unknown: HashSet<usize>,
    ranges: HashMap<usize, RangeValue>,
    learned: Vec<picus_core::poly::IrPoly>,
    learned_disjunctions: Vec<Vec<picus_core::poly::IrPoly>>,
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

// ───── Positive: rule fires ─────────────────────────────────────

#[test]
fn prop_linear_single_var_constraint_promotes_unconditionally() {
    // x1 = 0 ⇒ deps = {} ⇒ wire 1 promoted regardless of other state.
    let ir = make_ir(3, |ring| vec![ring.var(1)]);
    let mut owned = CtxOwned::new(&[], &[1, 2]);
    let mut lemma = LinearLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(progress, "empty-dep wire must be promoted");
    assert!(owned.known.contains(&1), "wire 1 promoted to known");
    assert!(!owned.unknown.contains(&1));
}

#[test]
fn prop_linear_two_var_constraint_promotes_when_dep_known() {
    // x1 + x2 = 0. Wire 1 has dep {2}; if wire 2 is known, wire 1
    // promotes. Wire 2 has dep {1}; if wire 1 is known, wire 2 promotes.
    let ir = make_ir(3, |ring| {
        let p = ring.add(ring.var(1), ring.var(2));
        vec![p]
    });
    let mut owned = CtxOwned::new(&[2], &[1]);
    let mut lemma = LinearLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(progress);
    assert!(owned.known.contains(&1), "wire 1 derivable from wire 2");
}

#[test]
fn prop_linear_no_progress_when_dep_unknown() {
    // x1 + x2 = 0 with NEITHER known: neither wire promotes (we don't
    // have enough info to derive either).
    let ir = make_ir(3, |ring| {
        let p = ring.add(ring.var(1), ring.var(2));
        vec![p]
    });
    let mut owned = CtxOwned::new(&[], &[1, 2]);
    let mut lemma = LinearLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "no deps known ⇒ no promotion");
    assert!(owned.known.is_empty());
}

#[test]
fn prop_linear_chain_promotion_within_one_call() {
    // Two constraints: x1 + x2 = 0, x2 + x3 = 0.
    // Start with wire 1 known. Inner loop should promote wire 2
    // (deps={1} satisfied), then wire 3 (deps={2} now satisfied)
    // — all within one `run` call (the inner `loop`).
    let ir = make_ir(4, |ring| {
        let c1 = ring.add(ring.var(1), ring.var(2));
        let c2 = ring.add(ring.var(2), ring.var(3));
        vec![c1, c2]
    });
    let mut owned = CtxOwned::new(&[1], &[2, 3]);
    let mut lemma = LinearLemma::default();
    let _ = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(owned.known.contains(&2), "wire 2 promoted in inner loop");
    assert!(owned.known.contains(&3), "wire 3 promoted after wire 2");
}

// ───── Negative: nonlinear variable does NOT promote ────────────

#[test]
fn prop_linear_pure_nonlinear_var_not_promoted_from_quadratic() {
    // x1*x2 = 0: both x1 and x2 appear only in a degree-2 term, so
    // both are "nonlinear" w.r.t. this constraint. No `(wire → deps)`
    // entry is emitted; promoting either from this constraint alone
    // would be unsound.
    let ir = make_ir(3, |ring| {
        let p = ring.mul(ring.var(1), ring.var(2));
        vec![p]
    });
    // Pretend wire 2 is known; that shouldn't be enough to promote
    // wire 1 from a purely-quadratic constraint.
    let mut owned = CtxOwned::new(&[2], &[1]);
    let mut lemma = LinearLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "purely-quadratic constraint cannot promote");
    assert!(!owned.known.contains(&1));
}

#[test]
fn prop_linear_mixed_term_var_not_linear_only() {
    // x1 + x1*x2 = 0: x1 appears in both a degree-1 term and a
    // degree-2 term. `linear ∩ nonlinear` ⇒ NOT linear-only, so no
    // implication recorded for wire 1 from this constraint.
    // x2 appears only in the degree-2 term ⇒ nonlinear ⇒ no
    // implication for wire 2 either.
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let x2 = ring.var(2);
        let mixed = ring.mul(ring.clone_poly(&x1), x2);
        vec![ring.add(x1, mixed)]
    });
    let mut owned = CtxOwned::new(&[2], &[1]);
    let mut lemma = LinearLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(
        !progress,
        "variable appearing in a higher-degree term must not be linear-only"
    );
}

#[test]
fn prop_linear_already_known_not_double_processed() {
    // x1 known up front. Re-running the lemma doesn't move it out of
    // known nor make spurious progress.
    let ir = make_ir(3, |ring| vec![ring.var(1)]);
    let mut owned = CtxOwned::new(&[1], &[2]);
    let mut lemma = LinearLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "already-known wire is not progress");
    assert!(owned.known.contains(&1));
}

#[test]
fn prop_linear_empty_ir_no_progress() {
    let ir = make_ir(3, |_| Vec::new());
    let mut owned = CtxOwned::new(&[], &[1, 2]);
    let mut lemma = LinearLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(!progress, "empty IR cannot make progress");
}

#[test]
fn prop_linear_cache_rebuilds_when_equalities_grow() {
    // First call: only x1 = 0 known. Wire 1 promotes.
    // After call, append `x2 = 0` to ir.equalities (simulating DPVL
    // learning new equality). Re-run: wire 2 must also promote, which
    // requires the cache to rebuild.
    let mut ir = make_ir(3, |ring| vec![ring.var(1)]);
    let mut owned = CtxOwned::new(&[], &[1, 2]);
    let mut lemma = LinearLemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(owned.known.contains(&1));
    assert!(!owned.known.contains(&2));

    // Append a new constraint.
    let new_eq = ir.ring.var(2);
    ir.equalities.push(new_eq);

    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(
        owned.known.contains(&2),
        "lemma must rebuild cdmap cache when equalities grow"
    );
}

#[test]
fn prop_linear_lemma_name_is_stable() {
    let lemma = LinearLemma::default();
    assert_eq!(lemma.name(), "linear");
}

/// `classify_poly_vars` treats a degree-0 non-zero constant term as a
/// no-op match arm. Build `x_1 + 1 = 0` (which is `x_1 - p_minus_1 = 0`
/// in field form): the polynomial has one constant term and one linear
/// term. The constant hits the `0 => {}` arm; the linear term registers
/// wire 1 as linear-only. wire 1's dep set is empty (no other
/// variables) ⇒ promotes unconditionally.
#[test]
fn test_linear_classify_handles_nonzero_constant_term() {
    let ir = make_ir(3, |ring| {
        let x1 = ring.var(1);
        let one = ring.constant(ring.field().one());
        vec![ring.add(x1, one)]
    });
    let mut owned = CtxOwned::new(&[], &[1]);
    let mut lemma = LinearLemma::default();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(
        progress,
        "x_1 + 1 = 0 still promotes wire 1 unconditionally (deps=empty)"
    );
    assert!(owned.known.contains(&1));
}

/// Cache HIT path: when the equality vector length is unchanged between
/// calls, `cdmap` is not rebuilt. The lemma must still respect
/// known/unknown updates that happened externally.
#[test]
fn test_linear_cache_hit_on_unchanged_ir() {
    // x_1 + x_2 = 0: starts with wire 2 known ⇒ wire 1 promotes.
    // Reset known/unknown, re-run with the same IR: cache hits, wire 1
    // promotes again (or not — depending on starting state).
    let ir = make_ir(3, |ring| {
        let p = ring.add(ring.var(1), ring.var(2));
        vec![p]
    });
    let mut owned = CtxOwned::new(&[2], &[1]);
    let mut lemma = LinearLemma::default();
    {
        let mut ctx = owned.ctx();
        let _ = lemma.run(&ir, &mut ctx);
    }
    assert!(owned.known.contains(&1));

    // Reset state, re-run on the SAME `ir` instance — cache hit branch.
    owned.known = [2usize].into_iter().collect();
    owned.unknown = [1usize].into_iter().collect();
    let progress = {
        let mut ctx = owned.ctx();
        lemma.run(&ir, &mut ctx)
    };
    assert!(progress, "cache hit must not blunt promotion logic");
    assert!(owned.known.contains(&1));
}
