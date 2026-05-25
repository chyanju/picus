//! Binary01 propagation lemma — detect wires forced to `{0, 1}`.
//!
//! Recognises any polynomial equality of the form `x^2 - x = 0` (in
//! field form, `x^2 + (p-1) * x` with no other terms). The constraint
//! pins the wire's value to `{0, 1}`. Once a wire's range collapses
//! to a singleton, it joins the known set.

use std::collections::HashSet;

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_smt::poly_ir::PolyIR;

use super::lemma::{LemmaDescriptor, PropagationCtx, PropagationLemma};
use super::range::RangeValue;

#[derive(Default)]
pub struct Binary01Lemma {
    /// Set of wires we've already classified as binary; avoids
    /// re-running the pattern match on every iteration.
    binary_wires: HashSet<usize>,
}

impl PropagationLemma for Binary01Lemma {
    fn name(&self) -> &'static str {
        "binary01"
    }

    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool {
        let p = ir.ring.field().prime();
        let p_minus_1 = p - BigUint::one();
        let binary_set: HashSet<BigUint> =
            [BigUint::zero(), BigUint::one()].into_iter().collect();

        let mut progress = false;
        for poly in &ir.equalities {
            if let Some(wire) = match_x_squared_minus_x(ir, poly, &p_minus_1)
                && self.binary_wires.insert(wire)
            {
                let entry = ctx.ranges.entry(wire).or_insert(RangeValue::Bottom);
                entry.intersect(binary_set.clone());
            }
        }

        // Promote any singleton-ranged unknown wire to known.
        let mut newly_known: Vec<usize> = Vec::new();
        for (&wire, range) in ctx.ranges.iter() {
            if range.is_singleton() && ctx.unknown.contains(&wire) {
                newly_known.push(wire);
            }
        }
        for wire in newly_known {
            if ctx.unknown.remove(&wire) {
                ctx.known.insert(wire);
                progress = true;
            }
        }
        progress
    }
}

/// Match `c1 * x^2 + c2 * x = 0` with `c1, c2` such that `c1 + c2 = 0`
/// mod p — i.e. the equation `c1 * (x^2 - x) = 0`. Returns the wire
/// index. Variables `y_i` (alt-copy) map back to wire `i`.
fn match_x_squared_minus_x(
    ir: &PolyIR,
    poly: &picus_core::poly::IrPoly,
    p_minus_1: &BigUint,
) -> Option<usize> {
    // Two-term degree-2 polynomial: gather terms sparse-natively as
    // (coeff, nonzero (var, exp) pairs) — no `0..n_vars` scan, no dense
    // monomial materialisation (matters on wide rings).
    let terms: Vec<(BigUint, Vec<(usize, usize)>)> = ir
        .poly_terms_idx(poly)
        .map(|(coeff, vars)| {
            let exps: Vec<(usize, usize)> = vars.into_iter().map(|(v, e)| (v, e as usize)).collect();
            (coeff, exps)
        })
        .collect();
    if terms.len() != 2 {
        return None;
    }

    // Identify the quadratic and linear terms.
    let mut sq_idx = None;
    let mut lin_idx = None;
    for (i, (_, exps)) in terms.iter().enumerate() {
        let total: usize = exps.iter().map(|&(_, e)| e).sum();
        if total == 2 && exps.len() == 1 && exps[0].1 == 2 {
            sq_idx = Some(i);
        } else if total == 1 && exps.len() == 1 && exps[0].1 == 1 {
            lin_idx = Some(i);
        }
    }
    let (sq_idx, lin_idx) = (sq_idx?, lin_idx?);
    let (sq_coeff, sq_exps) = &terms[sq_idx];
    let (lin_coeff, lin_exps) = &terms[lin_idx];

    if sq_exps[0].0 != lin_exps[0].0 {
        return None;
    }
    let var = sq_exps[0].0;

    // x^2 - x has c1 = 1, c2 = p-1 (so c1 + c2 = 0 mod p). More
    // generally any non-zero c1 with c2 = -c1 works.
    let p = ir.ring.field().prime();
    let neg_sq_coeff = if sq_coeff.is_zero() {
        BigUint::zero()
    } else {
        p - sq_coeff
    };
    if lin_coeff == &neg_sq_coeff || (sq_coeff == &BigUint::one() && lin_coeff == p_minus_1) {
        return Some(ir.var_to_wire(var));
    }
    None
}

inventory::submit! {
    LemmaDescriptor {
        name: "binary01",
        factory: || Box::new(Binary01Lemma::default()),
    }
}
