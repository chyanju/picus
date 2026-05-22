//! All-But-One-Zero (ABOZ) propagation lemma.
//!
//! In R1CS shape the original pattern is two `A * B = 0` constraints
//! plus a linear "constant-and-mux-bits" sum that ties them together;
//! after polynomial lowering each `A * B = 0` is a single bilinear
//! monomial. We look for triples
//!     `x * y0 = 0`,  `x * y1 = 0`,  `x + y0 + y1 + c = 0`
//! where `x` and `c` are known. From `x * y_i = 0` and `x ≠ 0` we
//! conclude `y_i = 0`. The lemma only fires when `x`'s range proves
//! `x ≠ 0`; without that gate, two witnesses with `x = 0` can disagree
//! on `y_0` / `y_1` (the bilinear constraints become vacuous and the
//! linear sum admits a one-parameter family of solutions), so marking
//! them as uniquely determined would be unsound.

use std::collections::HashSet;

use num_traits::Zero;
use picus_smt::poly_ir::PolyIR;
use picus_solver::poly::Poly;

use super::lemma::{LemmaDescriptor, PropagationCtx, PropagationLemma};

#[derive(Default)]
pub struct AbozLemma;

impl PropagationLemma for AbozLemma {
    fn name(&self) -> &'static str {
        "aboz"
    }

    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool {
        let products = collect_bilinear_zero(ir);
        if products.len() < 2 {
            return false;
        }
        let linear_sums = collect_linear_sums(ir);
        if linear_sums.is_empty() {
            return false;
        }

        let mut progress = false;
        for (i, (a0, b0)) in products.iter().enumerate() {
            for (a1, b1) in products.iter().skip(i + 1) {
                // Candidate quadruple (x, y0, y1, ...) — x is one wire
                // shared between the two products (typically the
                // selector), y0 / y1 are the other side of each.
                let shared = if a0 == a1 {
                    Some((*a0, *b0, *b1))
                } else if a0 == b1 {
                    Some((*a0, *b0, *a1))
                } else if b0 == a1 {
                    Some((*b0, *a0, *b1))
                } else if b0 == b1 {
                    Some((*b0, *a0, *a1))
                } else {
                    None
                };
                let Some((x, y0, y1)) = shared else {
                    continue;
                };
                if y0 == y1 {
                    continue;
                }

                // Find a linear sum that mentions {x, y0, y1, c} for
                // some additional known wire c (any wire other than
                // x/y0/y1 that's already in ks).
                for lin in &linear_sums {
                    if !lin.contains(&x) || !lin.contains(&y0) || !lin.contains(&y1) {
                        continue;
                    }
                    let has_known_partner = lin
                        .iter()
                        .any(|&w| w != x && w != y0 && w != y1 && ctx.known.contains(&w));
                    if !has_known_partner {
                        continue;
                    }
                    if !ctx.known.contains(&x) {
                        continue;
                    }
                    // Soundness gate: `x * y_i = 0` only forces
                    // `y_i = 0` when `x ≠ 0`. Without a range proving
                    // `x` cannot be zero, two witnesses with `x = 0`
                    // can disagree on `y_0` / `y_1` while satisfying
                    // every constraint.
                    if !ctx
                        .ranges
                        .get(&x)
                        .map_or(false, |r| r.excludes_zero())
                    {
                        continue;
                    }
                    // Promote y0, y1 to known if they were unknown.
                    if ctx.unknown.remove(&y0) {
                        ctx.known.insert(y0);
                        progress = true;
                    }
                    if ctx.unknown.remove(&y1) {
                        ctx.known.insert(y1);
                        progress = true;
                    }
                }
            }
        }
        progress
    }
}

/// Wire indices `(a, b)` for every equality of the form `c * x_a * x_b
/// = 0`. Skips constraints that have any other terms beyond the
/// single bilinear monomial.
fn collect_bilinear_zero(ir: &PolyIR) -> Vec<(usize, usize)> {
    let ring = &ir.ring.ring;
    let n_vars = ring.n_vars();
    let field = &ir.ring.field;
    let mut out = Vec::new();
    for poly in &ir.equalities {
        if let Some((a, b)) = match_bilinear(ir, poly, ring, n_vars, field) {
            out.push((a, b));
        }
    }
    out
}

fn match_bilinear(
    ir: &PolyIR,
    poly: &Poly,
    ring: &picus_solver::poly::PolyRingType,
    n_vars: usize,
    field: &picus_solver::ff::field::PrimeField,
) -> Option<(usize, usize)> {
    let mut bilinear: Option<(usize, usize)> = None;
    for (c, m) in ring.terms(poly) {
        let mut total = 0usize;
        let mut vars: Vec<usize> = Vec::new();
        for v in 0..n_vars {
            let e = ring.exponent_at(&m, v);
            total += e;
            if e == 1 {
                vars.push(v);
            } else if e > 1 {
                return None;
            }
        }
        match total {
            0 => {
                if !field.to_biguint(c).is_zero() {
                    return None;
                }
            }
            2 if vars.len() == 2 => {
                if bilinear.is_some() {
                    return None;
                }
                let a = ir.var_to_wire(vars[0]);
                let b = ir.var_to_wire(vars[1]);
                bilinear = Some((a.min(b), a.max(b)));
            }
            _ => return None,
        }
    }
    bilinear
}

/// Wire-index sets for every equality whose terms are all linear
/// monomials (no quadratic terms). Constants are ignored.
fn collect_linear_sums(ir: &PolyIR) -> Vec<HashSet<usize>> {
    let ring = &ir.ring.ring;
    let n_vars = ring.n_vars();
    let mut out = Vec::new();
    'poly: for poly in &ir.equalities {
        let mut wires: HashSet<usize> = HashSet::new();
        for (_, m) in ring.terms(poly) {
            let mut total = 0usize;
            let mut var: Option<usize> = None;
            for v in 0..n_vars {
                let e = ring.exponent_at(&m, v);
                total += e;
                if e == 1 {
                    if var.is_some() {
                        continue 'poly;
                    }
                    var = Some(v);
                } else if e > 1 {
                    continue 'poly;
                }
            }
            if total == 0 {
                continue;
            }
            wires.insert(ir.var_to_wire(var.unwrap()));
        }
        if !wires.is_empty() {
            out.push(wires);
        }
    }
    out
}

inventory::submit! {
    LemmaDescriptor {
        name: "aboz",
        factory: || Box::new(AbozLemma::default()),
    }
}
