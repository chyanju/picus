//! `tecomplete` — twisted-Edwards complete-addition denominator lemma.
//!
//! Recognizes the standard twisted-Edwards point-addition gadget (circomlib
//! `BabyAdd` shape) and, when its four input coordinates are known, marks both
//! output coordinates known. The cleared-denominator output constraints
//!
//! ```text
//!   xout · (1 + d·τ) = β + γ           yout · (1 − d·τ) = a·β − γ + δ
//!   τ = β·γ   β = x1·y2   γ = y1·x2     δ = (y1 − a·x1)(x2 + y2)
//! ```
//!
//! determine the outputs as rational functions whose denominators `1 ± d·τ`
//! never vanish on a solution: `1 + d·τ = 0` forces `(x1·y2)² = 1/d` and
//! `1 − d·τ = 0` forces `(x1·x2)² = 1/(a·d)`, both impossible when `a` is a
//! square and `d` a non-square in GF(p). This is the twisted-Edwards
//! completeness theorem (Bernstein & Lange, *Faster addition and doubling on
//! elliptic curves*, ASIACRYPT 2007). The certificate is two Legendre symbols
//! evaluated at runtime, so the lemma is sound for any prime / curve
//! parameters — not hard-coded to one curve.
//!
//! A wire is marked known only on a full structural match with the certificate
//! discharged; any deviation falls through (a sound miss costs only speed).
//! Wire-keyed: promotion relies on the matched constraints being mirrored in
//! both copies (the copy-symmetry invariant in `r1cs_to_poly_ir`); the matcher
//! runs on the `x_i` copy (all variables below `n_wires`).

use std::collections::BTreeMap;

use inventory;
use num_bigint::BigUint;
use picus_core::poly::IrPoly as Poly;
use picus_smt::poly_ir::PolyIR;

use super::lemma::{LemmaDescriptor, PropagationCtx, PropagationLemma};

/// A monomial: sorted `(wire, exponent)` pairs. The empty vector is the
/// constant monomial `1`.
type Mono = Vec<(usize, u16)>;
/// A polynomial as `monomial → coefficient`, zero coefficients dropped.
type TermMap = BTreeMap<Mono, BigUint>;

#[derive(Default)]
pub struct TecompleteLemma {
    gadgets: Option<Vec<Gadget>>,
    cached_len: Option<usize>,
}

struct Gadget {
    inputs: [usize; 4],
    outputs: [usize; 2],
}

impl PropagationLemma for TecompleteLemma {
    fn name(&self) -> &'static str {
        "tecomplete"
    }

    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool {
        let cur = ir.equalities.len();
        if self.gadgets.is_none() || self.cached_len != Some(cur) {
            self.gadgets = Some(find_gadgets(ir));
            self.cached_len = Some(cur);
        }
        let mut progress = false;
        for g in self.gadgets.as_ref().unwrap() {
            if !g.inputs.iter().all(|w| ctx.known.contains(w)) {
                continue;
            }
            for &out in &g.outputs {
                if !ctx.known.contains(&out) && ctx.unknown.remove(&out) {
                    ctx.known.insert(out);
                    progress = true;
                }
            }
        }
        progress
    }
}

/// Orig-copy term map of `poly`: `None` if any variable is an alt-copy wire
/// (index ≥ `n_wires`), restricting the matcher to the `x_i` copy. For the
/// orig copy a variable index equals its wire index.
fn orig_term_map(ir: &PolyIR, poly: &Poly) -> Option<TermMap> {
    let nw = ir.n_wires;
    let mut map = TermMap::new();
    for (c, vars) in ir.poly_terms_idx(poly) {
        let mut mono: Mono = Vec::with_capacity(vars.len());
        for (v, e) in vars {
            if v >= nw {
                return None;
            }
            mono.push((v, e));
        }
        mono.sort_unstable();
        if c != BigUint::from(0u32) {
            *map.entry(mono).or_insert_with(|| BigUint::from(0u32)) += c;
        }
    }
    Some(map)
}

/// `wire → {a, b}` for every constraint `wire − a·b = 0` (a product definition
/// with leading coefficient 1). Used to identify β, γ, τ and the input
/// products.
fn product_defs(polys: &[(usize, TermMap)], p: &BigUint) -> BTreeMap<usize, (usize, usize)> {
    let one = BigUint::from(1u32);
    let neg1 = p - 1u32;
    let mut defs = BTreeMap::new();
    for (_i, tm) in polys {
        if tm.len() != 2 {
            continue;
        }
        let mut def: Option<usize> = None;
        let mut prod: Option<(usize, usize)> = None;
        for (mono, c) in tm {
            match mono.as_slice() {
                [(w, 1)] if *c == one => def = Some(*w),
                [(a, 1), (b, 1)] if *c == neg1 => prod = Some((*a, *b)),
                _ => {}
            }
        }
        if let (Some(w), Some(ab)) = (def, prod) {
            defs.insert(w, ab);
        }
    }
    defs
}

/// Parse a constraint as a cleared denominator `v·(1 + cd·τ) − num = 0`:
/// returns `(v, cd, τ, num)`. `v` is the output wire — the member of the
/// constraint's unique quadratic monomial `[v, τ]` that also occurs in a bare
/// `(1,[v])` term; `num` is the negated `v`-free remainder. Product-definition
/// constraints (whose bare wire is not in the quadratic term) and constraints
/// with more than one quadratic term fall through.
fn as_denominator(tm: &TermMap, p: &BigUint) -> Option<(usize, BigUint, usize, TermMap)> {
    let one = BigUint::from(1u32);
    // The unique degree-2 monomial `[a, b]`; reject squared / higher-degree.
    let mut quad: Option<(usize, usize, BigUint)> = None;
    for (mono, c) in tm {
        match mono.as_slice() {
            [] | [(_, 1)] => {}
            [(a, 1), (b, 1)] => {
                if quad.is_some() {
                    return None;
                }
                quad = Some((*a, *b, c.clone()));
            }
            _ => return None,
        }
    }
    let (a, b, cd) = quad?;
    // `v` is whichever of a, b has a bare coefficient-1 term; τ is the other.
    let bare = |w: usize| tm.get(&vec![(w, 1u16)]);
    let (v, tau) = if bare(a) == Some(&one) {
        (a, b)
    } else if bare(b) == Some(&one) {
        (b, a)
    } else {
        return None;
    };
    // `v` must occur only in `[v]` and `[v, τ]`.
    for mono in tm.keys() {
        if mono.iter().any(|&(w, _)| w == v) {
            let ok = matches!(mono.as_slice(), [(w, 1)] if *w == v)
                || matches!(mono.as_slice(), [(x, 1), (y, 1)] if (*x == v && *y == tau) || (*y == v && *x == tau));
            if !ok {
                return None;
            }
        }
    }
    // num = −(terms free of v).
    let mut num = TermMap::new();
    for (mono, c) in tm {
        if !mono.iter().any(|&(w, _)| w == v) {
            num.insert(mono.clone(), (p - c) % p);
        }
    }
    Some((v, cd, tau, num))
}

/// Accumulate `c · monomial(k)` into `m`, reduced mod `p`.
fn add_term(m: &mut TermMap, mut k: Mono, c: &BigUint, p: &BigUint) {
    k.sort_unstable();
    let e = m.entry(k).or_insert_with(|| BigUint::from(0u32));
    *e = (&*e + c) % p;
}

/// Build the expected δ-defining constraint `wδ − (x2 + y2)(y1 − a·x1) = 0`
/// as a term map, for comparison against the actual constraint.
fn expected_delta(wd: usize, x1: usize, y1: usize, x2: usize, y2: usize, a: &BigUint, p: &BigUint) -> TermMap {
    let one = BigUint::from(1u32);
    let neg1 = p - 1u32;
    let mut m = TermMap::new();
    // wδ − (x2·y1 + y2·y1 − a·x2·x1 − a·y2·x1)
    add_term(&mut m, vec![(wd, 1)], &one, p);
    add_term(&mut m, vec![(x2, 1), (y1, 1)], &neg1, p);
    add_term(&mut m, vec![(y2, 1), (y1, 1)], &neg1, p);
    add_term(&mut m, vec![(x2, 1), (x1, 1)], a, p);
    add_term(&mut m, vec![(y2, 1), (x1, 1)], a, p);
    m.retain(|_, c| *c != BigUint::from(0u32));
    m
}

fn legendre(field: &picus_core::ff::field::PrimeField, x: &BigUint, p: &BigUint) -> i32 {
    if x % p == BigUint::from(0u32) {
        return 0;
    }
    let e = field.pow(&field.from_biguint(x), &((p - 1u32) / 2u32));
    let b = field.to_biguint(&e);
    if b == BigUint::from(1u32) {
        1
    } else {
        -1
    }
}

fn find_gadgets(ir: &PolyIR) -> Vec<Gadget> {
    let field = ir.ring.field();
    let p = field.prime().clone();
    let one = BigUint::from(1u32);

    let polys: Vec<(usize, TermMap)> = ir
        .equalities
        .iter()
        .enumerate()
        .filter_map(|(i, poly)| orig_term_map(ir, poly).map(|tm| (i, tm)))
        .collect();
    let pdef = product_defs(&polys, &p);

    // Collect denominator constraints: (v, cd, τ, num).
    let dens: Vec<(usize, BigUint, usize, TermMap)> =
        polys.iter().filter_map(|(_i, tm)| as_denominator(tm, &p)).collect();

    let mut gadgets = Vec::new();

    // x-output: den `1 + d·τ`, num = β + γ (two wires, coeff 1 each).
    for (xout, d, tau, num1) in &dens {
        // num1 must be exactly two coeff-1 single-wire terms.
        let beta_gamma: Vec<usize> = num1
            .iter()
            .filter_map(|(m, c)| match (m.as_slice(), c == &one) {
                ([(w, 1)], true) => Some(*w),
                _ => None,
            })
            .collect();
        if beta_gamma.len() != 2 || num1.len() != 2 {
            continue;
        }
        // τ = β·γ.
        let tau_def = match pdef.get(tau) {
            Some(&(a, b)) => [a, b],
            None => continue,
        };
        let mut bg = beta_gamma.clone();
        bg.sort_unstable();
        let mut td = tau_def;
        td.sort_unstable();
        if bg != td {
            continue;
        }

        // y-output: a den `1 − d·τ` (coeff = −d, same τ) with
        // num2 = a·β − γ + δ for the SAME {β,γ} and some δ, a.
        let neg_d = (&p - d) % &p;
        for (yout, cd2, tau2, num2) in &dens {
            if yout == xout || tau2 != tau || *cd2 != neg_d {
                continue;
            }
            // num2 must be {(a,[β]), (−1,[γ]), (1,[δ])} for one ordering of β,γ.
            for &(beta, gamma) in &[(beta_gamma[0], beta_gamma[1]), (beta_gamma[1], beta_gamma[0])] {
                let (a, wd) = match read_num2(num2, beta, gamma, &p) {
                    Some(v) => v,
                    None => continue,
                };
                // β, γ each a product of two inputs.
                let (bp, gp) = match (pdef.get(&beta), pdef.get(&gamma)) {
                    (Some(&bp), Some(&gp)) => (bp, gp),
                    _ => continue,
                };
                // δ = (x2 + y2)(y1 − a·x1) for some role assignment with
                // β = x1·y2 (β-pair) and γ = y1·x2 (γ-pair).
                let actual_delta = polys.iter().find_map(|(_i, tm)| {
                    if tm.get(&vec![(wd, 1u16)]) == Some(&one) {
                        Some(tm)
                    } else {
                        None
                    }
                });
                let actual_delta = match actual_delta {
                    Some(t) => t,
                    None => continue,
                };
                let mut matched: Option<[usize; 4]> = None;
                'roles: for &(x1, y2) in &[(bp.0, bp.1), (bp.1, bp.0)] {
                    for &(y1, x2) in &[(gp.0, gp.1), (gp.1, gp.0)] {
                        if expected_delta(wd, x1, y1, x2, y2, &a, &p) == *actual_delta {
                            matched = Some([x1, y1, x2, y2]);
                            break 'roles;
                        }
                    }
                }
                let inputs = match matched {
                    Some(i) => i,
                    None => continue,
                };
                // Certificate: a square, d non-square (⇒ a·d non-square too).
                if legendre(field, &a, &p) == 1 && legendre(field, d, &p) == -1 {
                    gadgets.push(Gadget {
                        inputs,
                        outputs: [*xout, *yout],
                    });
                }
            }
        }
    }
    gadgets
}

/// Match `num2 = a·β − γ + δ`: returns `(a, δ)` if `num2` is exactly
/// `{(a,[β]), (−1,[γ]), (1,[δ])}` for the given β, γ.
fn read_num2(num2: &TermMap, beta: usize, gamma: usize, p: &BigUint) -> Option<(BigUint, usize)> {
    if num2.len() != 3 {
        return None;
    }
    let one = BigUint::from(1u32);
    let neg1 = p - 1u32;
    if num2.get(&vec![(gamma, 1u16)]) != Some(&neg1) {
        return None;
    }
    let a = num2.get(&vec![(beta, 1u16)])?.clone();
    // δ is the remaining coeff-1 single-wire term, distinct from β, γ.
    let mut delta: Option<usize> = None;
    for (m, c) in num2 {
        if let [(w, 1)] = m.as_slice() {
            if *w != beta && *w != gamma && *c == one {
                if delta.is_some() {
                    return None;
                }
                delta = Some(*w);
            }
        }
    }
    delta.map(|d| (a, d))
}

inventory::submit! {
    LemmaDescriptor {
        name: "tecomplete",
        factory: || Box::new(TecompleteLemma::default()),
    }
}

#[cfg(test)]
#[path = "tecomplete_tests.rs"]
mod tests;
