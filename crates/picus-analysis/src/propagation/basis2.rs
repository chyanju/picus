//! Basis2 propagation lemma — binary decomposition pattern.
//!
//! Recognises polynomial equalities of the form
//! `target + sum_i (-2^i) * bit_i = 0` (equivalently
//! `target = sum_i 2^i * bit_i`), where every `bit_i` has already been
//! pinned to `{0, 1}` by [`super::binary01::Binary01Lemma`]. When
//! `target` is known the bits are recoverable bit-by-bit and so are
//! also known.

use std::collections::HashSet;

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::bn128_prime;
use picus_smt::poly_ir::PolyIR;

use super::lemma::{LemmaDescriptor, PropagationCtx, PropagationLemma};

#[derive(Default)]
pub struct Basis2Lemma;

impl PropagationLemma for Basis2Lemma {
    fn name(&self) -> &'static str {
        "basis2"
    }

    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool {
        let mut progress = false;
        for poly in &ir.equalities {
            if let Some((target_wire, bit_wires)) = match_basis2_pattern(ir, poly) {
                let all_binary = bit_wires
                    .iter()
                    .all(|w| matches!(ctx.ranges.get(w), Some(r) if r.is_binary()));
                if !all_binary {
                    continue;
                }
                if ctx.known.contains(&target_wire) {
                    for &bit in &bit_wires {
                        if ctx.unknown.remove(&bit) {
                            ctx.known.insert(bit);
                            progress = true;
                        }
                    }
                }
            }
        }
        progress
    }
}

/// Match `c0 * target + sum_i c_i * bit_i = 0`, where `c0` is ±1 (mod
/// p) and `{c_i / c0}` (after sign normalisation) form a power-of-2
/// sequence. Returns `(target_wire, [bit_wires])`.
fn match_basis2_pattern(
    ir: &PolyIR,
    poly: &picus_solver::poly::Poly,
) -> Option<(usize, Vec<usize>)> {
    let ring = &ir.ring.ring;
    let n_vars = ring.n_vars();
    let field = &ir.ring.field;
    let p = bn128_prime();

    // Collect linear-only terms (each containing exactly one variable
    // at exponent 1).
    let mut terms: Vec<(BigUint, usize)> = Vec::new();
    for (c, m) in ring.terms(poly) {
        let mut single_var = None;
        let mut total_deg = 0usize;
        for v in 0..n_vars {
            let e = ring.exponent_at(&m, v);
            total_deg += e;
            if e > 0 {
                if single_var.is_some() {
                    return None; // Multiple vars in a term ⇒ not basis2 shape.
                }
                if e != 1 {
                    return None;
                }
                single_var = Some(v);
            }
        }
        if total_deg == 0 {
            // Constant term: must be zero.
            if !field.to_biguint(c).is_zero() {
                return None;
            }
            continue;
        }
        let var = single_var?;
        let coeff = field.to_biguint(c);
        terms.push((coeff, var));
    }
    if terms.len() < 2 {
        return None;
    }

    // The target term has coefficient ±1; the rest have power-of-2-ish
    // coefficients (possibly negated). Try every term as the candidate
    // target and check the rest.
    let one = BigUint::one();
    let p_minus_1 = &(p - &one);
    for cand in 0..terms.len() {
        let (cand_coeff, cand_var) = &terms[cand];
        let target_sign = if cand_coeff == &one {
            Sign::Pos
        } else if cand_coeff == p_minus_1 {
            Sign::Neg
        } else {
            continue;
        };
        let mut bit_coeffs: Vec<BigUint> = Vec::with_capacity(terms.len() - 1);
        let mut bit_vars: Vec<usize> = Vec::with_capacity(terms.len() - 1);
        for (i, (c, v)) in terms.iter().enumerate() {
            if i == cand {
                continue;
            }
            // Bit's effective coefficient is `c / target_sign * (-1)`,
            // since `target + sum c_i bit_i = 0 ⇒ target = -sum c_i bit_i`,
            // and we want the bit weights as positive 2^k.
            let bit_coeff = match target_sign {
                Sign::Pos => p - c,
                Sign::Neg => c.clone(),
            } % p;
            bit_coeffs.push(bit_coeff);
            bit_vars.push(*v);
        }
        if is_power_of_2_sequence(&bit_coeffs) {
            let target_wire = var_to_wire(ir, *cand_var);
            let mut wires: Vec<usize> = bit_vars.iter().map(|&v| var_to_wire(ir, v)).collect();
            wires.sort();
            wires.dedup();
            return Some((target_wire, wires));
        }
    }
    None
}

enum Sign {
    Pos,
    Neg,
}

fn is_power_of_2_sequence(coeffs: &[BigUint]) -> bool {
    let mut s: HashSet<BigUint> = HashSet::new();
    for c in coeffs {
        if !is_power_of_2(c) {
            return false;
        }
        s.insert(c.clone());
    }
    let expected: HashSet<BigUint> = (0..coeffs.len()).map(|k| BigUint::from(1u32) << k).collect();
    s == expected
}

fn is_power_of_2(n: &BigUint) -> bool {
    !n.is_zero() && (n & (n - BigUint::one())).is_zero()
}

fn var_to_wire(ir: &PolyIR, var: usize) -> usize {
    if var < ir.n_wires {
        var
    } else {
        var - ir.n_wires
    }
}

inventory::submit! {
    LemmaDescriptor {
        name: "basis2",
        factory: || Box::new(Basis2Lemma::default()),
    }
}
