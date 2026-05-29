//! Basis2 propagation lemma — binary decomposition pattern.
//!
//! Recognises polynomial equalities of the form
//! `target + sum_i (-2^i) * bit_i = 0` (equivalently
//! `target = sum_i 2^i * bit_i`), where every `bit_i` has already been
//! pinned to `{0, 1}` by [`super::binary01::Binary01Lemma`]. When
//! `target` is known the bits are recoverable bit-by-bit and so are
//! also known.
//!
//! Wire-keyed: promoting the bit/target wires to known relies on the
//! decomposition being mirrored in both copies (the copy-symmetry
//! invariant documented in `picus_smt::poly_ir::r1cs_to_poly_ir`).
//!
//! Soundness depends on `2^n <= p`, where `n` is the number of bits.
//! When `2^n > p` two distinct bit assignments can sum to the same
//! target modulo `p` (e.g. `0` and `(1,1,...,1)` with `2^n - 1 ≡ 0
//! mod p`), so target uniqueness no longer implies bit uniqueness. The
//! lemma checks this bound before firing.
//!
//! ## Relaxing the gate when a range-check companion is present
//!
//! A `2^n > p` decomposition is still safe to propagate if some other
//! constraint forces the bit-vector's *integer* value `X = Σ 2^j b_j`
//! below `p`: then `X` is already reduced, two witnesses with the same
//! target share the same integer `X`, and an integer has a unique
//! binary expansion — so the bits are determined. Circomlib's strict
//! gadgets supply exactly this bound via `AliasCheck`, which is a
//! 254-bit `CompConstant(ct)` whose output is constrained to `0`.
//!
//! [`companion_proves_below_prime`] recognises that comparator purely
//! from the PolyIR polynomial structure (no gadget names): it matches
//! the 127 quadratic `parts`, the parts-sum, the inner bit
//! decomposition of that sum, and the forced-zero output, decodes the
//! constant `ct` from the part coefficients, and checks `ct < p`.
//!
//! Soundness of the relaxation (verified empirically on the real
//! lowered gadget over 5000 random + all boundary inputs): with
//! `a_i = 2^i`, `b_i = 2^128 - 2^i`, each `parts_i` evaluates to `b_i`
//! when its base-4 digit `d_i > c_i`, `0` when `d_i = c_i`, `a_i` when
//! `d_i < c_i` (where `ct = Σ 4^i c_i`). Writing the sum
//! `S = G·2^128 + R` with `R = Σ 2^i (l_i − g_i)` and `|R| < 2^127`,
//! bit 127 of `S` is `[R < 0] = [X > ct]` (the sign of `R` is fixed by
//! the most-significant differing digit). The inner decomposition is
//! faithful (`2^135 ≤ p`), so its bit-127 signal *is* `[X > ct]`;
//! forcing it to `0` gives `X ≤ ct`, and `ct < p` gives `X < p`. Only a
//! complete match relaxes the gate; any missing link keeps the
//! conservative gate (a miss is slow, never unsound).

use std::collections::HashMap;

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_smt::poly_ir::PolyIR;
use picus_core::poly::IrPoly as Poly;

use super::lemma::{LemmaDescriptor, PropagationCtx, PropagationLemma};

mod compconstant;
use compconstant::companion_proves_below_prime;

#[derive(Default)]
pub struct Basis2Lemma;

impl PropagationLemma for Basis2Lemma {
    fn name(&self) -> &'static str {
        "basis2"
    }

    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool {
        let p = ir.ring.field().prime();
        let mut progress = false;
        for poly in &ir.equalities {
            let Some(decomp) = match_decomp(ir, poly) else {
                continue;
            };
            let bit_wires: Vec<usize> = decomp.bits.iter().map(|&v| ir.var_to_wire(v)).collect();
            // Every bit must already be pinned to {0, 1}.
            let all_binary = bit_wires
                .iter()
                .all(|w| matches!(ctx.ranges.get(w), Some(r) if r.is_binary()));
            if !all_binary {
                continue;
            }
            // Soundness gate: `2^n > p` admits colliding bit patterns
            // under mod-p reduction. Relax only when a recognised
            // companion proves the bit-vector value `< p`.
            let two_pow_n: BigUint = BigUint::one() << decomp.bits.len();
            if &two_pow_n > p && !companion_proves_below_prime(ir, &decomp.bits, ctx.ranges) {
                continue;
            }
            let target_wire = ir.var_to_wire(decomp.target_var);
            if ctx.known.contains(&target_wire) {
                for &bit in &bit_wires {
                    if ctx.unknown.remove(&bit) {
                        ctx.known.insert(bit);
                        progress = true;
                    }
                }
            }
        }
        progress
    }
}

/// A recognised binary decomposition `target = Σ 2^k · bits[k]`.
struct Decomp {
    /// Ring-variable index of the target.
    target_var: usize,
    /// `bits[k]` is the ring-variable index of the weight-`2^k` bit.
    bits: Vec<usize>,
}

/// Match `c0 * target + sum_i c_i * bit_i = 0`, where `c0` is ±1 (mod
/// p) and the remaining coefficients (after sign normalisation) are a
/// power-of-2 sequence covering `2^0 .. 2^{n-1}` exactly once. Returns
/// the target and the bit variables indexed by weight.
fn match_decomp(ir: &PolyIR, poly: &Poly) -> Option<Decomp> {
    let p = ir.ring.field().prime();
    let one = BigUint::one();

    // Collect linear-only terms; reject any non-linear monomial; any
    // constant term must be zero.
    let mut terms: Vec<(BigUint, usize)> = Vec::new();
    for (coeff, vars) in ir.poly_terms_idx(poly) {
        if vars.is_empty() {
            if !coeff.is_zero() {
                return None;
            }
            continue;
        }
        if vars.len() != 1 || vars[0].1 != 1 {
            return None;
        }
        terms.push((coeff, vars[0].0));
    }
    if terms.len() < 2 {
        return None;
    }

    let p_minus_1 = &(p - &one);
    for cand in 0..terms.len() {
        let (cand_coeff, cand_var) = &terms[cand];
        // Target coefficient must be ±1.
        let neg = if cand_coeff == &one {
            false
        } else if cand_coeff == p_minus_1 {
            true
        } else {
            continue;
        };
        let mut by_weight: HashMap<usize, usize> = HashMap::new();
        let mut ok = true;
        for (i, (c, v)) in terms.iter().enumerate() {
            if i == cand {
                continue;
            }
            // `target = -Σ c_i bit_i`; the bit's positive weight is
            // `-c_i / c0`. With `c0 = +1` that is `p - c_i`; with
            // `c0 = -1` it is `c_i`.
            let bit_coeff = if neg { c.clone() } else { (p - c) % p };
            if !is_power_of_2(&bit_coeff) {
                ok = false;
                break;
            }
            let exp = bit_coeff.bits() as usize - 1;
            if by_weight.insert(exp, *v).is_some() {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        // Weights must be exactly `0 .. count-1`.
        let count = by_weight.len();
        let mut bits = Vec::with_capacity(count);
        let mut contiguous = true;
        for k in 0..count {
            match by_weight.get(&k) {
                Some(&v) => bits.push(v),
                None => {
                    contiguous = false;
                    break;
                }
            }
        }
        if contiguous {
            return Some(Decomp {
                target_var: *cand_var,
                bits,
            });
        }
    }
    None
}


fn is_power_of_2(n: &BigUint) -> bool {
    !n.is_zero() && (n & (n - BigUint::one())).is_zero()
}

inventory::submit! {
    LemmaDescriptor {
        name: "basis2",
        factory: || Box::new(Basis2Lemma::default()),
    }
}

#[cfg(test)]
#[path = "basis2_tests.rs"]
mod tests;
