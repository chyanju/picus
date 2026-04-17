//! L2: Basis2 lemma — binary decomposition detection.
//!
//! If z = 2^0*x_0 + 2^1*x_1 + ... + 2^n*x_n, all x_i ∈ {0,1}, and z is known,
//! then all x_i are known.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::bn128_prime;
use picus_r1cs::grammar::*;
use std::collections::{BTreeSet, HashSet};

use super::binary01::{self, RangeValue};

/// Precompute valid power-of-2 coefficient sets: {{1}, {1,2}, {1,2,4}, ..., {1,2,...,2^252}}.
fn basis2_sequences() -> HashSet<BTreeSet<BigUint>> {
    let mut seqs = HashSet::new();
    let mut current = BTreeSet::new();
    let mut power = BigUint::one();
    let p = bn128_prime();

    for _ in 0..253 {
        current.insert(power.clone());
        seqs.insert(current.clone());
        power = (&power * 2u32) % &p;
    }
    seqs
}

/// Apply the basis2 lemma.
pub fn apply_lemma(
    mut ks: HashSet<usize>,
    mut us: HashSet<usize>,
    cnsts: &RCmds,
    range_vec: &[RangeValue],
) -> (HashSet<usize>, HashSet<usize>) {
    let p = bn128_prime();
    let _seqs = basis2_sequences();

    for cmd in &cnsts.vs {
        if let RCmd::Assert(expr) = cmd
            && let Some((target_sig, bit_sigs, _)) = match_basis2_pattern(expr, &p) {
                // Check all bit signals are binary
                let all_binary = bit_sigs
                    .iter()
                    .all(|&s| s < range_vec.len() && range_vec[s].is_binary());

                if !all_binary {
                    continue;
                }

                // Check coefficient set matches a basis2 sequence
                // (simplified: we check in the match function)

                // If target signal is known, all bit signals become known
                if ks.contains(&target_sig) {
                    for &s in &bit_sigs {
                        if us.contains(&s) {
                            ks.insert(s);
                            us.remove(&s);
                        }
                    }
                }
            }
    }

    (ks, us)
}

/// Match pattern: 0 = x_target + c1*x1 + c2*x2 + ... where coefficients are powers of 2.
/// Returns (target_signal, bit_signals, coefficients).
fn match_basis2_pattern(
    expr: &RExpr,
    p: &BigUint,
) -> Option<(usize, Vec<usize>, Vec<BigUint>)> {
    // Match: Eq(lhs, rhs) where one side is 0
    if let RExpr::Eq(lhs, rhs) = expr {
        let (_zero_side, sum_side) = if is_zero_like(lhs) {
            (lhs, rhs)
        } else if is_zero_like(rhs) {
            (rhs, lhs)
        } else {
            return None;
        };

        let inner = strip_mod(sum_side);

        // inner should be Add([Var(x_target), Mul([Int(c1), Var(x1)]), ...])
        if let RExpr::Add(terms) = inner {
            let mut target_sig = None;
            let mut bit_sigs = Vec::new();
            let mut coeffs = Vec::new();

            for term in terms {
                match term {
                    RExpr::Var(name) => {
                        if let Some(id) = binary01::parse_var_index(name) {
                            target_sig = Some(id);
                        }
                    }
                    RExpr::Mul(mul_args) => {
                        if let Some((coeff, sig)) = extract_coeff_var(mul_args) {
                            bit_sigs.push(sig);
                            // Check if coefficient or p-coefficient is a power of 2
                            let neg_coeff = p - &coeff;
                            coeffs.push(coeff.min(neg_coeff));
                        }
                    }
                    RExpr::Int(v) if v.is_zero() => {} // skip leading zero
                    _ => return None,
                }
            }

            if let Some(target) = target_sig
                && !bit_sigs.is_empty() && is_power_of_2_sequence(&coeffs) {
                    return Some((target, bit_sigs, coeffs));
                }
        }
    }
    None
}

fn extract_coeff_var(args: &[RExpr]) -> Option<(BigUint, usize)> {
    if args.len() == 2
        && let (RExpr::Int(coeff), RExpr::Var(name)) = (&args[0], &args[1])
            && let Some(id) = binary01::parse_var_index(name) {
                return Some((coeff.clone(), id));
            }
    None
}

fn is_power_of_2_sequence(coeffs: &[BigUint]) -> bool {
    let sorted: BTreeSet<BigUint> = coeffs.iter().cloned().collect();
    let mut expected = BigUint::one();
    for c in &sorted {
        if c != &expected {
            return false;
        }
        expected *= 2u32;
    }
    true
}

fn is_zero_like(expr: &RExpr) -> bool {
    match strip_mod(expr) {
        RExpr::Int(v) => v.is_zero(),
        RExpr::Add(vs) if vs.len() == 1 => is_zero_like(&vs[0]),
        _ => false,
    }
}

fn strip_mod(expr: &RExpr) -> &RExpr {
    if let RExpr::Mod(inner, _) = expr {
        inner.as_ref()
    } else {
        expr
    }
}
