//! Basis2 propagation lemma — binary decomposition detection.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::grammar::*;
use picus_r1cs::{bn128_prime, parse_var_index};
use std::collections::HashSet;

use super::binary01::RangeValue;

/// Apply the basis2 lemma. Mutates `ks` and `us` in place.
pub fn apply_lemma(
    ks: &mut HashSet<usize>,
    us: &mut HashSet<usize>,
    cnsts: &RCmds,
    range_vec: &[RangeValue],
) {
    let p = bn128_prime();

    for cmd in &cnsts.commands {
        if let RCmd::Assert(expr) = cmd
            && let Some((target_sig, bit_sigs, _)) = match_basis2_pattern(expr, p) {
                let all_binary = bit_sigs
                    .iter()
                    .all(|&s| s < range_vec.len() && range_vec[s].is_binary());

                if !all_binary {
                    continue;
                }

                if ks.contains(&target_sig) {
                    for &s in &bit_sigs {
                        if us.remove(&s) {
                            ks.insert(s);
                        }
                    }
                }
            }
    }
}

fn match_basis2_pattern(
    expr: &RExpr,
    _p: &BigUint,
) -> Option<(usize, Vec<usize>, Vec<BigUint>)> {
    if let RExpr::Eq(lhs, rhs) = expr {
        let (_, sum_side) = if lhs.is_zero() {
            (lhs.as_ref(), rhs.as_ref())
        } else if rhs.is_zero() {
            (rhs.as_ref(), lhs.as_ref())
        } else {
            return None;
        };

        let inner = sum_side.strip_mod();

        if let RExpr::Add(terms) = inner {
            let mut target_sig = None;
            let mut bit_sigs = Vec::new();
            let mut coeffs = Vec::new();

            for term in terms {
                match term {
                    RExpr::Var(name) => {
                        if let Some(id) = parse_var_index(name) {
                            target_sig = Some(id);
                        }
                    }
                    RExpr::Mul(mul_args) => {
                        if let Some((coeff, sig)) = extract_coeff_var(mul_args) {
                            bit_sigs.push(sig);
                            coeffs.push(coeff);
                        } else {
                            return None;
                        }
                    }
                    RExpr::Int(v) if v.is_zero() => {}
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
    if args.len() != 2 {
        return None;
    }
    // Try (Int(coeff), Var(signal))
    if let (RExpr::Int(coeff), RExpr::Var(name)) = (&args[0], &args[1])
        && let Some(id) = parse_var_index(name) {
            return Some((coeff.clone(), id));
        }
    // Try (Var(named_const), Var(signal)) — after subp optimization,
    // numeric constants like p-1 become Var("ps1")
    if let (RExpr::Var(const_name), RExpr::Var(sig_name)) = (&args[0], &args[1]) {
        if let (Some(coeff), Some(id)) = (super::resolve_named_constant(const_name), parse_var_index(sig_name)) {
            return Some((coeff, id));
        }
        // Try reverse: signal first, constant second
        if let (Some(id), Some(coeff)) = (parse_var_index(const_name), super::resolve_named_constant(sig_name)) {
            return Some((coeff, id));
        }
    }
    None
}

/// Resolve named constants introduced by the subp optimizer.

fn is_power_of_2_sequence(coeffs: &[BigUint]) -> bool {
    // Check if the coefficient set equals {2^0, 2^1, ..., 2^(n-1)}
    // after field normalization (each coeff or its negation is a power of 2).
    use std::collections::HashSet;
    let p = bn128_prime();
    let expected: HashSet<BigUint> = (0..coeffs.len())
        .map(|k| BigUint::from(1u32) << k)
        .collect();

    let actual: HashSet<BigUint> = coeffs
        .iter()
        .map(|c| {
            let neg = p - c;
            // Take whichever IS a power of 2
            if is_power_of_2(c) {
                c.clone()
            } else if is_power_of_2(&neg) {
                neg
            } else {
                c.clone() // neither — will fail the check
            }
        })
        .collect();

    actual == expected
}

fn is_power_of_2(n: &BigUint) -> bool {
    !n.is_zero() && (n & (n - BigUint::one())).is_zero()
}
