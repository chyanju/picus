//! L4: Big Integer Multiply lemma — linear algebra over constraints.
//!
//! If a set of constraints forms Ax = 0 where A is square and det(A) ≠ 0,
#![allow(clippy::needless_range_loop)]
//! then all signals in x are uniquely determined.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::bn128_prime;
use picus_r1cs::grammar::*;
use std::collections::{HashMap, HashSet};

use super::binary01;

/// Apply the BIM lemma.
pub fn apply_lemma(
    mut ks: HashSet<usize>,
    mut us: HashSet<usize>,
    cnsts: &RCmds,
    _range_vec: &[super::binary01::RangeValue],
) -> (HashSet<usize>, HashSet<usize>) {
    let p = bn128_prime();

    // Collect all linear homogeneous constraints: 0 = a1*x1 + a2*x2 + ...
    let mut equations: Vec<Vec<(usize, BigUint)>> = Vec::new();

    for cmd in &cnsts.vs {
        if let RCmd::Assert(expr) = cmd
            && let Some(terms) = match_linear_homogeneous(expr)
                && !terms.is_empty() {
                    equations.push(terms);
                }
    }

    if equations.is_empty() {
        return (ks, us);
    }

    // Group equations by the set of signals involved
    // Try to find square subsystems
    let all_sigs: HashSet<usize> = equations
        .iter()
        .flat_map(|eq| eq.iter().map(|(s, _)| *s))
        .collect();

    // Simple case: if #equations == #signals and all signals unknown
    if equations.len() == all_sigs.len() && all_sigs.iter().all(|s| us.contains(s)) {
        // Build matrix and check determinant
        let sig_list: Vec<usize> = all_sigs.iter().copied().collect();
        let n = sig_list.len();
        let sig_idx: HashMap<usize, usize> = sig_list.iter().enumerate().map(|(i, &s)| (s, i)).collect();

        let mut matrix: Vec<Vec<BigUint>> = vec![vec![BigUint::zero(); n]; n];
        for (row, eq) in equations.iter().enumerate() {
            if row >= n {
                break;
            }
            for (sig, coeff) in eq {
                if let Some(&col) = sig_idx.get(sig) {
                    matrix[row][col] = coeff.clone();
                }
            }
        }

        // Compute determinant (mod p)
        if let Some(det) = matrix_det_mod(&matrix, &p)
            && !det.is_zero() {
                // All signals are uniquely determined
                for &sig in &all_sigs {
                    if us.contains(&sig) {
                        ks.insert(sig);
                        us.remove(&sig);
                    }
                }
            }
    }

    (ks, us)
}

/// Match pattern: Eq(zero, Add([Mul([coeff, var]), ...])) or similar.
fn match_linear_homogeneous(expr: &RExpr) -> Option<Vec<(usize, BigUint)>> {
    if let RExpr::Eq(lhs, rhs) = expr {
        let (_zero_side, sum_side) = if is_zero_like(lhs) {
            (lhs, rhs)
        } else if is_zero_like(rhs) {
            (rhs, lhs)
        } else {
            return None;
        };

        let inner = strip_mod(sum_side);
        if let RExpr::Add(terms) = inner {
            let mut result = Vec::new();
            for term in terms {
                match term {
                    RExpr::Int(v) if v.is_zero() => {} // skip zero
                    RExpr::Mul(args) => {
                        if let Some((coeff, sig)) = extract_coeff_sig(args) {
                            result.push((sig, coeff));
                        } else {
                            return None; // nonlinear term
                        }
                    }
                    RExpr::Var(name) => {
                        if let Some(id) = binary01::parse_var_index(name) {
                            result.push((id, BigUint::one()));
                        } else {
                            return None;
                        }
                    }
                    _ => return None,
                }
            }
            return Some(result);
        }
    }
    None
}

fn extract_coeff_sig(args: &[RExpr]) -> Option<(BigUint, usize)> {
    // Mul([Int(coeff), Var(name)]) — exactly 2 args, one int, one var
    if args.len() != 2 {
        return None;
    }
    match (&args[0], &args[1]) {
        (RExpr::Int(c), RExpr::Var(name)) => {
            binary01::parse_var_index(name).map(|id| (c.clone(), id))
        }
        (RExpr::Var(name), RExpr::Int(c)) => {
            binary01::parse_var_index(name).map(|id| (c.clone(), id))
        }
        _ => None,
    }
}

/// Compute determinant of a matrix modulo p using Gaussian elimination.
fn matrix_det_mod(matrix: &[Vec<BigUint>], p: &BigUint) -> Option<BigUint> {
    let n = matrix.len();
    if n == 0 || matrix[0].len() != n {
        return None;
    }

    let mut m: Vec<Vec<BigUint>> = matrix.to_vec();
    let mut det = BigUint::one();
    let mut sign_flip = false;

    for col in 0..n {
        // Find pivot
        let mut pivot = None;
        for row in col..n {
            if !m[row][col].is_zero() {
                pivot = Some(row);
                break;
            }
        }

        let pivot = match pivot {
            Some(p) => p,
            None => return Some(BigUint::zero()), // singular
        };

        if pivot != col {
            m.swap(pivot, col);
            sign_flip = !sign_flip;
        }

        det = (&det * &m[col][col]) % p;

        // Eliminate below
        let pivot_inv = mod_inverse(&m[col][col], p)?;
        for row in (col + 1)..n {
            if m[row][col].is_zero() {
                continue;
            }
            let factor = (&m[row][col] * &pivot_inv) % p;
            for j in col..n {
                let sub = (&factor * &m[col][j]) % p;
                m[row][j] = if m[row][j] >= sub {
                    (&m[row][j] - &sub) % p
                } else {
                    (p - &((&sub - &m[row][j]) % p)) % p
                };
            }
        }
    }

    if sign_flip {
        det = (p - &det) % p;
    }
    Some(det)
}

/// Compute modular inverse using extended GCD.
fn mod_inverse(a: &BigUint, p: &BigUint) -> Option<BigUint> {
    use num_integer::Integer;
    use num_bigint::BigInt;
    

    let a_int = BigInt::from(a.clone());
    let p_int = BigInt::from(p.clone());
    let gcd = a_int.extended_gcd(&p_int);

    if gcd.gcd != BigInt::one() {
        return None;
    }

    let inv = ((gcd.x % &p_int) + &p_int) % &p_int;
    Some(inv.to_biguint().unwrap())
}

fn is_zero_like(expr: &RExpr) -> bool {
    match strip_mod(expr) {
        RExpr::Int(v) => v.is_zero(),
        RExpr::Var(name) => name == "zero",
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
