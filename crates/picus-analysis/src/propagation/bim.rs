//! Big Integer Multiply (BIM) propagation lemma — linear algebra over constraints.
#![allow(clippy::needless_range_loop)]

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};
use picus_r1cs::grammar::*;
use picus_r1cs::{bn128_prime, parse_var_index};
use std::collections::{HashMap, HashSet};

use super::binary01::RangeValue;

/// Apply the BIM lemma. Mutates `ks` and `us` in place.
pub fn apply_lemma(
    ks: &mut HashSet<usize>,
    us: &mut HashSet<usize>,
    cnsts: &RCmds,
    _range_vec: &[RangeValue],
) {
    let p = bn128_prime();

    let mut equations: Vec<Vec<(usize, BigUint)>> = Vec::new();
    for cmd in &cnsts.commands {
        if let RCmd::Assert(expr) = cmd
            && let Some(terms) = match_linear_homogeneous(expr)
                && !terms.is_empty() {
                    equations.push(terms);
                }
    }

    if equations.is_empty() {
        return;
    }

    let all_sigs: HashSet<usize> = equations
        .iter()
        .flat_map(|eq| eq.iter().map(|(s, _)| *s))
        .collect();

    if equations.len() == all_sigs.len() && all_sigs.iter().all(|s| us.contains(s)) {
        let sig_list: Vec<usize> = all_sigs.iter().copied().collect();
        let n = sig_list.len();
        let sig_idx: HashMap<usize, usize> =
            sig_list.iter().enumerate().map(|(i, &s)| (s, i)).collect();

        let mut matrix: Vec<Vec<BigUint>> = vec![vec![BigUint::zero(); n]; n];
        for (row, eq) in equations.iter().enumerate() {
            if row >= n { break; }
            for (sig, coeff) in eq {
                if let Some(&col) = sig_idx.get(sig) {
                    matrix[row][col] = coeff.clone();
                }
            }
        }

        if let Some(det) = matrix_det_mod(&matrix, p)
            && !det.is_zero() {
                for &sig in &all_sigs {
                    if us.remove(&sig) {
                        ks.insert(sig);
                    }
                }
            }
    }
}

fn match_linear_homogeneous(expr: &RExpr) -> Option<Vec<(usize, BigUint)>> {
    if let RExpr::Eq(lhs, rhs) = expr {
        let sum_side = if lhs.is_zero() {
            rhs.as_ref()
        } else if rhs.is_zero() {
            lhs.as_ref()
        } else {
            return None;
        };

        let inner = sum_side.strip_mod();
        if let RExpr::Add(terms) = inner {
            let mut result = Vec::new();
            for term in terms {
                match term {
                    RExpr::Int(v) if v.is_zero() => {}
                    RExpr::Mul(args) => {
                        let pair = extract_coeff_sig(args)?;
                        result.push(pair);
                    }
                    RExpr::Var(name) => {
                        let id = parse_var_index(name)?;
                        result.push((id, BigUint::one()));
                    }
                    _ => return None,
                }
            }
            return Some(result);
        }
    }
    None
}

fn extract_coeff_sig(args: &[RExpr]) -> Option<(usize, BigUint)> {
    if args.len() != 2 { return None; }
    match (&args[0], &args[1]) {
        (RExpr::Int(c), RExpr::Var(name)) | (RExpr::Var(name), RExpr::Int(c)) => {
            parse_var_index(name).map(|id| (id, c.clone()))
        }
        _ => None,
    }
}

fn matrix_det_mod(matrix: &[Vec<BigUint>], p: &BigUint) -> Option<BigUint> {
    let n = matrix.len();
    if n == 0 || matrix[0].len() != n { return None; }

    let mut m: Vec<Vec<BigUint>> = matrix.to_vec();
    let mut det = BigUint::one();
    let mut sign_flip = false;

    for col in 0..n {
        let pivot = (col..n).find(|&row| !m[row][col].is_zero())?;

        if pivot != col {
            m.swap(pivot, col);
            sign_flip = !sign_flip;
        }

        det = (&det * &m[col][col]) % p;
        let pivot_inv = mod_inverse(&m[col][col], p)?;

        for row in (col + 1)..n {
            if m[row][col].is_zero() { continue; }
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

fn mod_inverse(a: &BigUint, p: &BigUint) -> Option<BigUint> {
    let a_int = BigInt::from(a.clone());
    let p_int = BigInt::from(p.clone());
    let gcd = a_int.extended_gcd(&p_int);
    if gcd.gcd != BigInt::one() { return None; }
    let inv = ((gcd.x % &p_int) + &p_int) % &p_int;
    Some(inv.to_biguint().expect("modular reduction should be non-negative"))
}
