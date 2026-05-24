//! BIM (Big Integer Multiply) propagation lemma.
//!
//! Collects every linear, homogeneous, constant-free equality from the
//! IR. If the variables that appear in the collected equations form
//! a square invertible system over GF(p), every variable in it is
//! uniquely determined and can be marked known.
#![allow(clippy::needless_range_loop)]

use std::collections::{HashMap, HashSet};

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};
use picus_smt::poly_ir::PolyIR;

use super::lemma::{LemmaDescriptor, PropagationCtx, PropagationLemma};

#[derive(Default)]
pub struct BimLemma;

impl PropagationLemma for BimLemma {
    fn name(&self) -> &'static str {
        "bim"
    }

    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool {
        let p = ir.ring.field().prime();
        let equations = collect_linear_homogeneous(ir);
        if equations.is_empty() {
            return false;
        }

        let all_sigs: HashSet<usize> = equations
            .iter()
            .flat_map(|eq| eq.iter().map(|(s, _)| *s))
            .collect();

        // Only apply when the variable count matches the equation count
        // and all variables are currently unknown.
        if equations.len() != all_sigs.len()
            || !all_sigs.iter().all(|s| ctx.unknown.contains(s))
        {
            return false;
        }
        let sig_list: Vec<usize> = all_sigs.iter().copied().collect();
        let n = sig_list.len();
        let sig_idx: HashMap<usize, usize> = sig_list
            .iter()
            .enumerate()
            .map(|(i, &s)| (s, i))
            .collect();

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

        let det = match matrix_det_mod(&matrix, p) {
            Some(d) => d,
            None => return false,
        };
        if det.is_zero() {
            return false;
        }

        let mut progress = false;
        for &sig in &all_sigs {
            if ctx.unknown.remove(&sig) {
                ctx.known.insert(sig);
                progress = true;
            }
        }
        progress
    }
}

/// Pick out every polynomial whose only terms are linear monomials with
/// a non-zero coefficient. Returns `Vec<(wire, coeff)>` per equation.
/// Constant terms are tolerated if and only if they are exactly zero.
fn collect_linear_homogeneous(ir: &PolyIR) -> Vec<Vec<(usize, BigUint)>> {
    let ring = &ir.ring;
    let n_vars = ring.n_vars();
    let field = ir.ring.field();

    let mut out = Vec::new();
    'poly: for poly in &ir.equalities {
        let mut row: Vec<(usize, BigUint)> = Vec::new();
        for (c, m) in ring.terms(poly) {
            let mut single_var = None;
            let mut total = 0usize;
            for v in 0..n_vars {
                let e = ring.exponent_at(&m, v);
                total += e;
                if e > 0 {
                    if single_var.is_some() {
                        continue 'poly;
                    }
                    if e != 1 {
                        continue 'poly;
                    }
                    single_var = Some(v);
                }
            }
            if total == 0 {
                if !field.to_biguint(c).is_zero() {
                    continue 'poly;
                }
            } else {
                let v = single_var.unwrap();
                row.push((ir.var_to_wire(v), field.to_biguint(c)));
            }
        }
        if !row.is_empty() {
            out.push(row);
        }
    }
    out
}

fn matrix_det_mod(matrix: &[Vec<BigUint>], p: &BigUint) -> Option<BigUint> {
    let n = matrix.len();
    if n == 0 || matrix[0].len() != n {
        return None;
    }
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

fn mod_inverse(a: &BigUint, p: &BigUint) -> Option<BigUint> {
    let a_int = BigInt::from(a.clone());
    let p_int = BigInt::from(p.clone());
    let gcd = a_int.extended_gcd(&p_int);
    if gcd.gcd != BigInt::one() {
        return None;
    }
    let inv = ((gcd.x % &p_int) + &p_int) % &p_int;
    Some(inv.to_biguint().expect("inverse should be non-negative"))
}

inventory::submit! {
    LemmaDescriptor {
        name: "bim",
        factory: || Box::new(BimLemma::default()),
    }
}
