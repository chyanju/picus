//! BIM (Big Integer Multiply) propagation lemma.
//!
//! Collects every linear, homogeneous, constant-free equality from the
//! IR. If the variables that appear in the collected equations form
//! a square invertible system over GF(p), every variable in it is
//! uniquely determined and can be marked known.
//!
//! Wire-keyed: marking a wire known relies on the collected equations
//! being mirrored in both copies (the copy-symmetry invariant documented
//! in `picus_smt::poly_ir::r1cs_to_poly_ir`).
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
                    // Accumulate (mod p): a wire appearing more than once in
                    // one equation must sum its coefficients, not keep only
                    // the last (an overwrite would mis-build the matrix).
                    let acc = (&matrix[row][col] + coeff) % p;
                    matrix[row][col] = acc;
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
    let mut out = Vec::new();
    // Sparse-native: a term is admissible iff it is the zero constant, or a
    // single linear variable (one nonzero entry with exponent 1).
    'poly: for poly in &ir.equalities {
        let mut row: Vec<(usize, BigUint)> = Vec::new();
        for (coeff, vars) in ir.poly_terms_idx(poly) {
            if vars.is_empty() {
                // constant term: tolerated only if exactly zero
                if !coeff.is_zero() {
                    continue 'poly;
                }
            } else if vars.len() == 1 && vars[0].1 == 1 {
                row.push((ir.var_to_wire(vars[0].0), coeff));
            } else {
                // nonlinear (deg ≥ 2, or a product of variables)
                continue 'poly;
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
