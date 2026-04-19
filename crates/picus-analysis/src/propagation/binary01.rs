//! Binary01 propagation lemma — detects x*(x-1)=0 patterns.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::grammar::*;
use picus_r1cs::{bn128_prime, parse_var_index};
use std::collections::HashSet;

/// Per-signal range: unconstrained (Bottom) or a finite set of values.
#[derive(Debug, Clone)]
pub enum RangeValue {
    Bottom,
    Values(HashSet<BigUint>),
}

impl RangeValue {
    pub fn intersect(&mut self, new_vals: HashSet<BigUint>) {
        match self {
            RangeValue::Bottom => *self = RangeValue::Values(new_vals),
            RangeValue::Values(existing) => {
                *existing = existing.intersection(&new_vals).cloned().collect();
            }
        }
    }

    #[must_use]
    pub fn is_singleton(&self) -> bool {
        matches!(self, RangeValue::Values(v) if v.len() == 1)
    }

    #[must_use]
    pub fn is_binary(&self) -> bool {
        match self {
            RangeValue::Bottom => false,
            RangeValue::Values(v) => v.iter().all(|x| x.is_zero() || x == &BigUint::one()),
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        matches!(self, RangeValue::Values(v) if v.is_empty())
    }
}

/// Apply the binary01 lemma. Mutates `ks`, `us`, and `range_vec` in place.
pub fn apply_lemma(
    ks: &mut HashSet<usize>,
    us: &mut HashSet<usize>,
    cnsts: &RCmds,
    range_vec: &mut [RangeValue],
) {
    let p = bn128_prime();
    let p_minus_1 = p - BigUint::one();
    let binary_set: HashSet<BigUint> = [BigUint::zero(), BigUint::one()].into_iter().collect();

    for cmd in &cnsts.commands {
        if let RCmd::Assert(expr) = cmd
            && let Some(signal_id) = match_binary01_pattern(expr, &p_minus_1)
                && signal_id < range_vec.len() {
                    range_vec[signal_id].intersect(binary_set.clone());
                }
    }

    for (sig, range) in range_vec.iter().enumerate() {
        if range.is_singleton() && us.remove(&sig) {
            ks.insert(sig);
        }
    }
}

fn match_binary01_pattern(expr: &RExpr, p_minus_1: &BigUint) -> Option<usize> {
    match expr {
        // Pattern A: Or([eq_zero_expr, eq_zero_expr]) — from AB0 optimization
        // After AB0, x*(x-1)=0 becomes or(A=0, B=0) where:
        //   - One branch contains just `x` (i.e., Eq(0, x))
        //   - The other branch contains a linear expression with `x`
        //     (e.g., Eq(0, ps1 + x) which means x = -(p-1) = 1)
        // Both branches have the same signal, proving x ∈ {0, 1}.
        RExpr::Or(vs) if vs.len() == 2 => {
            let sigs0 = extract_signals_from_eq_zero(&vs[0]);
            let sigs1 = extract_signals_from_eq_zero(&vs[1]);

            for &s0 in &sigs0 {
                for &s1 in &sigs1 {
                    if s0 == s1 {
                        return Some(s0);
                    }
                }
            }
            None
        }

        // Pattern B: Eq(quadratic_in_x, 0) — direct x^2 + (p-1)*x = 0
        RExpr::Eq(lhs, rhs) => try_match_quadratic(lhs, rhs, p_minus_1)
            .or_else(|| try_match_quadratic(rhs, lhs, p_minus_1)),

        _ => None,
    }
}

/// Extract all signal indices from an `Eq(0, expr)` or `Eq(expr, 0)` expression.
fn extract_signals_from_eq_zero(expr: &RExpr) -> Vec<usize> {
    if let RExpr::Eq(lhs, rhs) = expr {
        let inner = if lhs.is_zero() {
            rhs.as_ref()
        } else if rhs.is_zero() {
            lhs.as_ref()
        } else {
            return vec![];
        };
        // Collect all signal indices from the non-zero side
        return collect_signal_indices(inner);
    }
    vec![]
}

/// Recursively collect all signal indices from an expression.
fn collect_signal_indices(expr: &RExpr) -> Vec<usize> {
    match expr {
        RExpr::Var(name) => parse_var_index(name).into_iter().collect(),
        RExpr::Add(vs) | RExpr::Mul(vs) | RExpr::Sub(vs) => {
            vs.iter().flat_map(collect_signal_indices).collect()
        }
        RExpr::Mod(inner, _) | RExpr::Neg(inner) => collect_signal_indices(inner),
        _ => vec![],
    }
}

fn try_match_quadratic(lhs: &RExpr, rhs: &RExpr, p_minus_1: &BigUint) -> Option<usize> {
    let inner_lhs = lhs.strip_mod();
    let inner_rhs = rhs.strip_mod();

    if !inner_rhs.is_zero() {
        return None;
    }

    if let RExpr::Add(terms) = inner_lhs
        && terms.len() == 2 {
            return try_extract_binary_signal(&terms[0], &terms[1], p_minus_1)
                .or_else(|| try_extract_binary_signal(&terms[1], &terms[0], p_minus_1));
        }
    None
}

fn try_extract_binary_signal(
    term_sq: &RExpr,
    term_lin: &RExpr,
    p_minus_1: &BigUint,
) -> Option<usize> {
    let sq_var = extract_squared_var(term_sq)?;
    let (coeff, lin_var) = extract_linear_term(term_lin)?;
    if sq_var == lin_var && (coeff == *p_minus_1 || coeff == BigUint::one()) {
        return Some(sq_var);
    }
    None
}

fn extract_squared_var(expr: &RExpr) -> Option<usize> {
    if let RExpr::Mul(vs) = expr {
        let vars: Vec<usize> = vs.iter().filter_map(extract_signal_id).collect();
        if vars.len() == 2 && vars[0] == vars[1] {
            return Some(vars[0]);
        }
    }
    None
}

fn extract_linear_term(expr: &RExpr) -> Option<(BigUint, usize)> {
    if let RExpr::Mul(vs) = expr {
        let mut coeff = BigUint::one();
        let mut var_id = None;
        for v in vs {
            match v {
                RExpr::Int(n) => {
                    coeff = n.clone();
                }
                RExpr::Var(name) => {
                    if let Some(id) = parse_var_index(name) {
                        var_id = Some(id);
                    } else if let Some(c) = super::resolve_named_constant(name) {
                        // Named constant like "ps1" = p-1
                        coeff = c;
                    }
                }
                _ => {}
            }
        }
        if let Some(vid) = var_id {
            return Some((coeff, vid));
        }
    }
    None
}

/// Resolve named constants introduced by the subp optimizer.

pub fn extract_signal_id(expr: &RExpr) -> Option<usize> {
    if let RExpr::Var(name) = expr {
        parse_var_index(name)
    } else {
        None
    }
}
