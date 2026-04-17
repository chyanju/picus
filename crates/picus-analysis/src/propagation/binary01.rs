//! L1: Binary01 lemma — detects x*(x-1)=0 patterns to infer x ∈ {0,1}.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::bn128_prime;
use picus_r1cs::grammar::*;
use std::collections::HashSet;

/// Per-signal range: either unconstrained (Bottom) or a finite set of values.
#[derive(Debug, Clone)]
pub enum RangeValue {
    /// Unconstrained — full field.
    Bottom,
    /// Constrained to a finite set of values.
    Values(HashSet<BigUint>),
}

impl RangeValue {
    /// Intersect with a new set of values.
    pub fn intersect(&mut self, new_vals: HashSet<BigUint>) {
        match self {
            RangeValue::Bottom => *self = RangeValue::Values(new_vals),
            RangeValue::Values(existing) => {
                *existing = existing.intersection(&new_vals).cloned().collect();
            }
        }
    }

    /// Check if this range is a singleton.
    pub fn is_singleton(&self) -> bool {
        matches!(self, RangeValue::Values(v) if v.len() == 1)
    }

    /// Check if this range contains a value.
    pub fn contains(&self, val: &BigUint) -> bool {
        match self {
            RangeValue::Bottom => true,
            RangeValue::Values(v) => v.contains(val),
        }
    }

    /// Check if range is a subset of {0, 1}.
    pub fn is_binary(&self) -> bool {
        match self {
            RangeValue::Bottom => false,
            RangeValue::Values(v) => {
                v.iter()
                    .all(|x| x.is_zero() || x == &BigUint::one())
            }
        }
    }
}

/// Apply the binary01 lemma: detect x*(x-1)=0 patterns and update range_vec.
///
/// After detection, any signal with singleton range is moved to known set.
pub fn apply_lemma(
    mut ks: HashSet<usize>,
    mut us: HashSet<usize>,
    cnsts: &RCmds,
    range_vec: &mut [RangeValue],
) -> (HashSet<usize>, HashSet<usize>) {
    let p = bn128_prime();
    let p_minus_1 = &p - BigUint::one();
    let binary_set: HashSet<BigUint> = [BigUint::zero(), BigUint::one()].into_iter().collect();

    for cmd in &cnsts.vs {
        if let RCmd::Assert(expr) = cmd
            && let Some(signal_id) = match_binary01_pattern(expr, &p, &p_minus_1) {
                // Override range with {0, 1}
                if signal_id < range_vec.len() {
                    range_vec[signal_id].intersect(binary_set.clone());
                }
            }
    }

    // Check for singletons: signals whose range collapsed to one value
    for (sig, range) in range_vec.iter().enumerate() {
        if range.is_singleton() && us.contains(&sig) {
            ks.insert(sig);
            us.remove(&sig);
        }
    }

    (ks, us)
}

/// Try to match various forms of x*(x-1)=0 patterns.
/// Returns the signal index if matched.
fn match_binary01_pattern(expr: &RExpr, p: &BigUint, p_minus_1: &BigUint) -> Option<usize> {
    // Pattern 1 (after ab0): Or([Eq(0, x), Eq(0, x-1)]) → x ∈ {0, 1}
    // Pattern 2: Eq(Mod(Add(Mul(x, x), Mul(p-1, x)), p), Mod(Int(0), p))
    // Pattern 3: Eq(Add(Mul(x, x), Mul(p-1, x)), Int(0)) [cvc5]
    // And many commutative variants...

    match expr {
        // Or pattern (from ab0 optimization)
        RExpr::Or(vs) if vs.len() == 2 => {
            let sig0 = match_eq_zero_var(&vs[0]);
            let sig1 = match_eq_zero_var(&vs[1]);
            if let (Some(s0), Some(s1)) = (sig0, sig1)
                && s0 == s1 {
                    return Some(s0);
                }
            // Try matching eq(0, x-k) form for detecting binary constraint
            None
        }

        // x^2 + (p-1)*x = 0 in mod form (z3)
        RExpr::Eq(lhs, rhs) => {
            // Check both directions
            try_match_quadratic(lhs, rhs, p, p_minus_1)
                .or_else(|| try_match_quadratic(rhs, lhs, p, p_minus_1))
        }

        _ => None,
    }
}

/// Try matching x² + (p-1)*x = 0 (mod p) or in finite field.
fn try_match_quadratic(
    lhs: &RExpr,
    rhs: &RExpr,
    _p: &BigUint,
    p_minus_1: &BigUint,
) -> Option<usize> {
    // Match: Add([Mul([x, x]), Mul([p-1, x])]) = 0
    let inner_lhs = strip_mod(lhs);
    let inner_rhs = strip_mod(rhs);

    // rhs should be 0
    if !is_zero_expr(inner_rhs) {
        return None;
    }

    // lhs should be Add([Mul([x, x]), Mul([p-1, x])])
    if let RExpr::Add(terms) = inner_lhs
        && terms.len() == 2 {
            // Try both orderings
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
    // term_sq = Mul([Var(x), Var(x)]) or Mul([Int(1), Var(x), Var(x)])
    let sq_var = extract_squared_var(term_sq)?;
    // term_lin = Mul([Int(p-1), Var(x)]) or Mul([Var(ps1), Var(x)])
    let (coeff, lin_var) = extract_linear_term(term_lin)?;
    if sq_var == lin_var && (coeff == *p_minus_1 || coeff == BigUint::one()) {
        return Some(sq_var);
    }
    None
}

fn extract_squared_var(expr: &RExpr) -> Option<usize> {
    if let RExpr::Mul(vs) = expr {
        let vars: Vec<usize> = vs
            .iter()
            .filter_map(extract_signal_id)
            .collect();
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
                RExpr::Int(n) => coeff = n.clone(),
                RExpr::Var(name) => {
                    if let Some(id) = parse_var_index(name) {
                        var_id = Some(id);
                    } else {
                        // Named constant like "ps1" — treat as coefficient placeholder
                        // We'll handle this by returning the name-based match
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

fn match_eq_zero_var(expr: &RExpr) -> Option<usize> {
    if let RExpr::Eq(lhs, rhs) = expr {
        if is_zero_expr(lhs) {
            return extract_signal_id(rhs);
        }
        if is_zero_expr(rhs) {
            return extract_signal_id(lhs);
        }
    }
    None
}

fn strip_mod(expr: &RExpr) -> &RExpr {
    if let RExpr::Mod(inner, _) = expr {
        inner.as_ref()
    } else {
        expr
    }
}

fn is_zero_expr(expr: &RExpr) -> bool {
    match strip_mod(expr) {
        RExpr::Int(v) => v.is_zero(),
        RExpr::Add(vs) if vs.len() == 1 => is_zero_expr(&vs[0]),
        _ => false,
    }
}

pub fn extract_signal_id(expr: &RExpr) -> Option<usize> {
    if let RExpr::Var(name) = expr {
        parse_var_index(name)
    } else {
        None
    }
}

pub fn parse_var_index(name: &str) -> Option<usize> {
    if (name.starts_with('x') || name.starts_with('y')) && name.len() > 1 {
        name[1..].parse().ok()
    } else {
        None
    }
}
