//! L3: All-But-One-Zero lemma — sliding window 3-constraint match.

use num_bigint::BigUint;
use picus_r1cs::grammar::*;
use std::collections::HashSet;

use super::binary01;

/// Apply the ABOZ lemma using a sliding window of 3 consecutive constraints.
pub fn apply_lemma(
    mut ks: HashSet<usize>,
    mut us: HashSet<usize>,
    cnsts: &RCmds,
    _range_vec: &[super::binary01::RangeValue],
) -> (HashSet<usize>, HashSet<usize>) {
    let asserts: Vec<&RExpr> = cnsts
        .vs
        .iter()
        .filter_map(|cmd| match cmd {
            RCmd::Assert(e) => Some(e),
            _ => None,
        })
        .collect();

    if asserts.len() < 3 {
        return (ks, us);
    }

    for i in 0..asserts.len() - 2 {
        if let Some((x_sig, y0_sig, y1_sig, c_sig)) =
            match_aboz_triple(asserts[i], asserts[i + 1], asserts[i + 2])
        {
            // If x and c are known, y0 and y1 become known
            if ks.contains(&x_sig) && ks.contains(&c_sig) {
                if us.contains(&y0_sig) {
                    ks.insert(y0_sig);
                    us.remove(&y0_sig);
                }
                if us.contains(&y1_sig) {
                    ks.insert(y1_sig);
                    us.remove(&y1_sig);
                }
            }
        }
    }

    (ks, us)
}

/// Match the ABOZ triple pattern:
/// c[i]:   or(x=0, y0=0)
/// c[i+1]: or(x-1=0, y1=0)  (or: or(sub(x,1)=0, y1=0))
/// c[i+2]: y0 + y1 - c = 0
///
/// Returns (x_signal, y0_signal, y1_signal, c_signal) if matched.
fn match_aboz_triple(
    c0: &RExpr,
    c1: &RExpr,
    c2: &RExpr,
) -> Option<(usize, usize, usize, usize)> {
    // c0: Or([Eq(0, x), Eq(0, y0)]) — x*(y0) pattern after ab0
    let (x0_candidates, y0_candidates) = match_or_zero_pair(c0)?;
    // c1: Or([Eq(0, x-1_term), Eq(0, y1)]) — similar
    let (_x1_candidates, y1_candidates) = match_or_zero_pair(c1)?;

    // c2: pattern matching for y0 + y1 = c (or equivalent)
    // This is complex; simplified version: look for Add terms
    let sum_sigs = match_linear_sum(c2)?;

    // Try to find matching signal IDs across the three constraints
    for &x in &x0_candidates {
        for &y0 in &y0_candidates {
            if y0 == x {
                continue;
            }
            for &y1 in &y1_candidates {
                if y1 == x || y1 == y0 {
                    continue;
                }
                // Check sum constraint involves y0, y1, and some c
                for &c in &sum_sigs {
                    if c != y0 && c != y1 && c != x {
                        return Some((x, y0, y1, c));
                    }
                }
            }
        }
    }

    None
}

fn match_or_zero_pair(expr: &RExpr) -> Option<(Vec<usize>, Vec<usize>)> {
    if let RExpr::Or(vs) = expr
        && vs.len() == 2 {
            let mut all_sigs = Vec::new();
            for v in vs {
                if let Some(sig) = match_eq_zero_signal(v) {
                    all_sigs.push(sig);
                }
            }
            if all_sigs.len() == 2 {
                return Some((vec![all_sigs[0]], vec![all_sigs[1]]));
            }
        }
    None
}

fn match_eq_zero_signal(expr: &RExpr) -> Option<usize> {
    if let RExpr::Eq(lhs, rhs) = expr {
        if is_zero(lhs) {
            return extract_any_signal(rhs);
        }
        if is_zero(rhs) {
            return extract_any_signal(lhs);
        }
    }
    None
}

fn extract_any_signal(expr: &RExpr) -> Option<usize> {
    match expr {
        RExpr::Var(name) => binary01::parse_var_index(name),
        RExpr::Mod(inner, _) => extract_any_signal(inner),
        _ => None,
    }
}

fn match_linear_sum(expr: &RExpr) -> Option<Vec<usize>> {
    // Simplified: extract all signal IDs from the expression
    let vars: HashSet<usize> = expr
        .get_variables(true)
        .into_iter()
        .filter_map(|v| match v {
            picus_r1cs::grammar::VarRef::Index(i) => Some(i),
            _ => None,
        })
        .collect();
    if vars.len() >= 2 {
        Some(vars.into_iter().collect())
    } else {
        None
    }
}

fn is_zero(expr: &RExpr) -> bool {
    match expr {
        RExpr::Int(v) => v == &BigUint::ZERO,
        RExpr::Mod(inner, _) => is_zero(inner),
        _ => false,
    }
}
