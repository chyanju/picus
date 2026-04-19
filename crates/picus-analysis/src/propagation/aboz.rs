//! All-But-One-Zero (ABOZ) propagation lemma — sliding window 3-constraint match.

use picus_r1cs::grammar::*;
use picus_r1cs::parse_var_index;
use std::collections::HashSet;

use super::binary01::RangeValue;

/// Apply the ABOZ lemma. Mutates `ks` and `us` in place.
pub fn apply_lemma(
    ks: &mut HashSet<usize>,
    us: &mut HashSet<usize>,
    cnsts: &RCmds,
    _range_vec: &[RangeValue],
) {
    let asserts: Vec<&RExpr> = cnsts
        .commands
        .iter()
        .filter_map(|cmd| match cmd {
            RCmd::Assert(e) => Some(e),
            _ => None,
        })
        .collect();

    if asserts.len() < 3 {
        return;
    }

    for i in 0..asserts.len() - 2 {
        if let Some((x_sig, y0_sig, y1_sig, c_sig)) =
            match_aboz_triple(asserts[i], asserts[i + 1], asserts[i + 2])
            && ks.contains(&x_sig) && ks.contains(&c_sig) {
                if us.remove(&y0_sig) {
                    ks.insert(y0_sig);
                }
                if us.remove(&y1_sig) {
                    ks.insert(y1_sig);
                }
            }
    }
}

fn match_aboz_triple(c0: &RExpr, c1: &RExpr, c2: &RExpr) -> Option<(usize, usize, usize, usize)> {
    let (x0_candidates, y0_candidates) = match_or_zero_pair(c0)?;
    let (_x1_candidates, y1_candidates) = match_or_zero_pair(c1)?;
    let sum_sigs = match_linear_sum(c2)?;

    for &x in &x0_candidates {
        for &y0 in &y0_candidates {
            if y0 == x { continue; }
            for &y1 in &y1_candidates {
                if y1 == x || y1 == y0 { continue; }
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
        if lhs.is_zero() {
            return extract_any_signal(rhs);
        }
        if rhs.is_zero() {
            return extract_any_signal(lhs);
        }
    }
    None
}

fn extract_any_signal(expr: &RExpr) -> Option<usize> {
    match expr {
        RExpr::Var(name) => parse_var_index(name),
        RExpr::Mod(inner, _) => extract_any_signal(inner),
        _ => None,
    }
}

fn match_linear_sum(expr: &RExpr) -> Option<Vec<usize>> {
    let vars: HashSet<usize> = expr
        .get_variables(true)
        .into_iter()
        .filter_map(|v| match v {
            VarRef::Index(i) => Some(i),
            _ => None,
        })
        .collect();
    if vars.len() >= 2 {
        Some(vars.into_iter().collect())
    } else {
        None
    }
}
