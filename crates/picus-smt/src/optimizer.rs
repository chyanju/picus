//! R1CS AST optimization passes (Z3 / QF_NIA shape).
//!
//! Three passes:
//! - Phase 0 (ab0): A*B=0 → A=0 ∨ B=0
//! - Normalize (simple): strip *1, +0, x0→1, etc.
//! - Phase 1 (subp): substitute p-related integer constants

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::bn128_prime;
use picus_r1cs::grammar::*;

/// AB0 rewrite: `(mul a b) = 0` → `a = 0 ∨ b = 0`.
pub fn optimize_p0(cnsts: &RCmds) -> RCmds {
    ab0_optimize(cnsts)
}

/// Simple normalization: fold int literals, strip identities, `x0 → 1`.
pub fn normalize(cnsts: &RCmds) -> RCmds {
    simple_optimize(cnsts)
}

/// `include_p_defs`: if true, prepend p-related constant definitions.
/// The original copy should use true; the alt copy should use false
/// to avoid duplicate declarations.
pub fn optimize_p1(cnsts: &RCmds, decls: &RCmds, include_p_defs: bool) -> (RCmds, RCmds) {
    subp_optimize(cnsts, decls, include_p_defs)
}

// ========================= Simple optimizer (normalize) =========================

fn simple_optimize(cmds: &RCmds) -> RCmds {
    RCmds::new(cmds.commands.iter().map(simple_opt_cmd).collect())
}

fn simple_opt_cmd(cmd: &RCmd) -> RCmd {
    match cmd {
        RCmd::Assert(e) => RCmd::Assert(simple_opt_expr(e)),
        _ => cmd.clone(),
    }
}

fn simple_opt_expr(expr: &RExpr) -> RExpr {
    match expr {
        // x0 → 1
        RExpr::Var(v) if v == "x0" => RExpr::Int(BigUint::one()),

        RExpr::Add(vs) => {
            // After per-child recursion, fold all `Int` literals into
            // a single constant addend (sum) and canonicalise position
            // (constant last).
            let optimized: Vec<RExpr> = vs
                .iter()
                .map(simple_opt_expr)
                .filter(|v| !is_zero_int(v))
                .collect();
            let mut int_sum: BigUint = BigUint::zero();
            let mut non_int: Vec<RExpr> = Vec::with_capacity(optimized.len());
            for e in optimized {
                match &e {
                    RExpr::Int(n) => int_sum += n,
                    _ => non_int.push(e),
                }
            }
            if !int_sum.is_zero() {
                non_int.push(RExpr::Int(int_sum));
            }
            match non_int.len() {
                0 => RExpr::Int(BigUint::zero()),
                1 => non_int.into_iter().next().unwrap(),
                _ => RExpr::Add(non_int),
            }
        }

        RExpr::Mul(vs) => {
            // Fold integer-literal factors into a single constant and
            // canonicalise position (constant first).
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr).collect();
            if optimized.iter().any(is_zero_int) {
                return RExpr::Int(BigUint::zero());
            }
            let filtered: Vec<RExpr> = optimized.into_iter().filter(|v| !is_one_int(v)).collect();
            let mut int_prod: BigUint = BigUint::one();
            let mut non_int: Vec<RExpr> = Vec::with_capacity(filtered.len());
            for e in filtered {
                match &e {
                    RExpr::Int(n) => int_prod *= n,
                    _ => non_int.push(e),
                }
            }
            if !int_prod.is_one() {
                non_int.insert(0, RExpr::Int(int_prod));
            }
            match non_int.len() {
                0 => RExpr::Int(BigUint::one()),
                1 => non_int.into_iter().next().unwrap(),
                _ => RExpr::Mul(non_int),
            }
        }

        RExpr::Sub(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr).collect();
            if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                RExpr::Sub(optimized)
            }
        }

        RExpr::And(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr).collect();
            if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                RExpr::And(optimized)
            }
        }

        RExpr::Or(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr).collect();
            if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                RExpr::Or(optimized)
            }
        }

        // Strip trivial mod on a bare variable or integer
        RExpr::Mod(v, _m) => {
            let inner = simple_opt_expr(v);
            match &inner {
                RExpr::Var(_) | RExpr::Int(_) => inner,
                _ => RExpr::Mod(Box::new(inner), Box::new(simple_opt_expr(_m))),
            }
        }

        RExpr::Eq(l, r) => RExpr::Eq(
            Box::new(simple_opt_expr(l)),
            Box::new(simple_opt_expr(r)),
        ),
        RExpr::Neq(l, r) => RExpr::Neq(
            Box::new(simple_opt_expr(l)),
            Box::new(simple_opt_expr(r)),
        ),
        RExpr::Leq(l, r) => RExpr::Leq(
            Box::new(simple_opt_expr(l)),
            Box::new(simple_opt_expr(r)),
        ),
        RExpr::Lt(l, r) => RExpr::Lt(
            Box::new(simple_opt_expr(l)),
            Box::new(simple_opt_expr(r)),
        ),
        RExpr::Geq(l, r) => RExpr::Geq(
            Box::new(simple_opt_expr(l)),
            Box::new(simple_opt_expr(r)),
        ),
        RExpr::Gt(l, r) => RExpr::Gt(
            Box::new(simple_opt_expr(l)),
            Box::new(simple_opt_expr(r)),
        ),
        RExpr::Imp(l, r) => RExpr::Imp(
            Box::new(simple_opt_expr(l)),
            Box::new(simple_opt_expr(r)),
        ),
        RExpr::Neg(v) => RExpr::Neg(Box::new(simple_opt_expr(v))),

        _ => expr.clone(),
    }
}

// ============================ AB0 optimiser ===============================

fn ab0_optimize(cmds: &RCmds) -> RCmds {
    let p = bn128_prime();
    RCmds::new(cmds.commands.iter().map(|c| ab0_opt_cmd(c, p)).collect())
}

fn ab0_opt_cmd(cmd: &RCmd, p: &BigUint) -> RCmd {
    match cmd {
        RCmd::Assert(RExpr::Eq(lhs, rhs)) => {
            if let Some(mul_args) = match_ab0(lhs, rhs) {
                let disjuncts: Vec<RExpr> = mul_args
                    .iter()
                    .map(|v| {
                        RExpr::Eq(
                            Box::new(RExpr::Int(BigUint::zero())),
                            Box::new(RExpr::Mod(
                                Box::new(v.clone()),
                                Box::new(RExpr::Int(p.clone())),
                            )),
                        )
                    })
                    .collect();
                RCmd::Assert(RExpr::Or(disjuncts))
            } else if let Some(mul_args) = match_ab0(rhs, lhs) {
                let disjuncts: Vec<RExpr> = mul_args
                    .iter()
                    .map(|v| {
                        RExpr::Eq(
                            Box::new(RExpr::Int(BigUint::zero())),
                            Box::new(RExpr::Mod(
                                Box::new(v.clone()),
                                Box::new(RExpr::Int(p.clone())),
                            )),
                        )
                    })
                    .collect();
                RCmd::Assert(RExpr::Or(disjuncts))
            } else {
                cmd.clone()
            }
        }
        _ => cmd.clone(),
    }
}

/// Match pattern: lhs = (mod (mul [vs]) p), rhs = (mod (add [0]) p)
fn match_ab0(lhs: &RExpr, rhs: &RExpr) -> Option<Vec<RExpr>> {
    if let RExpr::Mod(lhs_inner, _) = lhs
        && let RExpr::Mul(vs) = lhs_inner.as_ref()
    {
        if is_zero_rhs(rhs) {
            return Some(vs.clone());
        }
    }
    None
}

fn is_zero_rhs(expr: &RExpr) -> bool {
    if let RExpr::Mod(inner, _) = expr
        && let RExpr::Add(vs) = inner.as_ref()
    {
        return vs.len() == 1 && is_zero_int(&vs[0]);
    }
    false
}

// ============================ SubP optimiser ==============================

/// Names introduced into the constraint system by the SubP optimiser.
/// Downstream code (e.g. witness post-processing) uses this list to filter
/// these names out, since they are not circuit signals.
pub const SUBP_CONSTANT_NAMES: &[&str] =
    &["p", "ps1", "ps2", "ps3", "ps4", "ps5", "zero", "one"];

fn subp_optimize(cnsts: &RCmds, decls: &RCmds, include_p_defs: bool) -> (RCmds, RCmds) {
    let p = bn128_prime();
    // Z3 (QF_NIA) sees the field as integers, so `p` itself is a usable
    // named constant.
    let constants: Vec<(&str, BigUint)> = vec![
        ("p", p.clone()),
        ("ps1", p - BigUint::from(1u32)),
        ("ps2", p - BigUint::from(2u32)),
        ("ps3", p - BigUint::from(3u32)),
        ("ps4", p - BigUint::from(4u32)),
        ("ps5", p - BigUint::from(5u32)),
        ("zero", BigUint::zero()),
        ("one", BigUint::one()),
    ];

    let mut extra_decls = Vec::new();
    if include_p_defs {
        extra_decls.push(RCmd::Comment("======== p-related constants ========".into()));
        for (name, val) in &constants {
            extra_decls.push(RCmd::Def {
                var: (*name).to_string(),
                typ: "Int".to_string(),
            });
            extra_decls.push(RCmd::Assert(RExpr::Eq(
                Box::new(RExpr::Var((*name).to_string())),
                Box::new(RExpr::Int(val.clone())),
            )));
        }
    }

    let subst_map: Vec<(BigUint, &str)> =
        constants.iter().map(|(n, v)| (v.clone(), *n)).collect();

    let new_cnsts = RCmds::new(
        cnsts
            .commands
            .iter()
            .map(|c| subp_cmd(&subst_map, c))
            .collect(),
    );

    let mut all_decls = extra_decls;
    all_decls.extend(decls.commands.iter().cloned());
    (new_cnsts, RCmds::new(all_decls))
}

fn subp_cmd(subst: &[(BigUint, &str)], cmd: &RCmd) -> RCmd {
    match cmd {
        RCmd::Assert(e) => RCmd::Assert(subp_expr(subst, e)),
        _ => cmd.clone(),
    }
}

fn subp_expr(subst: &[(BigUint, &str)], expr: &RExpr) -> RExpr {
    match expr {
        RExpr::Int(v) => {
            for (val, name) in subst {
                if v == val {
                    return RExpr::Var(name.to_string());
                }
            }
            expr.clone()
        }
        RExpr::Eq(l, r) => RExpr::Eq(
            Box::new(subp_expr(subst, l)),
            Box::new(subp_expr(subst, r)),
        ),
        RExpr::Neq(l, r) => RExpr::Neq(
            Box::new(subp_expr(subst, l)),
            Box::new(subp_expr(subst, r)),
        ),
        RExpr::Leq(l, r) => RExpr::Leq(
            Box::new(subp_expr(subst, l)),
            Box::new(subp_expr(subst, r)),
        ),
        RExpr::Lt(l, r) => RExpr::Lt(
            Box::new(subp_expr(subst, l)),
            Box::new(subp_expr(subst, r)),
        ),
        RExpr::Geq(l, r) => RExpr::Geq(
            Box::new(subp_expr(subst, l)),
            Box::new(subp_expr(subst, r)),
        ),
        RExpr::Gt(l, r) => RExpr::Gt(
            Box::new(subp_expr(subst, l)),
            Box::new(subp_expr(subst, r)),
        ),
        RExpr::And(vs) => RExpr::And(vs.iter().map(|v| subp_expr(subst, v)).collect()),
        RExpr::Or(vs) => RExpr::Or(vs.iter().map(|v| subp_expr(subst, v)).collect()),
        RExpr::Imp(l, r) => RExpr::Imp(
            Box::new(subp_expr(subst, l)),
            Box::new(subp_expr(subst, r)),
        ),
        RExpr::Add(vs) => RExpr::Add(vs.iter().map(|v| subp_expr(subst, v)).collect()),
        RExpr::Sub(vs) => RExpr::Sub(vs.iter().map(|v| subp_expr(subst, v)).collect()),
        RExpr::Mul(vs) => RExpr::Mul(vs.iter().map(|v| subp_expr(subst, v)).collect()),
        RExpr::Neg(v) => RExpr::Neg(Box::new(subp_expr(subst, v))),
        RExpr::Mod(v, m) => RExpr::Mod(
            Box::new(subp_expr(subst, v)),
            Box::new(subp_expr(subst, m)),
        ),
        _ => expr.clone(),
    }
}

// ========================= Helpers =========================

fn is_zero_int(expr: &RExpr) -> bool {
    matches!(expr, RExpr::Int(v) if v.is_zero())
}

fn is_one_int(expr: &RExpr) -> bool {
    matches!(expr, RExpr::Int(v) if v == &BigUint::one())
}
