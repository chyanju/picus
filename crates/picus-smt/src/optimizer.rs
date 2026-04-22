//! R1CS AST optimization passes.
//!
//! Three passes per solver backend:
//! - Phase 0 (ab0): A*B=0 → A=0 ∨ B=0
//! - Normalize (simple): strip *1, +0, x0→1, etc.
//! - Phase 1 (subp): substitute p-related constants

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::bn128_prime;
use picus_r1cs::grammar::*;

use crate::SolverKind;

/// Run the full optimization pipeline: p0 → expand → normalize → p1.
/// Note: expand is done separately via r1cs_parser::expand_r1cs.
pub fn optimize_p0(cnsts: &RCmds, solver: SolverKind) -> RCmds {
    match solver {
        SolverKind::Z3 => ab0_optimize_z3(cnsts),
        // Skip AB0 for cvc5: cvc5 1.2.0–1.3.3 has a bug where `or` disjunctions in QF_FF
        // can produce spurious SAT results with inconsistent models.
        // The solver handles nonlinear A*B=0 constraints natively.
        SolverKind::None => unreachable!(),
        SolverKind::Native => unreachable!(),
        SolverKind::Cvc5 => cnsts.clone(),
    }
}

pub fn normalize(cnsts: &RCmds, solver: SolverKind) -> RCmds {
    match solver {
        SolverKind::Z3 => simple_optimize_z3(cnsts),
        SolverKind::None => unreachable!(),
        SolverKind::Native => unreachable!(),
        SolverKind::Cvc5 => simple_optimize_cvc5(cnsts),
    }
}

/// `include_p_defs`: if true, prepend p-related constant definitions.
/// The original copy should use true; the alt copy should use false
/// to avoid duplicate declarations.
pub fn optimize_p1(cnsts: &RCmds, decls: &RCmds, solver: SolverKind, include_p_defs: bool) -> (RCmds, RCmds) {
    match solver {
        SolverKind::Z3 => subp_optimize_z3(cnsts, decls, include_p_defs),
        SolverKind::None => unreachable!(),
        SolverKind::Native => unreachable!(),
        SolverKind::Cvc5 => subp_optimize_cvc5(cnsts, decls, include_p_defs),
    }
}

// ========================= Simple optimizer (normalize) =========================

fn simple_optimize_z3(cmds: &RCmds) -> RCmds {
    RCmds::new(cmds.commands.iter().map(simple_opt_cmd_z3).collect())
}

fn simple_opt_cmd_z3(cmd: &RCmd) -> RCmd {
    match cmd {
        RCmd::Assert(e) => RCmd::Assert(simple_opt_expr_z3(e)),
        _ => cmd.clone(),
    }
}

fn simple_opt_expr_z3(expr: &RExpr) -> RExpr {
    match expr {
        // x0 → 1
        RExpr::Var(v) if v == "x0" => RExpr::Int(BigUint::one()),

        RExpr::Add(vs) => {
            let optimized: Vec<RExpr> = vs
                .iter()
                .map(simple_opt_expr_z3)
                .filter(|v| !is_zero_int(v))
                .collect();
            match optimized.len() {
                0 => RExpr::Int(BigUint::zero()),
                1 => optimized.into_iter().next().unwrap(),
                _ => RExpr::Add(optimized),
            }
        }

        RExpr::Mul(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr_z3).collect();
            // If any is zero, whole product is zero
            if optimized.iter().any(is_zero_int) {
                return RExpr::Int(BigUint::zero());
            }
            let filtered: Vec<RExpr> = optimized
                .into_iter()
                .filter(|v| !is_one_int(v))
                .collect();
            match filtered.len() {
                0 => RExpr::Int(BigUint::one()),
                1 => filtered.into_iter().next().unwrap(),
                _ => RExpr::Mul(filtered),
            }
        }

        RExpr::Sub(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr_z3).collect();
            if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                RExpr::Sub(optimized)
            }
        }

        RExpr::And(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr_z3).collect();
            if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                RExpr::And(optimized)
            }
        }

        RExpr::Or(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr_z3).collect();
            if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                RExpr::Or(optimized)
            }
        }

        // Strip trivial mod on a bare variable or integer
        RExpr::Mod(v, _m) => {
            let inner = simple_opt_expr_z3(v);
            match &inner {
                RExpr::Var(_) | RExpr::Int(_) => inner,
                _ => RExpr::Mod(Box::new(inner), Box::new(simple_opt_expr_z3(_m))),
            }
        }

        RExpr::Eq(l, r) => RExpr::Eq(
            Box::new(simple_opt_expr_z3(l)),
            Box::new(simple_opt_expr_z3(r)),
        ),
        RExpr::Neq(l, r) => RExpr::Neq(
            Box::new(simple_opt_expr_z3(l)),
            Box::new(simple_opt_expr_z3(r)),
        ),
        RExpr::Leq(l, r) => RExpr::Leq(
            Box::new(simple_opt_expr_z3(l)),
            Box::new(simple_opt_expr_z3(r)),
        ),
        RExpr::Lt(l, r) => RExpr::Lt(
            Box::new(simple_opt_expr_z3(l)),
            Box::new(simple_opt_expr_z3(r)),
        ),
        RExpr::Geq(l, r) => RExpr::Geq(
            Box::new(simple_opt_expr_z3(l)),
            Box::new(simple_opt_expr_z3(r)),
        ),
        RExpr::Gt(l, r) => RExpr::Gt(
            Box::new(simple_opt_expr_z3(l)),
            Box::new(simple_opt_expr_z3(r)),
        ),
        RExpr::Imp(l, r) => RExpr::Imp(
            Box::new(simple_opt_expr_z3(l)),
            Box::new(simple_opt_expr_z3(r)),
        ),
        RExpr::Neg(v) => RExpr::Neg(Box::new(simple_opt_expr_z3(v))),

        _ => expr.clone(),
    }
}

fn simple_optimize_cvc5(cmds: &RCmds) -> RCmds {
    RCmds::new(cmds.commands.iter().map(simple_opt_cmd_cvc5).collect())
}

fn simple_opt_cmd_cvc5(cmd: &RCmd) -> RCmd {
    match cmd {
        RCmd::Assert(e) => RCmd::Assert(simple_opt_expr_cvc5(e)),
        _ => cmd.clone(),
    }
}

fn simple_opt_expr_cvc5(expr: &RExpr) -> RExpr {
    match expr {
        RExpr::Var(v) if v == "x0" => RExpr::Int(BigUint::one()),

        RExpr::Add(vs) => {
            let optimized: Vec<RExpr> = vs
                .iter()
                .map(simple_opt_expr_cvc5)
                .filter(|v| !is_zero_int(v))
                .collect();
            match optimized.len() {
                0 => RExpr::Int(BigUint::zero()),
                1 => optimized.into_iter().next().unwrap(),
                _ => RExpr::Add(optimized),
            }
        }

        RExpr::Mul(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr_cvc5).collect();
            if optimized.iter().any(is_zero_int) {
                return RExpr::Int(BigUint::zero());
            }
            let filtered: Vec<RExpr> = optimized
                .into_iter()
                .filter(|v| !is_one_int(v))
                .collect();
            match filtered.len() {
                0 => RExpr::Int(BigUint::one()),
                1 => filtered.into_iter().next().unwrap(),
                _ => RExpr::Mul(filtered),
            }
        }

        RExpr::And(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr_cvc5).collect();
            if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                RExpr::And(optimized)
            }
        }

        RExpr::Or(vs) => {
            let optimized: Vec<RExpr> = vs.iter().map(simple_opt_expr_cvc5).collect();
            if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                RExpr::Or(optimized)
            }
        }

        RExpr::Eq(l, r) => RExpr::Eq(
            Box::new(simple_opt_expr_cvc5(l)),
            Box::new(simple_opt_expr_cvc5(r)),
        ),
        RExpr::Neq(l, r) => RExpr::Neq(
            Box::new(simple_opt_expr_cvc5(l)),
            Box::new(simple_opt_expr_cvc5(r)),
        ),
        RExpr::Imp(l, r) => RExpr::Imp(
            Box::new(simple_opt_expr_cvc5(l)),
            Box::new(simple_opt_expr_cvc5(r)),
        ),

        _ => expr.clone(),
    }
}

// ========================= AB0 optimizer (phase 0) =========================

fn ab0_optimize_z3(cmds: &RCmds) -> RCmds {
    let p = bn128_prime();
    RCmds::new(cmds.commands.iter().map(|c| ab0_opt_cmd_z3(c, p)).collect())
}

fn ab0_opt_cmd_z3(cmd: &RCmd, p: &BigUint) -> RCmd {
    match cmd {
        RCmd::Assert(RExpr::Eq(lhs, rhs)) => {
            // Check: (mod (mul [vs]) p) = (mod (add [0]) p) or vice versa
            if let Some(mul_args) = match_ab0_z3(lhs, rhs) {
                // Rewrite: or(v1=0, v2=0, ...)
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
            } else if let Some(mul_args) = match_ab0_z3(rhs, lhs) {
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
fn match_ab0_z3(lhs: &RExpr, rhs: &RExpr) -> Option<Vec<RExpr>> {
    if let RExpr::Mod(lhs_inner, _) = lhs
        && let RExpr::Mul(vs) = lhs_inner.as_ref() {
            // Check rhs is zero: (mod (add [0]) p)
            if is_zero_rhs_z3(rhs) {
                return Some(vs.clone());
            }
        }
    None
}

fn is_zero_rhs_z3(expr: &RExpr) -> bool {
    if let RExpr::Mod(inner, _) = expr
        && let RExpr::Add(vs) = inner.as_ref() {
            return vs.len() == 1 && is_zero_int(&vs[0]);
        }
    false
}

// NOTE: cvc5 AB0 disabled due to cvc5 1.2.0–1.3.3 bug with `or` in QF_FF.
// These functions are retained for when the bug is fixed in future cvc5 versions.
#[allow(dead_code)]
fn ab0_optimize_cvc5(cmds: &RCmds) -> RCmds {
    RCmds::new(cmds.commands.iter().map(ab0_opt_cmd_cvc5).collect())
}

#[allow(dead_code)]
fn ab0_opt_cmd_cvc5(cmd: &RCmd) -> RCmd {
    match cmd {
        RCmd::Assert(RExpr::Eq(lhs, rhs)) => {
            // Check: (mul [vs]) = (add [0]) or vice versa
            if let Some(mul_args) = match_ab0_cvc5(lhs, rhs) {
                let disjuncts: Vec<RExpr> = mul_args
                    .iter()
                    .map(|v| {
                        RExpr::Eq(
                            Box::new(RExpr::Int(BigUint::zero())),
                            Box::new(v.clone()),
                        )
                    })
                    .collect();
                RCmd::Assert(RExpr::Or(disjuncts))
            } else if let Some(mul_args) = match_ab0_cvc5(rhs, lhs) {
                let disjuncts: Vec<RExpr> = mul_args
                    .iter()
                    .map(|v| {
                        RExpr::Eq(
                            Box::new(RExpr::Int(BigUint::zero())),
                            Box::new(v.clone()),
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

#[allow(dead_code)]
fn match_ab0_cvc5(lhs: &RExpr, rhs: &RExpr) -> Option<Vec<RExpr>> {
    if let RExpr::Mul(vs) = lhs
        && is_zero_rhs_cvc5(rhs) {
            return Some(vs.clone());
        }
    None
}

#[allow(dead_code)]
fn is_zero_rhs_cvc5(expr: &RExpr) -> bool {
    match expr {
        RExpr::Add(vs) if vs.len() == 1 => is_zero_int(&vs[0]),
        RExpr::Int(v) => v.is_zero(),
        _ => false,
    }
}

// ========================= SubP optimizer (phase 1) =========================

fn subp_optimize_z3(cnsts: &RCmds, decls: &RCmds, include_p_defs: bool) -> (RCmds, RCmds) {
    let p = bn128_prime();

    let constants = [
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
                var: name.to_string(),
                typ: "Int".to_string(),
            });
            extra_decls.push(RCmd::Assert(RExpr::Eq(
                Box::new(RExpr::Var(name.to_string())),
                Box::new(RExpr::Int(val.clone())),
            )));
        }
    }

    // Substitute constants in constraints
    let subst_map: Vec<(BigUint, &str)> = constants.iter().map(|(n, v)| (v.clone(), *n)).collect();
    let new_cnsts = RCmds::new(
        cnsts
            .commands
            .iter()
            .map(|c| subp_cmd(&subst_map, c))
            .collect(),
    );

    // Merge extra decls with existing decls
    let mut all_decls = extra_decls;
    all_decls.extend(decls.commands.iter().cloned());
    (new_cnsts, RCmds::new(all_decls))
}

fn subp_optimize_cvc5(cnsts: &RCmds, decls: &RCmds, include_p_defs: bool) -> (RCmds, RCmds) {
    let p = bn128_prime();

    let constants: Vec<(&str, BigUint)> = vec![
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
                var: name.to_string(),
                typ: "F".to_string(),
            });
            extra_decls.push(RCmd::Assert(RExpr::Eq(
                Box::new(RExpr::Var(name.to_string())),
                Box::new(RExpr::Int(val.clone())),
            )));
        }
    }

    // For cvc5, p itself maps to 0
    let mut subst_map: Vec<(BigUint, &str)> =
        constants.iter().map(|(n, v)| (v.clone(), *n)).collect();
    subst_map.push((p.clone(), "zero")); // p → zero in finite field

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
