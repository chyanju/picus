//! R1CS binary constraints → AST conversion (solver-specific).
#![allow(clippy::type_complexity)]
//!
//! Two-phase pipeline:
//! 1. `parse_r1cs` — binary R1CS → standard form AST (`A * B = C`, optionally
//!    wrapped in `mod p`)
//! 2. `expand_r1cs` — expand `A * B` into a sum of cross-product terms
//!
//! Backend-specific behaviour (Z3 vs cvc5) is captured by a small
//! [`R1csBackend`] descriptor used by the shared `parse_r1cs_impl` and
//! `expand_cmd_impl` bodies.

use num_bigint::BigUint;
use num_traits::Zero;
use picus_r1cs::grammar::*;
use picus_r1cs::{bn128_prime, field_reduce};

use crate::SolverKind;

/// Result of parsing R1CS into AST.
pub struct ParsedR1cs {
    /// Variable name list (e.g., ["x0", "x1", ...] or mixed with "y" for alt).
    pub xlist: Vec<String>,
    /// Options commands (logic declaration).
    pub opts: RCmds,
    /// Declaration commands (variable defs + range constraints).
    pub decls: RCmds,
    /// Main constraint commands.
    pub cnsts: RCmds,
}

/// Solver-specific R1CS-encoding parameters. Bundled so the shared
/// `parse_r1cs_impl` / `expand_cmd_impl` bodies only have to dispatch
/// on these flags, not on a `SolverKind` enum.
struct R1csBackend {
    /// SMT logic name (e.g. `QF_NIA`, `QF_FF`).
    logic: &'static str,
    /// Variable sort name (e.g. `Int` for Z3, `F` for cvc5 finite field).
    var_type: &'static str,
    /// Extra option commands emitted after the `(set-logic …)` line.
    /// cvc5 needs `(define-sort F () (_ FiniteField p))`; Z3 needs nothing.
    extra_opts: Vec<RCmd>,
    /// Emit `(and (<= 0 x) (< x p))` range constraints for each variable.
    /// Z3/QF_NIA needs them; cvc5/QF_FF doesn't (the F sort is field-ranged).
    include_range_check: bool,
    /// Wrap `A * B = C` constraints with `(mod _ p)` on both sides.
    /// Z3/QF_NIA needs the wrapper; cvc5/QF_FF computes in the field.
    wrap_with_mod: bool,
}

impl R1csBackend {
    fn z3() -> Self {
        R1csBackend {
            logic: "QF_NIA",
            var_type: "Int",
            extra_opts: Vec::new(),
            include_range_check: true,
            wrap_with_mod: true,
        }
    }

    fn cvc5() -> Self {
        let p = bn128_prime();
        R1csBackend {
            logic: "QF_FF",
            var_type: "F",
            extra_opts: vec![RCmd::Raw(format!(
                "(define-sort F () (_ FiniteField {}))",
                p
            ))],
            include_range_check: false,
            wrap_with_mod: false,
        }
    }
}

fn backend_for(solver: SolverKind) -> R1csBackend {
    match solver {
        SolverKind::Z3 => R1csBackend::z3(),
        SolverKind::Cvc5 => R1csBackend::cvc5(),
        SolverKind::None => unreachable!("propagation-only mode does not use R1CS AST parser"),
        SolverKind::Native => unreachable!("native solver does not use R1CS AST parser"),
    }
}

/// Convert binary R1CS to standard-form AST.
///
/// `xlist_in`: if non-empty, reuse these variable names; otherwise
/// generate fresh `x0`, `x1`, ...
pub fn parse_r1cs(
    r1cs: &picus_r1cs::grammar::R1csFile,
    xlist_in: &[String],
    solver: SolverKind,
) -> ParsedR1cs {
    parse_r1cs_impl(r1cs, xlist_in, &backend_for(solver))
}

/// Expand standard-form constraints into sum-of-products form.
pub fn expand_r1cs(cnsts: &RCmds, solver: SolverKind) -> RCmds {
    let backend = backend_for(solver);
    let expanded: Vec<RCmd> = cnsts
        .commands
        .iter()
        .map(|cmd| expand_cmd_impl(cmd, &backend))
        .collect();
    RCmds::new(expanded)
}

// ─── Shared implementation ────────────────────────────────────────────────

fn parse_r1cs_impl(
    r1cs: &R1csFile,
    xlist_in: &[String],
    backend: &R1csBackend,
) -> ParsedR1cs {
    let p = bn128_prime();
    let nwires = r1cs.n_wires() as usize;

    let xlist: Vec<String> = if xlist_in.is_empty() {
        (0..nwires).map(|i| format!("x{}", i)).collect()
    } else {
        xlist_in.to_vec()
    };

    // Options: logic + any backend-specific declarations.
    let mut opts_cmds: Vec<RCmd> = vec![RCmd::Logic(backend.logic.to_string())];
    opts_cmds.extend(backend.extra_opts.iter().cloned());
    let opts = RCmds::new(opts_cmds);

    // Declarations.
    let mut decls = Vec::new();
    decls.push(RCmd::Comment("======== declaration constraints ========".into()));
    for x in &xlist {
        if !xlist_in.is_empty() && x.starts_with('x') {
            decls.push(RCmd::Comment(format!("{}: already defined", x)));
        } else {
            decls.push(RCmd::Def {
                var: x.clone(),
                typ: backend.var_type.to_string(),
            });
        }
    }

    // Range constraints (Z3/NIA only).
    if backend.include_range_check {
        decls.push(RCmd::Comment("======== range constraints ========".into()));
        for x in &xlist {
            if !xlist_in.is_empty() && x.starts_with('x') {
                decls.push(RCmd::Comment(format!("{}: already defined", x)));
            } else {
                decls.push(RCmd::Assert(RExpr::And(vec![
                    RExpr::Leq(
                        Box::new(RExpr::Int(BigUint::zero())),
                        Box::new(RExpr::Var(x.clone())),
                    ),
                    RExpr::Lt(
                        Box::new(RExpr::Var(x.clone())),
                        Box::new(RExpr::Int(p.clone())),
                    ),
                ])));
            }
        }
    }

    // Main constraints: A * B = C, optionally wrapped with (mod _ p).
    let mut cnsts = Vec::new();
    cnsts.push(RCmd::Comment("======== main constraints ========".into()));

    for constraint in &r1cs.constraints.constraints {
        let terms_a = block_to_terms(&constraint.a, &xlist);
        let terms_b = block_to_terms(&constraint.b, &xlist);
        let terms_c = block_to_terms(&constraint.c, &xlist);

        let sum_a = make_sum_with_zero(terms_a);
        let sum_b = make_sum_with_zero(terms_b);
        let sum_c = make_sum_with_zero(terms_c);

        let ab = RExpr::Mul(vec![sum_a, sum_b]);
        let (ab_side, c_side) = if backend.wrap_with_mod {
            (
                RExpr::Mod(Box::new(ab), Box::new(RExpr::Int(p.clone()))),
                RExpr::Mod(Box::new(sum_c), Box::new(RExpr::Int(p.clone()))),
            )
        } else {
            (ab, sum_c)
        };

        cnsts.push(RCmd::Assert(RExpr::Eq(Box::new(ab_side), Box::new(c_side))));
    }

    // x0 = 1
    cnsts.push(RCmd::Assert(RExpr::Eq(
        Box::new(RExpr::Int(BigUint::from(1u32))),
        Box::new(RExpr::Var(xlist[0].clone())),
    )));

    ParsedR1cs {
        xlist,
        opts,
        decls: RCmds::new(decls),
        cnsts: RCmds::new(cnsts),
    }
}

fn expand_cmd_impl(cmd: &RCmd, backend: &R1csBackend) -> RCmd {
    let p = bn128_prime();
    match cmd {
        RCmd::Assert(RExpr::Eq(lhs, rhs)) => {
            let parsed = if backend.wrap_with_mod {
                try_match_standard_form_with_mod(lhs, rhs)
            } else {
                try_match_standard_form_no_mod(lhs, rhs)
            };

            let (terms_a, terms_b, terms_c) = match parsed {
                Some(t) => t,
                None => return cmd.clone(),
            };

            let ab_expr = if terms_a.is_empty() || terms_b.is_empty() {
                RExpr::Int(BigUint::zero())
            } else {
                let cross_terms: Vec<RExpr> = terms_a
                    .iter()
                    .flat_map(|va| {
                        terms_b.iter().map(move |vb| {
                            let coeff = field_reduce(&(&va.0 * &vb.0));
                            RExpr::Mul(vec![
                                RExpr::Int(coeff),
                                RExpr::Var(va.1.clone()),
                                RExpr::Var(vb.1.clone()),
                            ])
                        })
                    })
                    .collect();
                let inner = RExpr::Add(cross_terms);
                if backend.wrap_with_mod {
                    RExpr::Mod(Box::new(inner), Box::new(RExpr::Int(p.clone())))
                } else {
                    inner
                }
            };

            let c_expr = if terms_c.is_empty() {
                RExpr::Int(BigUint::zero())
            } else {
                let c_terms: Vec<RExpr> = terms_c
                    .iter()
                    .map(|v| RExpr::Mul(vec![RExpr::Int(v.0.clone()), RExpr::Var(v.1.clone())]))
                    .collect();
                let inner = RExpr::Add(c_terms);
                if backend.wrap_with_mod {
                    RExpr::Mod(Box::new(inner), Box::new(RExpr::Int(p.clone())))
                } else {
                    inner
                }
            };

            RCmd::Assert(RExpr::Eq(Box::new(ab_expr), Box::new(c_expr)))
        }
        _ => cmd.clone(),
    }
}

// ─── Standard-form matchers ───────────────────────────────────────────────

type StandardForm = (
    Vec<(BigUint, String)>, // terms_a
    Vec<(BigUint, String)>, // terms_b
    Vec<(BigUint, String)>, // terms_c
);

/// Match `(mod (mul [sum_a, sum_b]) p) = (mod sum_c p)` (Z3 / QF_NIA shape).
fn try_match_standard_form_with_mod(lhs: &RExpr, rhs: &RExpr) -> Option<StandardForm> {
    if let (RExpr::Mod(lhs_inner, _), RExpr::Mod(rhs_inner, _)) = (lhs, rhs)
        && let RExpr::Mul(mul_args) = lhs_inner.as_ref()
        && mul_args.len() == 2
    {
        let terms_a = extract_sum_terms(&mul_args[0])?;
        let terms_b = extract_sum_terms(&mul_args[1])?;
        let terms_c = extract_sum_terms(rhs_inner)?;
        return Some((terms_a, terms_b, terms_c));
    }
    None
}

/// Match `(mul [sum_a, sum_b]) = sum_c` (cvc5 / QF_FF shape).
fn try_match_standard_form_no_mod(lhs: &RExpr, rhs: &RExpr) -> Option<StandardForm> {
    if let RExpr::Mul(mul_args) = lhs
        && mul_args.len() == 2
    {
        let terms_a = extract_sum_terms(&mul_args[0])?;
        let terms_b = extract_sum_terms(&mul_args[1])?;
        let terms_c = extract_sum_terms(rhs)?;
        return Some((terms_a, terms_b, terms_c));
    }
    None
}

/// Extract terms from `Add([Int(0), Mul([Int(f), Var(x)]), ...])`.
fn extract_sum_terms(expr: &RExpr) -> Option<Vec<(BigUint, String)>> {
    match expr {
        RExpr::Add(vs) => {
            let mut terms = Vec::new();
            for v in vs {
                match v {
                    RExpr::Int(n) if n.is_zero() => {} // skip the leading 0
                    RExpr::Mul(mul_args) if mul_args.len() == 2 => {
                        if let (RExpr::Int(f), RExpr::Var(x)) = (&mul_args[0], &mul_args[1]) {
                            terms.push((f.clone(), x.clone()));
                        } else {
                            return None;
                        }
                    }
                    _ => return None,
                }
            }
            Some(terms)
        }
        _ => None,
    }
}

// ─── Term-level helpers ───────────────────────────────────────────────────

/// Convert a constraint block into terms: `[(factor, var_name), ...]`.
fn block_to_terms(block: &ConstraintBlock, xlist: &[String]) -> Vec<RExpr> {
    block
        .wire_ids
        .iter()
        .zip(block.factors.iter())
        .filter_map(|(&wid, factor)| {
            let idx = wid as usize;
            if idx >= xlist.len() {
                log::warn!("wire ID {} out of bounds (n_wires={}), skipping", wid, xlist.len());
                return None;
            }
            let var_name = &xlist[idx];
            Some(RExpr::Mul(vec![
                RExpr::Int(factor.clone()),
                RExpr::Var(var_name.clone()),
            ]))
        })
        .collect()
}

/// Wrap term list as `Add([Int(0), term1, term2, ...])`, matching the
/// canonical shape produced by the Racket reference implementation.
fn make_sum_with_zero(terms: Vec<RExpr>) -> RExpr {
    let mut all = vec![RExpr::Int(BigUint::zero())];
    all.extend(terms);
    RExpr::Add(all)
}
