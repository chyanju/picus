//! R1CS binary constraints → AST conversion (Z3 / QF_NIA shape).
#![allow(clippy::type_complexity)]
//!
//! Two-phase pipeline:
//! 1. [`parse_r1cs`] — binary R1CS → standard form AST (`A * B = C`, wrapped
//!    in `(mod _ p)`)
//! 2. [`expand_r1cs`] — expand `A * B` into a sum of cross-product terms

use num_bigint::BigUint;
use num_traits::Zero;
use picus_r1cs::grammar::*;
use picus_r1cs::{bn128_prime, field_reduce};

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

/// Convert binary R1CS to standard-form AST.
///
/// `xlist_in`: if non-empty, reuse these variable names; otherwise
/// generate fresh `x0`, `x1`, ...
pub fn parse_r1cs(r1cs: &R1csFile, xlist_in: &[String]) -> ParsedR1cs {
    let p = bn128_prime();
    let nwires = r1cs.n_wires() as usize;

    let xlist: Vec<String> = if xlist_in.is_empty() {
        (0..nwires).map(|i| format!("x{}", i)).collect()
    } else {
        xlist_in.to_vec()
    };

    let opts = RCmds::new(vec![RCmd::Logic("QF_NIA".to_string())]);

    let mut decls = Vec::new();
    decls.push(RCmd::Comment("======== declaration constraints ========".into()));
    for x in &xlist {
        if !xlist_in.is_empty() && x.starts_with('x') {
            decls.push(RCmd::Comment(format!("{}: already defined", x)));
        } else {
            decls.push(RCmd::Def {
                var: x.clone(),
                typ: "Int".to_string(),
            });
        }
    }

    // Range constraints: 0 <= x < p
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

    // Main constraints: (mod (mul a b) p) = (mod c p)
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
        let ab_side = RExpr::Mod(Box::new(ab), Box::new(RExpr::Int(p.clone())));
        let c_side = RExpr::Mod(Box::new(sum_c), Box::new(RExpr::Int(p.clone())));

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

/// Expand standard-form constraints into sum-of-products form.
pub fn expand_r1cs(cnsts: &RCmds) -> RCmds {
    let expanded: Vec<RCmd> = cnsts.commands.iter().map(expand_cmd).collect();
    RCmds::new(expanded)
}

fn expand_cmd(cmd: &RCmd) -> RCmd {
    let p = bn128_prime();
    match cmd {
        RCmd::Assert(RExpr::Eq(lhs, rhs)) => {
            let (terms_a, terms_b, terms_c) = match try_match_standard_form(lhs, rhs) {
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
                RExpr::Mod(Box::new(inner), Box::new(RExpr::Int(p.clone())))
            };

            let c_expr = if terms_c.is_empty() {
                RExpr::Int(BigUint::zero())
            } else {
                let c_terms: Vec<RExpr> = terms_c
                    .iter()
                    .map(|v| RExpr::Mul(vec![RExpr::Int(v.0.clone()), RExpr::Var(v.1.clone())]))
                    .collect();
                let inner = RExpr::Add(c_terms);
                RExpr::Mod(Box::new(inner), Box::new(RExpr::Int(p.clone())))
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

/// Match `(mod (mul [sum_a, sum_b]) p) = (mod sum_c p)`.
fn try_match_standard_form(lhs: &RExpr, rhs: &RExpr) -> Option<StandardForm> {
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

/// Wrap term list as `Add([Int(0), term1, term2, ...])`. The leading
/// `Int(0)` is required by the canonical Picus AST shape.
fn make_sum_with_zero(terms: Vec<RExpr>) -> RExpr {
    let mut all = vec![RExpr::Int(BigUint::zero())];
    all.extend(terms);
    RExpr::Add(all)
}
