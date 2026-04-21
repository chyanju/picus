//! Solver backend trait and common types.

pub mod z3_nia;
pub mod cvc5_ff;
pub mod cvc5_nia;
pub mod native_ff;

use num_bigint::BigUint;
use std::collections::HashMap;
use thiserror::Error;

use crate::query::UniquenessQuery;

/// Result from a solver invocation.
#[derive(Debug, Clone)]
pub enum SolverResult {
    Unsat,
    Sat(HashMap<String, BigUint>),
    Unknown,
}

#[derive(Debug, Error)]
pub enum SolverError {
    #[error("solver error: {0}")]
    Internal(String),
    #[error("unsupported solver/theory combination: {0}")]
    Unsupported(String),
}

/// Trait for solver backends.
pub trait SolverBackend {
    fn solve(
        &mut self,
        query: &UniquenessQuery,
        timeout_ms: u64,
    ) -> Result<SolverResult, SolverError>;

    fn dump_smt(&self, query: &UniquenessQuery) -> String;
}

// ============================================================
// Shared SMT-LIB serialization for NIA backends (z3 + cvc5)
// ============================================================

use crate::query::IRConstraint;

/// Serialize an IR constraint to SMT-LIB NIA format.
/// `mod_op` is the modulus function name ("rem" for z3, "mod" for cvc5).
pub fn constraint_to_smtlib_nia(c: &IRConstraint, p: &BigUint, mod_op: &str) -> String {
    match c {
        IRConstraint::Linear(terms) => {
            let inner: Vec<String> = terms.iter().map(|t| format!("(* {} {})", t.coeff, t.var)).collect();
            let sum = if inner.len() == 1 { inner[0].clone() } else { format!("(+ {})", inner.join(" ")) };
            format!("(= ({} {} {}) 0)", mod_op, sum, p)
        }
        IRConstraint::NonLinear { lhs_terms, rhs_terms } => {
            let lhs: Vec<String> = lhs_terms.iter().map(|t| format!("(* {} {} {})", t.coeff, t.var_a, t.var_b)).collect();
            let rhs: Vec<String> = rhs_terms.iter().map(|t| format!("(* {} {})", t.coeff, t.var)).collect();
            let lhs_str = if lhs.len() == 1 { lhs[0].clone() } else { format!("(+ {})", lhs.join(" ")) };
            let rhs_str = if rhs.is_empty() { "0".into() } else if rhs.len() == 1 { rhs[0].clone() } else { format!("(+ {})", rhs.join(" ")) };
            format!("(= ({} {} {}) ({} {} {}))", mod_op, lhs_str, p, mod_op, rhs_str, p)
        }
        IRConstraint::Or(subs) => {
            let inner: Vec<String> = subs.iter().map(|s| constraint_to_smtlib_nia(s, p, mod_op)).collect();
            format!("(or {})", inner.join(" "))
        }
        IRConstraint::VarEq(var, val) => format!("(= {} {})", var, val),
        IRConstraint::VarNeq(a, b) => format!("(not (= {} {}))", a, b),
    }
}
