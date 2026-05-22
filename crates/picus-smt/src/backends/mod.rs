//! Solver backend trait and common types.

pub mod cvc5_ff;
pub mod cvc5_nia;
pub mod native_ff;
pub mod z3_nia;

use num_bigint::BigUint;
use std::collections::HashMap;
use thiserror::Error;

use crate::poly_ir::PolyIR;

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
///
/// Backends consume a [`PolyIR`] snapshot whose `target_signal` and
/// `known_signals` reflect the current DPVL state. The PolyIR's
/// `equalities` already encode `x_0 = 1`, the input wires' `x_i = y_i`
/// equalities, and every learned equality from previous solves; the
/// backend additionally asserts `x_target ≠ y_target` and runs SMT
/// `(check-sat)`. SAT models are returned as
/// `HashMap<String, BigUint>` keyed by the ring's canonical variable
/// names (`x0`, `y3`, ...).
pub trait SolverBackend {
    fn solve(
        &mut self,
        ir: &PolyIR,
        timeout_ms: u64,
    ) -> Result<SolverResult, SolverError>;

    fn dump_smt(&self, ir: &PolyIR) -> String;
}

// ─── Shared SMT-LIB-text helpers (NIA backends) ────────────────────

/// Emit a single `Poly` as an SMT-LIB nonlinear-integer-arithmetic
/// expression. Each `(coeff, monomial_vars)` term becomes
/// `(* coeff v1 v2 ...)`; the sum is wrapped in `(+ ...)` when it has
/// more than one term, and an empty polynomial reduces to literal `0`.
pub fn poly_to_smtlib_nia(ir: &PolyIR, poly: &picus_solver::poly::Poly) -> String {
    let parts: Vec<String> = ir
        .poly_terms(poly)
        .map(|(coeff, vars)| {
            let mut atoms = vec![coeff.to_string()];
            atoms.extend(vars);
            if atoms.len() == 1 {
                atoms.pop().unwrap()
            } else {
                format!("(* {})", atoms.join(" "))
            }
        })
        .collect();
    match parts.len() {
        0 => "0".to_string(),
        1 => parts.into_iter().next().unwrap(),
        _ => format!("(+ {})", parts.join(" ")),
    }
}

/// Emit a single `Poly` as an SMT-LIB QF_FF expression, using
/// `ff.add` / `ff.mul` and `#fNmP` literals over the field defined
/// by the ring's prime.
pub fn poly_to_smtlib_ff(ir: &PolyIR, poly: &picus_solver::poly::Poly) -> String {
    let p = ir.ring.field.prime();
    let parts: Vec<String> = ir
        .poly_terms(poly)
        .map(|(coeff, vars)| {
            let mut atoms = vec![format!("#f{}m{}", coeff, p)];
            atoms.extend(vars);
            if atoms.len() == 1 {
                atoms.pop().unwrap()
            } else {
                format!("(ff.mul {})", atoms.join(" "))
            }
        })
        .collect();
    match parts.len() {
        0 => format!("#f0m{}", p),
        1 => parts.into_iter().next().unwrap(),
        _ => format!("(ff.add {})", parts.join(" ")),
    }
}
