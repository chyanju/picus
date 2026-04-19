//! Solver backend trait and common types.

pub mod z3_nia;
pub mod cvc5_ff;
pub mod cvc5_nia;

use num_bigint::BigUint;
use std::collections::HashMap;
use thiserror::Error;

use crate::query::UniquenessQuery;

/// Result from a solver invocation.
#[derive(Debug, Clone)]
pub enum SolverResult {
    /// UNSAT — the signal is uniquely determined.
    Unsat,
    /// SAT — found two distinct witnesses. Model maps variable names to values.
    Sat(HashMap<String, BigUint>),
    /// Solver timed out or returned unknown.
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
    /// Solve a uniqueness query.
    fn solve(
        &mut self,
        query: &UniquenessQuery,
        timeout_ms: u64,
    ) -> Result<SolverResult, SolverError>;

    /// Dump the query as an SMT-LIB string for debugging.
    fn dump_smt(&self, query: &UniquenessQuery) -> String;
}
