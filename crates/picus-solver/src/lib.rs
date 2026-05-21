//! Pure Rust finite field solver for zero-knowledge circuit verification.
//!
//! This crate implements a Groebner-basis-based satisfiability solver for
//! polynomial systems over prime finite fields GF(p), designed as a drop-in
//! replacement for cvc5's QF_FF theory solver within the Picus ecosystem.
//!
//! The algorithm follows [OKTB23] "Satisfiability Modulo Finite Fields" (CAV 2023).

pub mod ff;
pub mod field;
pub mod poly;
pub mod ideal;
pub mod parse;
pub mod bitprop;
pub mod brancher;
pub mod split_gb;
pub mod encoder;
pub mod core;
pub mod incremental;
pub mod incremental_context;
pub mod gb;
pub mod roots;
pub mod model;
pub mod timeout;
pub mod stats;
pub mod tracer;
pub mod profile;
pub mod homog;
pub mod gb_homog;
pub mod smt2;
pub mod rewriter;
pub mod boolean;
pub mod sat;
pub mod cdclt;
pub mod bench_fixtures;

use num_bigint::BigUint;
use std::collections::HashMap;
use thiserror::Error;

/// Result of a satisfiability check.
#[derive(Debug, Clone)]
pub enum SolverResult {
    /// The system is unsatisfiable (the target signal is uniquely determined).
    Unsat,
    /// The system is satisfiable — two distinct valid witnesses found.
    Sat(HashMap<String, BigUint>),
    /// The solver could not determine satisfiability (timeout, etc.).
    Unknown,
}

/// Errors that can occur during solving.
#[derive(Debug, Error)]
pub enum SolverError {
    #[error("solver error: {0}")]
    Internal(String),
    #[error("encoding error: {0}")]
    Encoding(String),
    #[error("timeout")]
    Timeout,
}
