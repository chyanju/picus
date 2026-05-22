//! Pure Rust finite field solver for zero-knowledge circuit verification.
//!
//! This crate implements a Groebner-basis-based satisfiability solver for
//! polynomial systems over prime finite fields GF(p), designed as a drop-in
//! replacement for cvc5's QF_FF theory solver within the Picus ecosystem.
//!
//! The algorithm follows [OKTB23] "Satisfiability Modulo Finite Fields" (CAV 2023).

// Public modules: used by external crates (picus-smt backends, picus-cli)
// and/or integration tests under `tests/` / `src/bin/`.
pub mod bench_fixtures;
pub mod bitprop;
pub mod boolean;
pub mod cdclt;
pub mod config;
pub mod core;
pub mod encoder;
pub mod ff;
pub mod field;
pub mod gb;
pub mod ideal;
pub mod incremental;
pub mod incremental_context;
pub mod parse;
pub mod poly;
pub mod profile;
pub mod roots;
pub mod smt2;
pub mod split_gb;
pub mod timeout;

// Internal modules: only referenced from within the crate. Kept private to
// keep the surface area focused.
pub(crate) mod brancher;
pub(crate) mod gb_homog;
pub(crate) mod homog_ring;
pub(crate) mod model;
pub(crate) mod rewriter;
pub(crate) mod sat;
pub(crate) mod tracer;

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
