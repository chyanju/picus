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

use thiserror::Error;

/// Internal error type for the Groebner-basis engine. Used as the
/// `Err` arm of `Result<_, SolverError>` throughout `ff::buchberger`
/// and `ideal::*` to surface cooperative cancellation
/// (`SolverError::Timeout`) and internal failures. The backend-facing
/// error type — the one returned by [`crate::core::solve_encoded_with_cancel`]
/// callers and `picus_smt::backends::SolverBackend::solve` — is the
/// distinct [`picus_smt::backends::SolverError`].
#[derive(Debug, Error)]
pub enum SolverError {
    #[error("solver error: {0}")]
    Internal(String),
    #[error("encoding error: {0}")]
    Encoding(String),
    #[error("timeout")]
    Timeout,
}
