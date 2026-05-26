//! Pure Rust finite field solver for zero-knowledge circuit verification.
//!
//! This crate implements a Groebner-basis-based satisfiability solver for
//! polynomial systems over prime finite fields GF(p), designed as a drop-in
//! replacement for cvc5's QF_FF theory solver within the Picus ecosystem.
//!
//! The algorithm follows [OKTB23] "Satisfiability Modulo Finite Fields" (CAV 2023).

// Public modules: used by external crates (picus-smt backends, picus-cli)
// and/or integration tests under `tests/` / `src/bin/`.
pub mod boolean;
pub mod cdclt;
pub mod core;
pub mod ff;
pub mod frontend;
pub mod gb;
pub mod incremental_context;
pub mod smt2;
pub mod split_gb;

pub(crate) mod sat;

// Shared substrate (runtime config, polynomial ring, profiler, cancellation)
// lives in picus-core; re-bound so in-crate code uses
// `crate::{config, poly, profile, timeout}`.
pub(crate) use picus_core::{config, poly, profile, timeout};

use thiserror::Error;

/// Internal error type for the Gröbner-basis engine: the `Err` arm of
/// `Result<_, EngineError>` throughout `ff::buchberger` and `gb::ideal`,
/// surfacing cooperative cancellation (`EngineError::Timeout`) and internal
/// failures. Distinct from the backend-facing `picus_smt::backends::SolverError`
/// returned to `SolverBackend::solve` callers (this one never crosses the
/// crate boundary).
#[derive(Debug, Error)]
pub enum EngineError {
    #[error("solver error: {0}")]
    Internal(String),
    #[error("encoding error: {0}")]
    Encoding(String),
    #[error("timeout")]
    Timeout,
}
