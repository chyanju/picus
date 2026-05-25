//! Shared algebra and runtime substrate for the Picus solver stack.
//!
//! - [`ff`]: finite-field arithmetic over GF(p), dense and sparse
//!   multivariate polynomials, divisibility masks, and geobucket reduction.
//! - [`poly`]: the polynomial ring facade ([`poly::FfPolyRing`], [`poly::IrPoly`]).
//! - [`config`]: thread-local runtime configuration ([`config::RuntimeConfig`],
//!   [`config::ReprKind`], [`config::GbStrategy`]).
//! - [`timeout`]: cooperative cancellation ([`timeout::CancelToken`]).
//! - [`profile`]: zero-dependency phase profiler.
//!
//! Consumed by `picus-solver` (GB / CDCL(T) engine), `picus-smt` (backend
//! adapters) and `picus-analysis` (propagation lemmas).

pub mod config;
pub mod ff;
pub mod poly;
pub mod profile;
pub mod timeout;
