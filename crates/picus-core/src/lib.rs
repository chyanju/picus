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

/// Namespaced gb-stats instrumentation vocabulary: `metric::incr!`,
/// `metric::add!`, `metric::max!`, `metric::timer!`. Every profiling call site
/// goes through this `metric::` namespace (paired with the `#[metric]`
/// attribute), so `grep -E 'metric::|#\[metric\]'` finds exactly the profiling
/// and nothing in main logic. Backed by [`profile`] (`record_add` / `MetricTimer`
/// / `GbStatsLayer`).
pub mod metric {
    pub use crate::{
        __metric_add as add, __metric_bump as bump, __metric_def as def,
        __metric_flush as flush, __metric_incr as incr, __metric_max as max,
        __metric_timer as timer,
    };
}
