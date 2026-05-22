//! Runtime configuration for the solver.
//!
//! Aggregates every knob that was previously read from a `PICUS_*`
//! environment variable or a `static AtomicU8`. The active config is
//! stored thread-local so concurrent solves on different threads can
//! pick distinct settings, and so callers (the `picus` facade, CLI,
//! library consumers, tests) can override individual fields without
//! mutating process-global state.
//!
//! Defaults come from [`RuntimeConfig::from_env`], which reads the
//! same `PICUS_*` variables the prior implementation honoured. Callers
//! that need different values pass a fresh [`RuntimeConfig`] through
//! [`set`] (one-shot) or [`ConfigGuard`] (RAII scope).
//!
//! Soundness invariant: every field is read by the production code via
//! [`with`] at the point of use, never cached into a long-lived value.
//! Tests that mutate the config restore the previous value with
//! `ConfigGuard` so they don't leak settings into sibling tests.

use std::cell::RefCell;

use crate::ideal::GbStrategy;

#[derive(Clone, Debug)]
pub struct RuntimeConfig {
    /// GB algorithm strategy.
    pub gb_strategy: GbStrategy,
    /// Use F4 matrix reduction for batched same-sugar S-pairs.
    pub use_f4: bool,
    /// DNF expansion cap (max disjunct count) before
    /// [`crate::boolean::solve_boolean_query_dnf`] returns `Unknown`.
    pub dnf_cap: u64,
    /// Pick DNF instead of CNF for the boolean layer.
    pub dnf_enabled: bool,
    /// CDCL(T) outer-iteration cap. Set `0` to force an immediate
    /// `Unknown` (used by tests); `u64::MAX` for effectively unbounded.
    pub cdclt_iter_cap: u64,
    /// Emit per-run GB statistics (basis size, S-pair counts, F4 batch
    /// distribution) to stderr.
    pub gb_stats_enabled: bool,
    /// Emit GB trace events for the in-flight basis to stderr.
    pub gb_trace_enabled: bool,
    /// Enable the phase profiler (`ScopedTimer`).
    pub profile_enabled: bool,
}

impl Default for RuntimeConfig {
    fn default() -> Self {
        Self {
            gb_strategy: GbStrategy::Direct,
            use_f4: false,
            dnf_cap: 100_000,
            dnf_enabled: false,
            cdclt_iter_cap: 1_000_000,
            gb_stats_enabled: false,
            gb_trace_enabled: false,
            profile_enabled: false,
        }
    }
}

impl RuntimeConfig {
    /// Read defaults from the `PICUS_*` environment variables. Used to
    /// seed the thread-local config the first time a thread asks for it.
    pub fn from_env() -> Self {
        let mut c = Self::default();
        if std::env::var_os("PICUS_USE_F4").is_some() {
            c.use_f4 = true;
        }
        if let Ok(v) = std::env::var("PICUS_BOOLEAN") {
            c.dnf_enabled = v == "dnf";
        }
        if let Ok(v) = std::env::var("PICUS_DNF_CAP") {
            if let Ok(n) = v.parse::<u64>() {
                c.dnf_cap = n;
            }
        }
        if let Ok(v) = std::env::var("PICUS_CDCLT_ITER_CAP") {
            if let Ok(n) = v.parse::<u64>() {
                c.cdclt_iter_cap = n;
            }
        }
        if std::env::var_os("PICUS_GB_STATS").is_some() {
            c.gb_stats_enabled = true;
        }
        if std::env::var_os("PICUS_GB_TRACE").is_some() {
            c.gb_trace_enabled = true;
        }
        if std::env::var_os("PICUS_PROFILE").is_some() {
            c.profile_enabled = true;
        }
        c
    }
}

thread_local! {
    static THREAD_CONFIG: RefCell<RuntimeConfig> = RefCell::new(RuntimeConfig::from_env());
}

/// Read a snapshot of the current thread's config.
pub fn with<R>(f: impl FnOnce(&RuntimeConfig) -> R) -> R {
    THREAD_CONFIG.with(|c| f(&c.borrow()))
}

/// Replace the thread's config. The previous value is discarded; prefer
/// [`ConfigGuard`] for scoped overrides.
pub fn set(new: RuntimeConfig) {
    THREAD_CONFIG.with(|c| *c.borrow_mut() = new);
}

/// RAII override: installs `new` for the lifetime of the guard, then
/// restores the previous config on drop. Tests use this to flip a
/// single knob without leaking the change to sibling tests.
pub struct ConfigGuard {
    prev: RuntimeConfig,
}

impl ConfigGuard {
    pub fn install(new: RuntimeConfig) -> Self {
        let prev = THREAD_CONFIG.with(|c| c.borrow().clone());
        set(new);
        Self { prev }
    }

    /// Replace just one field, keeping the rest of the current config.
    pub fn with_override(f: impl FnOnce(&mut RuntimeConfig)) -> Self {
        let prev = THREAD_CONFIG.with(|c| c.borrow().clone());
        let mut next = prev.clone();
        f(&mut next);
        set(next);
        Self { prev }
    }
}

impl Drop for ConfigGuard {
    fn drop(&mut self) {
        THREAD_CONFIG.with(|c| *c.borrow_mut() = self.prev.clone());
    }
}
