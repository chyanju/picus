//! Runtime configuration for the solver.
//!
//! Single thread-local [`RuntimeConfig`] aggregates every runtime
//! knob: GB strategy, F4 toggle, DNF cap, CDCL(T) iteration cap,
//! GB-stats / GB-trace / phase-profile flags. Production code reads
//! values via [`with`] at the point of use so no cached snapshot can
//! drift from the active config. Callers override fields via
//! [`set`] (one-shot) or [`ConfigGuard`] (RAII scope); per-thread
//! storage keeps concurrent solves on different threads independent.
//!
//! [`RuntimeConfig::from_env`] seeds the defaults from the
//! `PICUS_*` environment variables so existing benchmark scripts
//! and CLI invocations keep their behaviour without code changes.

use std::cell::RefCell;

use crate::ideal::GbStrategy;

/// Polynomial representation for the solver-agnostic IR layer
/// (`PolyIR` equalities/disjunctions and the lemma `learned` buffers).
///
/// `Dense` stores each monomial as a full-length exponent vector
/// (O(n_vars) per term); `Sparse` stores only the nonzero `(var, exp)`
/// pairs (O(nnz) per term). On wide rings (e.g. a circuit with tens of
/// thousands of wires → tens of thousands of ring variables) the dense
/// form makes the IR's *resident* memory blow up, so `Sparse` is the
/// representation that scales the lowering + cvc5 path. The choice is a
/// runtime knob because both forms are kept permanently: `Dense` is the
/// differential-test oracle and is the faster choice on small circuits.
///
/// This selects the representation of the IR poly type only; the
/// Gröbner-basis engine keeps its own dense `Polynomial`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReprKind {
    Dense,
    Sparse,
}

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
    /// Reuse the incremental Buchberger cache between successive
    /// `solve()` calls in the same `NativeFfBackend` instance. The cache
    /// amortises split-GB across calls whose constraint set didn't
    /// change. Disabling it forces every call to rebuild the basis from
    /// scratch — useful for benchmarking or for diagnosing cache bugs.
    pub cache_enabled: bool,
    /// Let the `aboz` lemma emit the (entailed) zero-product
    /// disjunctions for selector patterns whose selector cannot be
    /// proved non-zero, feeding the disjunction-aware solver path. On by
    /// default: each clause follows from an `s * o = 0` equality already
    /// in the IR, so it is sound and verdict-neutral; this keeps the
    /// pipeline's disjunction path live. Set `PICUS_NO_ABOZ_DISJ` to
    /// disable (e.g. for an A/B perf comparison).
    pub aboz_emit_disjunctions: bool,
    /// Representation of the IR poly type ([`ReprKind`]). Defaults to
    /// `Sparse` so lowering + the cvc5 path scale on wide rings (the dense
    /// form OOMs there); set `PICUS_POLY_REPR=dense` to force the dense
    /// representation (the differential-test oracle, faster on small rings).
    pub poly_repr: ReprKind,
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
            cache_enabled: true,
            aboz_emit_disjunctions: true,
            poly_repr: ReprKind::Sparse,
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
        if std::env::var_os("PICUS_NO_INCREMENTAL_CACHE").is_some() {
            c.cache_enabled = false;
        }
        if std::env::var_os("PICUS_NO_ABOZ_DISJ").is_some() {
            c.aboz_emit_disjunctions = false;
        }
        if let Ok(v) = std::env::var("PICUS_POLY_REPR") {
            match v.as_str() {
                "dense" => c.poly_repr = ReprKind::Dense,
                "sparse" => c.poly_repr = ReprKind::Sparse,
                _ => {}
            }
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
