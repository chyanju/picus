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

use serde::{Deserialize, Serialize};
use std::cell::RefCell;

/// Strategy for computing a Groebner basis. Set via
/// [`RuntimeConfig::gb_strategy`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum GbStrategy {
    /// Plain DegRevLex Buchberger on `P`. Default.
    Direct,
    /// Homogenize → GB on `P[h]` → dehomogenize → interreduce.
    ByHomog,
    /// Pick `Direct` if every input is already homogeneous w.r.t. the
    /// total-degree grading; otherwise pick `ByHomog`.
    Auto,
}

/// Polynomial storage representation, selected at ring construction and
/// carried by `ff::PolyRing.repr`. Applies to the IR (`PolyIR` equalities/
/// disjunctions, lemma `learned` buffers) and the native Gröbner solve.
///
/// `Dense` stores each monomial as a full-length exponent vector
/// (O(n_vars) per term); `Sparse` stores only the nonzero `(var, exp)`
/// pairs (O(nnz) per term). On wide rings (tens of thousands of variables)
/// dense resident memory is O(n_vars · terms), so `Sparse` is the scalable
/// choice. Both are kept permanently: `Dense` is the differential-test
/// oracle and is faster on small/narrow rings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ReprKind {
    Dense,
    Sparse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
    /// Seed the compiled defaults, then apply any `PICUS_*` environment
    /// overrides. Used to initialise the thread-local config the first
    /// time a thread asks for it, so existing benchmark scripts and CLI
    /// invocations keep their behaviour.
    pub fn from_env() -> Self {
        let mut c = Self::default();
        c.apply_overlay(&EngineOverlay::from_env());
        c
    }

    /// Merge the `Some` fields of `o` onto `self`; `None` fields are
    /// left untouched. This is the overlay/merge step that layers a
    /// config file, environment, or CLI flags onto a base config.
    pub fn apply_overlay(&mut self, o: &EngineOverlay) {
        if let Some(v) = o.gb_strategy { self.gb_strategy = v; }
        if let Some(v) = o.use_f4 { self.use_f4 = v; }
        if let Some(v) = o.dnf_cap { self.dnf_cap = v; }
        if let Some(v) = o.dnf_enabled { self.dnf_enabled = v; }
        if let Some(v) = o.cdclt_iter_cap { self.cdclt_iter_cap = v; }
        if let Some(v) = o.gb_stats_enabled { self.gb_stats_enabled = v; }
        if let Some(v) = o.gb_trace_enabled { self.gb_trace_enabled = v; }
        if let Some(v) = o.profile_enabled { self.profile_enabled = v; }
        if let Some(v) = o.cache_enabled { self.cache_enabled = v; }
        if let Some(v) = o.aboz_emit_disjunctions { self.aboz_emit_disjunctions = v; }
        if let Some(v) = o.poly_repr { self.poly_repr = v; }
    }
}

/// Partial overlay for [`RuntimeConfig`]: every field is optional, so a
/// single config layer (file, environment, CLI) carries only the knobs
/// it actually sets. Merged onto a base via [`RuntimeConfig::apply_overlay`];
/// later layers win.
///
/// TOML keys mirror the [`RuntimeConfig`] field names exactly, so adding
/// a knob is one field here plus one line in `apply_overlay` — no rename
/// bookkeeping. `deny_unknown_fields` turns a mistyped key into an error
/// rather than a silent no-op.
#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct EngineOverlay {
    pub gb_strategy: Option<GbStrategy>,
    pub use_f4: Option<bool>,
    pub dnf_cap: Option<u64>,
    pub dnf_enabled: Option<bool>,
    pub cdclt_iter_cap: Option<u64>,
    pub gb_stats_enabled: Option<bool>,
    pub gb_trace_enabled: Option<bool>,
    pub profile_enabled: Option<bool>,
    pub cache_enabled: Option<bool>,
    pub aboz_emit_disjunctions: Option<bool>,
    pub poly_repr: Option<ReprKind>,
}

impl EngineOverlay {
    /// Read the `PICUS_*` environment variables into an overlay. Absent
    /// variables stay `None` so they don't clobber lower config layers.
    pub fn from_env() -> Self {
        let mut o = Self::default();
        if std::env::var_os("PICUS_USE_F4").is_some() {
            o.use_f4 = Some(true);
        }
        if let Ok(v) = std::env::var("PICUS_BOOLEAN") {
            o.dnf_enabled = Some(v == "dnf");
        }
        if let Ok(v) = std::env::var("PICUS_DNF_CAP") {
            if let Ok(n) = v.parse::<u64>() {
                o.dnf_cap = Some(n);
            }
        }
        if let Ok(v) = std::env::var("PICUS_CDCLT_ITER_CAP") {
            if let Ok(n) = v.parse::<u64>() {
                o.cdclt_iter_cap = Some(n);
            }
        }
        if std::env::var_os("PICUS_GB_STATS").is_some() {
            o.gb_stats_enabled = Some(true);
        }
        if std::env::var_os("PICUS_GB_TRACE").is_some() {
            o.gb_trace_enabled = Some(true);
        }
        if std::env::var_os("PICUS_PROFILE").is_some() {
            o.profile_enabled = Some(true);
        }
        if std::env::var_os("PICUS_NO_INCREMENTAL_CACHE").is_some() {
            o.cache_enabled = Some(false);
        }
        if std::env::var_os("PICUS_NO_ABOZ_DISJ").is_some() {
            o.aboz_emit_disjunctions = Some(false);
        }
        if let Ok(v) = std::env::var("PICUS_POLY_REPR") {
            match v.as_str() {
                "dense" => o.poly_repr = Some(ReprKind::Dense),
                "sparse" => o.poly_repr = Some(ReprKind::Sparse),
                _ => {}
            }
        }
        o
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
