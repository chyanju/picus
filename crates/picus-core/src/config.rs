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
//! The thread-local seed is the compiled [`RuntimeConfig::default`];
//! file and CLI layers are merged on top by the `picus` facade
//! (`resolve_config`) via [`RuntimeConfig::apply_overlay`].

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
    /// pipeline's disjunction path live. Set `aboz_emit_disjunctions =
    /// false` in config (CLI `--no-aboz-disj`) to disable (e.g. for an
    /// A/B perf comparison).
    pub aboz_emit_disjunctions: bool,
    /// Representation of the IR poly type ([`ReprKind`]). Defaults to
    /// `Sparse` so lowering + the cvc5 path scale on wide rings (the dense
    /// form OOMs there); set `poly_repr = "dense"` in config (CLI
    /// `--poly-repr dense`) to force the dense representation (the
    /// differential-test oracle, faster on small rings).
    pub poly_repr: ReprKind,
    /// Opt-in linear (Gaussian) pre-elimination (cvc5 `gauss.cpp`
    /// analogue): before solving, reduce the nonlinear constraints modulo
    /// a Gröbner basis of the linear subsystem, substituting out pivot
    /// variables. Off by default — split-GB already handles linear
    /// constraints in basis 0, and the substitution can densify the
    /// nonlinear part and add per-`solve` overhead, so it is a net loss on
    /// the general workload. Exposed as a knob for linear-heavy
    /// conjunctive circuits where it may pay off.
    pub linear_elim: bool,
    /// Track inter-reduction reducer dependencies in the single-GB UNSAT-core
    /// tracer (`GbTracer`), so a trivial core reflects the basis elements that
    /// actually reduced the contradiction — matching cvc5/CoCoA's precise
    /// cores. On by default: it only affects the non-default SingleGb path
    /// (the default split-GB path uses a separate tracer with `NoObserver`,
    /// so there is no cost on the PLDI/main workload), and gives precise
    /// cores there. Set false to drop the small per-reduce counting cost on
    /// the SingleGb path.
    pub track_inter_reduce_deps: bool,
    /// Use triangular model construction (cvc5 `multi_roots` analogue) on the
    /// **default split-GB** path: when the combined system is zero-dimensional,
    /// decide it by complete univariate-root + back-substitution enumeration
    /// instead of the split brancher DFS. Sound: SAT returns a verified
    /// witness; UNSAT comes only from a complete zero-dimensional enumeration;
    /// any other case (positive-dimensional, inconclusive, cancelled) falls
    /// back to the DFS, so it can change timing/`Unknown`-resolution but never
    /// a definite verdict. Off by default: validated ON (corpus verdicts
    /// identical to baseline) but corpus-neutral — no `Unknown` is resolved
    /// (the PLDI set has no zero-dim-stuck circuit), and it builds the combined
    /// GB the split path avoids. On (`--split-triangular on`) for zero-dim
    /// workloads where the bounded brancher otherwise leaves `Unknown`.
    pub split_triangular: bool,
    /// Cache the geobucket reducer's divisor index (DivMask buckets + degree
    /// order) across S-pair reductions whose active basis is unchanged, instead
    /// of rebuilding it per call. Result-preserving (same normal form). Off by
    /// default: validated ON (corpus verdicts identical) but corpus-neutral —
    /// the Buchberger basis grows so the cache hit rate is low (~39% on
    /// Pedersen) and the rebuild-on-miss offsets the hit savings. On
    /// (`--reducer-index-cache on`) for long runs against a stable basis.
    pub reducer_index_cache: bool,
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
            linear_elim: false,
            track_inter_reduce_deps: true,
            // Validated with these ON: the corpus verdicts are identical to
            // the baseline (both are correct/verdict-neutral), but neither
            // improves the corpus (no Unknown resolved, timings neutral) and
            // both add work the default path otherwise avoids — so the shipped
            // default is OFF, exposed as a switch for workloads that benefit.
            split_triangular: false,
            reducer_index_cache: false,
        }
    }
}

impl RuntimeConfig {
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
        if let Some(v) = o.linear_elim { self.linear_elim = v; }
        if let Some(v) = o.track_inter_reduce_deps { self.track_inter_reduce_deps = v; }
        if let Some(v) = o.split_triangular { self.split_triangular = v; }
        if let Some(v) = o.reducer_index_cache { self.reducer_index_cache = v; }
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
    pub linear_elim: Option<bool>,
    pub track_inter_reduce_deps: Option<bool>,
    pub split_triangular: Option<bool>,
    pub reducer_index_cache: Option<bool>,
}

thread_local! {
    static THREAD_CONFIG: RefCell<RuntimeConfig> = RefCell::new(RuntimeConfig::default());
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
