//! Lightweight, zero-external-deps phase profiler.
//!
//! Enabled via the `profile_enabled` config flag (CLI `--profile wall`).
//! When disabled, all `ScopedTimer` operations are reduced to a single atomic
//! load (the global enabled flag), so leaving the calls in production code
//! has negligible cost.
//!
//! Usage:
//! ```ignore
//! use crate::profile::ScopedTimer;
//! fn hot_function() {
//!     let _t = ScopedTimer::new("hot_function");
//!     // work...
//! }
//! ```
//!
//! Call [`dump_to_stderr`] (or [`take`]) before process exit to print the
//! accumulated table.  `picus-cli` calls `dump_to_stderr` automatically when
//! profiling is enabled (CLI `--profile wall`).
//!
//! The profiler is coarse: it accumulates total wall-clock time and a call
//! count per named site. Overlapping timers on the same site each add their
//! full elapsed time, so a recursive site's total can exceed wall-clock.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

/// Monotonic id for active timers.
static NEXT_ID: AtomicU64 = AtomicU64::new(1);

// Global counters for the split-GB driver and DFS, gated by the
// `gb_stats` config flag. Independent of the `ScopedTimer` table. All counters
// are `AtomicU64` so updates are wait-free and thread-safe.

#[derive(Default)]
pub struct SplitDfsCounters {
    pub branches_tried: AtomicU64,
    pub quick_eval_unsat_hits: AtomicU64,
    pub linear_quick_unsat_hits: AtomicU64,
    pub nogood_subsumption_hits: AtomicU64,
    pub branches_to_full_extend: AtomicU64,
    pub conflicts_returned: AtomicU64,
    pub max_dfs_depth: AtomicU64,
    pub time_in_basis_clone_ns: AtomicU64,
    pub time_in_split_gb_extend_ns: AtomicU64,
    pub time_in_quick_eval_unsat_ns: AtomicU64,
    pub time_in_linear_quick_unsat_ns: AtomicU64,
    pub points_returned: AtomicU64,
    pub split_zero_extend_calls: AtomicU64,
}

#[derive(Default)]
pub struct SplitGbCounters {
    pub split_gb_extend_calls: AtomicU64,
    pub fixpoint_iters_total: AtomicU64,
    pub fixpoint_iters_per_call_max: AtomicU64,
    pub propagate_candidates_total: AtomicU64,
    pub propagate_admit_passes: AtomicU64,
    pub propagate_contains_calls: AtomicU64,
    pub propagate_contains_true: AtomicU64,
    pub propagate_contains_false: AtomicU64,
    pub propagate_memo_hits: AtomicU64,
    pub new_polys_added_total: AtomicU64,
    pub new_polys_per_iter_max: AtomicU64,
    pub bit_eq_emitted_total: AtomicU64,
    pub time_in_extend_with_cancel_ns: AtomicU64,
    pub time_in_contains_ns: AtomicU64,
    pub time_in_bit_eq_ns: AtomicU64,
    pub basis_size_max: AtomicU64,
    pub basis_size_total_terms_max: AtomicU64,
    pub extend_with_cancel_calls: AtomicU64,
    pub extend_no_op_skips: AtomicU64,
    /// Fine-grained reducer timers.
    pub reduce_calls: AtomicU64,
    pub reduce_lt_pops: AtomicU64,
    pub reduce_div_lookups: AtomicU64,
    pub reduce_sub_scaled_calls: AtomicU64,
    pub time_div_lt_setup_ns: AtomicU64,
    pub time_pop_lt_ns: AtomicU64,
    pub time_div_lookup_ns: AtomicU64,
    pub time_sub_scaled_ns: AtomicU64,
    pub time_sub_scaled_setup_ns: AtomicU64,
    pub time_sub_scaled_addpoly_ns: AtomicU64,
    pub time_finalize_ns: AtomicU64,
    pub merge_owned_calls: AtomicU64,
    pub merge_owned_terms_total: AtomicU64,
}

pub static SPLIT_DFS: SplitDfsCounters = SplitDfsCounters::new_const();
pub static SPLIT_GB: SplitGbCounters = SplitGbCounters::new_const();

/// Counters for `gb::ideal::Ideal` introspection used by FGLM /
/// model construction. `gb_stats`-gated like the others.
#[derive(Default)]
pub struct IdealCounters {
    pub is_zero_dim_calls: AtomicU64,
    pub quotient_dimension_calls: AtomicU64,
}

impl IdealCounters {
    pub const fn new_const() -> Self {
        Self {
            is_zero_dim_calls: AtomicU64::new(0),
            quotient_dimension_calls: AtomicU64::new(0),
        }
    }
}

pub static IDEAL: IdealCounters = IdealCounters::new_const();

/// Counters for the native-ff SMT backend, surfaced when `gb_stats` is
/// enabled. Reports per-call encoding vs. solving time and
/// constraint-side digest stability across consecutive calls.
#[derive(Default)]
pub struct NativeFfBackendCounters {
    pub solve_calls: AtomicU64,
    pub encode_time_ns: AtomicU64,
    pub solve_inner_time_ns: AtomicU64,
    pub encoded_polys_total: AtomicU64,
    pub encoded_polys_max: AtomicU64,
    pub encoded_vars_max: AtomicU64,
    /// Number of distinct constraint-side digests observed.
    pub distinct_cs_digests: AtomicU64,
    /// Number of solve calls whose constraint-side digest equaled the
    /// immediately-previous call's.
    pub repeated_cs_digest_streak: AtomicU64,
    /// Cache hit / rebuild stats.
    pub cache_hits: AtomicU64,
    pub cache_rebuild_time_ns: AtomicU64,
    pub cache_query_diff_time_ns: AtomicU64,
    /// Number of solve calls that resumed an in-progress GB build saved
    /// from a prior cancelled call.
    pub cache_partial_resumes: AtomicU64,
    /// Number of partial builds that completed (`partial_build`
    /// → `cached_base`).
    pub cache_partial_completions: AtomicU64,
}

pub static NATIVE_FF: NativeFfBackendCounters = NativeFfBackendCounters::new_const();

impl NativeFfBackendCounters {
    pub const fn new_const() -> Self {
        Self {
            solve_calls: AtomicU64::new(0),
            encode_time_ns: AtomicU64::new(0),
            solve_inner_time_ns: AtomicU64::new(0),
            encoded_polys_total: AtomicU64::new(0),
            encoded_polys_max: AtomicU64::new(0),
            encoded_vars_max: AtomicU64::new(0),
            distinct_cs_digests: AtomicU64::new(0),
            repeated_cs_digest_streak: AtomicU64::new(0),
            cache_hits: AtomicU64::new(0),
            cache_rebuild_time_ns: AtomicU64::new(0),
            cache_query_diff_time_ns: AtomicU64::new(0),
            cache_partial_resumes: AtomicU64::new(0),
            cache_partial_completions: AtomicU64::new(0),
        }
    }
}

impl SplitDfsCounters {
    pub const fn new_const() -> Self {
        Self {
            branches_tried: AtomicU64::new(0),
            quick_eval_unsat_hits: AtomicU64::new(0),
            linear_quick_unsat_hits: AtomicU64::new(0),
            nogood_subsumption_hits: AtomicU64::new(0),
            branches_to_full_extend: AtomicU64::new(0),
            conflicts_returned: AtomicU64::new(0),
            max_dfs_depth: AtomicU64::new(0),
            time_in_basis_clone_ns: AtomicU64::new(0),
            time_in_split_gb_extend_ns: AtomicU64::new(0),
            time_in_quick_eval_unsat_ns: AtomicU64::new(0),
            time_in_linear_quick_unsat_ns: AtomicU64::new(0),
            points_returned: AtomicU64::new(0),
            split_zero_extend_calls: AtomicU64::new(0),
        }
    }
}

impl SplitGbCounters {
    pub const fn new_const() -> Self {
        Self {
            split_gb_extend_calls: AtomicU64::new(0),
            fixpoint_iters_total: AtomicU64::new(0),
            fixpoint_iters_per_call_max: AtomicU64::new(0),
            propagate_candidates_total: AtomicU64::new(0),
            propagate_admit_passes: AtomicU64::new(0),
            propagate_contains_calls: AtomicU64::new(0),
            propagate_contains_true: AtomicU64::new(0),
            propagate_contains_false: AtomicU64::new(0),
            propagate_memo_hits: AtomicU64::new(0),
            new_polys_added_total: AtomicU64::new(0),
            new_polys_per_iter_max: AtomicU64::new(0),
            bit_eq_emitted_total: AtomicU64::new(0),
            time_in_extend_with_cancel_ns: AtomicU64::new(0),
            time_in_contains_ns: AtomicU64::new(0),
            time_in_bit_eq_ns: AtomicU64::new(0),
            basis_size_max: AtomicU64::new(0),
            basis_size_total_terms_max: AtomicU64::new(0),
            extend_with_cancel_calls: AtomicU64::new(0),
            extend_no_op_skips: AtomicU64::new(0),
            reduce_calls: AtomicU64::new(0),
            reduce_lt_pops: AtomicU64::new(0),
            reduce_div_lookups: AtomicU64::new(0),
            reduce_sub_scaled_calls: AtomicU64::new(0),
            time_div_lt_setup_ns: AtomicU64::new(0),
            time_pop_lt_ns: AtomicU64::new(0),
            time_div_lookup_ns: AtomicU64::new(0),
            time_sub_scaled_ns: AtomicU64::new(0),
            time_sub_scaled_setup_ns: AtomicU64::new(0),
            time_sub_scaled_addpoly_ns: AtomicU64::new(0),
            time_finalize_ns: AtomicU64::new(0),
            merge_owned_calls: AtomicU64::new(0),
            merge_owned_terms_total: AtomicU64::new(0),
        }
    }
}

/// Atomic running-max update (CAS loop). Public so `metric::max!` can lower to
/// `observe_max(&PATH, v)` against any `AtomicU64` counter field.
pub fn observe_max(slot: &AtomicU64, v: u64) {
    let mut cur = slot.load(Ordering::Relaxed);
    while v > cur {
        match slot.compare_exchange_weak(cur, v, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => break,
            Err(now) => cur = now,
        }
    }
}

#[inline]
pub fn gb_stats_enabled() -> bool {
    crate::config::with(|c| c.gb_stats_enabled)
}

#[inline]
pub fn gb_trace_enabled() -> bool {
    crate::config::with(|c| c.gb_trace_enabled)
}

// ─────────────────────────── metric:: instrumentation ──────────────────────
//
// gb-stats instrumentation is invoked through the `metric::` namespace
// (`metric::incr!`, `metric::add!`, `metric::max!`, `metric::timer!`) plus the
// `#[metric]` attribute. Every profiling site uses this syntax and does not
// borrow main-logic syntax (`let`, `+=`, `if`), so
// `grep -E 'metric::|#\[metric\]'` finds exactly the profiling.
//
// Each macro takes the *typed counter path* (e.g.
// `SPLIT_GB.fixpoint_iters_total`) and lowers to a direct,
// `gb_stats_enabled`-gated atomic update (compiler-checked, no name dispatch).
// The `__metric_*` macros are the `#[macro_export]` implementations,
// re-exported under clean names by the `metric` module in `lib.rs`; call sites
// use `metric::incr!(PATH)` etc., not these directly.
//
// Vocabulary: incr! / add! / max! (counters), timer! (RAII into a global
// counter) / timer_local! (RAII into a local u64 tally) / stopwatch! (gb-stats
// Option<Instant> read at several points), gate! (read the flag once into a
// cached Gate for a hot loop/step, then pass it to a gated timer!/timer_local!),
// def! / bump! (local accumulators: declare / `+=`, drained once via a
// gb-stats-gated scope! + add!), next! (increment-and-return for a
// counter-as-id), scope! { } (a gb-stats-gated pure-profiling block),
// trace! { } / clock! (the gb-*trace* sink: verbose per-step output, distinct
// flag from gb-stats).
//
// Hot-loop gating: the per-monomial reducer timing in `ff::polynomial::
// dense_reduce` and the per-step sub-region timing in `ff::geobucket::
// sub_scaled_tail` must not do a thread-local config read on every iteration.
// They use `metric::gate!(g)` to read `gb_stats_enabled()` once, then gate the
// inner timers on the cached bool via `metric::timer_local!(g, ..)` /
// `metric::timer!(g, ..)`.

/// Backs `metric::incr!(counter)`: `counter += 1` when gb-stats is on.
#[macro_export]
macro_rules! __metric_incr {
    ($c:expr) => {
        if $crate::profile::gb_stats_enabled() {
            $c.fetch_add(1, ::std::sync::atomic::Ordering::Relaxed);
        }
    };
}

/// Backs `metric::add!(counter, n)`: `counter += n` when gb-stats is on.
#[macro_export]
macro_rules! __metric_add {
    ($c:expr, $n:expr) => {
        if $crate::profile::gb_stats_enabled() {
            $c.fetch_add($n, ::std::sync::atomic::Ordering::Relaxed);
        }
    };
}

/// Backs `metric::max!(counter, v)`: `counter = max(counter, v)` when on.
#[macro_export]
macro_rules! __metric_max {
    ($c:expr, $v:expr) => {
        if $crate::profile::gb_stats_enabled() {
            $crate::profile::observe_max(&$c, $v);
        }
    };
}

/// RAII timer that adds its elapsed wall-clock (ns) to `slot` on drop. Takes a
/// timestamp only when [`gb_stats_enabled`] (checked once at construction), so
/// it is a no-op in production. Construct via `metric::timer!`.
pub struct MetricTimer<'a> {
    slot: Option<(&'a AtomicU64, Instant)>,
}

impl<'a> MetricTimer<'a> {
    #[inline]
    pub fn new(slot: &'a AtomicU64) -> Self {
        Self::new_gated(gb_stats_enabled(), slot)
    }

    /// Like [`Self::new`] but takes a pre-read gb-stats flag (a cached
    /// [`Gate`]), so a caller timing two sub-regions of one hot step reads
    /// the thread-local config once rather than per `metric::timer!`. See
    /// `metric::timer!(gate, counter)`.
    #[inline]
    pub fn new_gated(on: bool, slot: &'a AtomicU64) -> Self {
        if on {
            MetricTimer { slot: Some((slot, Instant::now())) }
        } else {
            MetricTimer { slot: None }
        }
    }
}

impl Drop for MetricTimer<'_> {
    #[inline]
    fn drop(&mut self) {
        if let Some((slot, start)) = self.slot {
            slot.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        }
    }
}

/// Backs `metric::timer!(counter);` (re-reads the gb-stats flag) and
/// `metric::timer!(gate, counter);` (uses a pre-read [`Gate`], for a hot step
/// that times two sub-regions without re-reading the thread-local config).
/// Statement-form RAII timer: expands to a hidden, block-scoped guard (no bare
/// `let` at the call site); on drop it adds the elapsed ns to `counter`. Times
/// "this line → end of enclosing block".
#[macro_export]
macro_rules! __metric_timer {
    ($c:expr) => {
        let _metric_guard = $crate::profile::MetricTimer::new(&$c);
    };
    ($gate:expr, $c:expr) => {
        let _metric_guard = $crate::profile::MetricTimer::new_gated($gate.on, &$c);
    };
}

/// RAII timer that accumulates its elapsed ns into a **local** `u64` (not a
/// global counter) on drop, gated by gb-stats. For per-phase time tallies that
/// are summed into a local across a loop and printed in a `metric::scope!`
/// dump. Construct via `metric::timer_local!`.
pub struct LocalTimer<'a> {
    slot: Option<(&'a mut u64, Instant)>,
}

impl<'a> LocalTimer<'a> {
    #[inline]
    pub fn new(slot: &'a mut u64) -> Self {
        Self::new_gated(gb_stats_enabled(), slot)
    }

    /// Like [`Self::new`] but takes a pre-read gb-stats flag (a cached
    /// [`Gate`]), so a hot loop does not re-read the thread-local config on
    /// every iteration. See `metric::timer_local!(gate, local)`.
    #[inline]
    pub fn new_gated(on: bool, slot: &'a mut u64) -> Self {
        if on {
            LocalTimer { slot: Some((slot, Instant::now())) }
        } else {
            LocalTimer { slot: None }
        }
    }
}

/// A cached gb-stats gate. Read `gb_stats_enabled()` once (e.g. at the top of a
/// hot reducer loop) via `metric::gate!(g)`, then pass `g` to the per-iteration
/// `metric::timer_local!(g, ..)` so the hottest loop reads a cached bool field
/// rather than re-doing a thread-local config lookup every iteration.
#[derive(Clone, Copy)]
pub struct Gate {
    pub on: bool,
}

impl Gate {
    #[inline]
    pub fn new() -> Self {
        Gate { on: gb_stats_enabled() }
    }
}

impl Default for Gate {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for LocalTimer<'_> {
    #[inline]
    fn drop(&mut self) {
        if let Some((slot, start)) = &mut self.slot {
            **slot += start.elapsed().as_nanos() as u64;
        }
    }
}

/// Backs `metric::timer_local!(local);` (re-reads the gb-stats flag) and
/// `metric::timer_local!(gate, local);` (uses a pre-read [`Gate`], for hot
/// loops). Block-scoped RAII timer adding elapsed ns to the local `u64`
/// accumulator on drop. See [`LocalTimer`].
#[macro_export]
macro_rules! __metric_timer_local {
    ($local:expr) => {
        let _metric_guard = $crate::profile::LocalTimer::new(&mut $local);
    };
    ($gate:expr, $local:expr) => {
        let _metric_guard = $crate::profile::LocalTimer::new_gated($gate.on, &mut $local);
    };
}

/// Backs `metric::gate!(g);`: read the gb-stats flag once into a cached
/// [`Gate`] for a hot loop, then gate per-iteration `metric::timer_local!(g, ..)`
/// on the cached bool instead of re-reading the thread-local config.
#[macro_export]
macro_rules! __metric_gate {
    ($name:ident) => {
        let $name = $crate::profile::Gate::new();
    };
}

/// Backs `metric::stopwatch!(name);`: declare an `Option<Instant>` profiling
/// local that is `Some(now)` only when gb-stats is on, readable at several
/// later `metric::scope!` dump points via `name.map(|t| t.elapsed())`. The
/// gb-stats analogue of [`metric::clock!`] (which is gb-trace).
#[macro_export]
macro_rules! __metric_stopwatch {
    ($name:ident) => {
        let $name = if $crate::profile::gb_stats_enabled() {
            ::core::option::Option::Some(::std::time::Instant::now())
        } else {
            ::core::option::Option::None
        };
    };
}

// Local-accumulator vocabulary for hot loops: keep per-iteration work to a
// plain local `+=` (no atomic), then drain once via a gb-stats-gated
// `metric::scope!` + `metric::add!`. `def`/`bump` are always-on (a local
// `u64`, negligible when stats are off); only the drain block is gated.

/// Backs `metric::def!(acc);` (accumulator `= 0`) and
/// `metric::def!(name = expr);` (a profiling-local seeded from `expr`, e.g. an
/// entry snapshot of a counter, or `metric::next!`).
#[macro_export]
macro_rules! __metric_def {
    ($name:ident) => {
        let mut $name: u64 = 0;
    };
    ($name:ident = $init:expr) => {
        let $name = $init;
    };
}

/// Backs `metric::next!(counter)`: increment `counter` and return the new
/// value (a per-call sequence id) when gb-stats is on, else `0`. For
/// profiling ids that need the post-increment value, which `metric::incr!`
/// discards.
#[macro_export]
macro_rules! __metric_next {
    ($c:expr) => {
        if $crate::profile::gb_stats_enabled() {
            $c.fetch_add(1, ::std::sync::atomic::Ordering::Relaxed) + 1
        } else {
            0
        }
    };
}

/// Backs `metric::trace! { ... }`: run a pure gb-*trace* block (gated by
/// `gb_trace_enabled`, the verbose per-step diagnostic sink, distinct from the
/// gb-stats `metric::scope!`).
#[macro_export]
macro_rules! __metric_trace {
    ($($body:tt)*) => {
        if $crate::profile::gb_trace_enabled() {
            $($body)*
        }
    };
}

/// Backs `metric::clock!(name);`: declare an `Option<Instant>` profiling
/// local that is `Some(now)` only when gb-trace is on, for a
/// `metric::trace!`-printed elapsed. No `Instant::now()` cost when trace is off.
#[macro_export]
macro_rules! __metric_clock {
    ($name:ident) => {
        let $name = if $crate::profile::gb_trace_enabled() {
            ::core::option::Option::Some(::std::time::Instant::now())
        } else {
            ::core::option::Option::None
        };
    };
}

/// Backs `metric::bump!(acc)` / `metric::bump!(acc, n)`: local `acc += 1|n`.
#[macro_export]
macro_rules! __metric_bump {
    ($name:ident) => {
        $name += 1;
    };
    ($name:ident, $n:expr) => {
        $name += $n;
    };
}

/// Backs `metric::scope! { ... }`: run a pure-profiling block only when
/// gb-stats is on. For telemetry that is more than one counter (stats-only
/// computation feeding several counters, a per-run dump). The block must
/// contain only profiling — no main-logic side effects, since it is skipped
/// when gb-stats is off.
#[macro_export]
macro_rules! __metric_scope {
    ($($body:tt)*) => {
        if $crate::profile::gb_stats_enabled() {
            $($body)*
        }
    };
}

/// Print SplitDfs/SplitGb counters to stderr. Called from the top-level
/// `solve_encoded` (or `picus-cli`) at termination when `gb_stats` is enabled.
pub fn dump_split_stats_to_stderr() {
    // No-op when nothing has been recorded — i.e. when
    // `gb_stats_enabled` was false (or the relevant solver paths
    // were never exercised) for the entire run.
    let nothing_recorded = SPLIT_DFS.branches_tried.load(Ordering::Relaxed) == 0
        && SPLIT_GB.split_gb_extend_calls.load(Ordering::Relaxed) == 0
        && NATIVE_FF.solve_calls.load(Ordering::Relaxed) == 0;
    if nothing_recorded {
        return;
    }
    let d = &SPLIT_DFS;
    let g = &SPLIT_GB;
    let load = |a: &AtomicU64| a.load(Ordering::Relaxed);
    eprintln!("\n=== picus split-GB driver stats ===");
    eprintln!("[split-dfs] split_zero_extend_calls={} branches_tried={} quick_eval_unsat={} lin_quick_unsat={} nogood_hits={} branches_to_full_extend={} conflicts={} points={} max_depth={}",
        load(&d.split_zero_extend_calls),
        load(&d.branches_tried),
        load(&d.quick_eval_unsat_hits),
        load(&d.linear_quick_unsat_hits),
        load(&d.nogood_subsumption_hits),
        load(&d.branches_to_full_extend),
        load(&d.conflicts_returned),
        load(&d.points_returned),
        load(&d.max_dfs_depth),
    );
    eprintln!("[split-dfs-time-ms] basis_clone={:.2} split_gb_extend={:.2} quick_eval_unsat={:.2} lin_quick_unsat={:.2}",
        load(&d.time_in_basis_clone_ns) as f64 / 1e6,
        load(&d.time_in_split_gb_extend_ns) as f64 / 1e6,
        load(&d.time_in_quick_eval_unsat_ns) as f64 / 1e6,
        load(&d.time_in_linear_quick_unsat_ns) as f64 / 1e6,
    );
    eprintln!("[split-gb] calls={} fixpoint_iters_total={} fixpoint_iters_per_call_max={} new_polys_added_total={} new_polys_per_iter_max={} bit_eqs_total={} basis_size_max={} basis_terms_max={}",
        load(&g.split_gb_extend_calls),
        load(&g.fixpoint_iters_total),
        load(&g.fixpoint_iters_per_call_max),
        load(&g.new_polys_added_total),
        load(&g.new_polys_per_iter_max),
        load(&g.bit_eq_emitted_total),
        load(&g.basis_size_max),
        load(&g.basis_size_total_terms_max),
    );
    let calls = load(&g.propagate_contains_calls);
    let trues = load(&g.propagate_contains_true);
    let falses = load(&g.propagate_contains_false);
    let true_pct = if calls > 0 { (trues as f64 * 100.0) / calls as f64 } else { 0.0 };
    let memo_hits = load(&g.propagate_memo_hits);
    let admit = load(&g.propagate_admit_passes);
    let memo_hit_pct = if admit > 0 { (memo_hits as f64 * 100.0) / admit as f64 } else { 0.0 };
    eprintln!("[split-gb-propagate] candidates={} admit_passes={} memo_hits={} memo_hit_rate={:.1}% contains_calls={} contains_true={} contains_false={} contains_true_rate={:.1}%",
        load(&g.propagate_candidates_total),
        admit,
        memo_hits,
        memo_hit_pct,
        calls,
        trues,
        falses,
        true_pct,
    );
    eprintln!("[split-gb-time-ms] extend_with_cancel={:.2} contains={:.2} bit_eq={:.2}",
        load(&g.time_in_extend_with_cancel_ns) as f64 / 1e6,
        load(&g.time_in_contains_ns) as f64 / 1e6,
        load(&g.time_in_bit_eq_ns) as f64 / 1e6,
    );
    eprintln!("[split-gb-extend] calls={} no_op_skips={}",
        load(&g.extend_with_cancel_calls),
        load(&g.extend_no_op_skips),
    );
    let r_calls = load(&g.reduce_calls);
    if r_calls > 0 {
        let avg_pops = load(&g.reduce_lt_pops) as f64 / r_calls as f64;
        let avg_lookups = load(&g.reduce_div_lookups) as f64 / r_calls as f64;
        eprintln!(
            "[reducer] calls={} avg_lt_pops={:.1} avg_div_lookups={:.1} sub_scaled_calls={}",
            r_calls, avg_pops, avg_lookups,
            load(&g.reduce_sub_scaled_calls),
        );
        eprintln!(
            "[reducer-time-ms] div_lt_setup={:.2} pop_lt={:.2} div_lookup={:.2} sub_scaled={:.2} (setup={:.2} addpoly={:.2}) finalize={:.2}",
            load(&g.time_div_lt_setup_ns) as f64 / 1e6,
            load(&g.time_pop_lt_ns) as f64 / 1e6,
            load(&g.time_div_lookup_ns) as f64 / 1e6,
            load(&g.time_sub_scaled_ns) as f64 / 1e6,
            load(&g.time_sub_scaled_setup_ns) as f64 / 1e6,
            load(&g.time_sub_scaled_addpoly_ns) as f64 / 1e6,
            load(&g.time_finalize_ns) as f64 / 1e6,
        );
    }
    let mo_calls = load(&g.merge_owned_calls);
    if mo_calls > 0 {
        eprintln!(
            "[merge-owned] calls={} terms_total={} avg_terms={:.1}",
            mo_calls,
            load(&g.merge_owned_terms_total),
            load(&g.merge_owned_terms_total) as f64 / mo_calls as f64,
        );
    }
    let nf = &NATIVE_FF;
    let nf_calls = load(&nf.solve_calls);
    if nf_calls > 0 {
        let enc_ms = load(&nf.encode_time_ns) as f64 / 1e6;
        let solve_ms = load(&nf.solve_inner_time_ns) as f64 / 1e6;
        let total_ms = enc_ms + solve_ms;
        let enc_pct = if total_ms > 0.0 { enc_ms / total_ms * 100.0 } else { 0.0 };
        eprintln!(
            "[native-ff] solve_calls={} encoded_polys_max={} encoded_vars_max={} polys_total={} distinct_cs_digests={} repeated_streak={}",
            nf_calls,
            load(&nf.encoded_polys_max),
            load(&nf.encoded_vars_max),
            load(&nf.encoded_polys_total),
            load(&nf.distinct_cs_digests),
            load(&nf.repeated_cs_digest_streak),
        );
        eprintln!(
            "[native-ff-time-ms] encode={:.2} solve_inner={:.2} total={:.2} encode_pct={:.1}%",
            enc_ms, solve_ms, total_ms, enc_pct,
        );
        let hits = load(&nf.cache_hits);
        let rebuild_ms = load(&nf.cache_rebuild_time_ns) as f64 / 1e6;
        let diff_ms = load(&nf.cache_query_diff_time_ns) as f64 / 1e6;
        let resumes = load(&nf.cache_partial_resumes);
        let completions = load(&nf.cache_partial_completions);
        if hits > 0 || rebuild_ms > 0.0 || resumes > 0 {
            let total = hits + load(&nf.distinct_cs_digests);
            let hit_pct = if total > 0 { hits as f64 * 100.0 / total as f64 } else { 0.0 };
            eprintln!(
                "[native-ff-cache] hits={} rebuilds={} hit_rate={:.1}% rebuild_ms={:.2} query_diff_ms={:.2} partial_resumes={} partial_completions={}",
                hits,
                load(&nf.distinct_cs_digests),
                hit_pct, rebuild_ms, diff_ms, resumes, completions,
            );
        }
    }
    eprintln!("=== end split-GB stats ===\n");
}


/// Per-site stats: total time, call count.
#[derive(Default, Clone, Copy)]
struct SiteStats {
    total: Duration,
    count: u64,
}

fn table() -> &'static Mutex<HashMap<&'static str, SiteStats>> {
    static TABLE: OnceLock<Mutex<HashMap<&'static str, SiteStats>>> = OnceLock::new();
    TABLE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// In-flight timers (id -> (label, start_instant)).  Used so a SIGTERM dump
/// can include time spent in calls that haven't returned yet.
fn active() -> &'static Mutex<HashMap<u64, (&'static str, Instant)>> {
    static ACTIVE: OnceLock<Mutex<HashMap<u64, (&'static str, Instant)>>> = OnceLock::new();
    ACTIVE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Returns true when profiling is active. Reads
/// [`crate::config::RuntimeConfig::profile_enabled`] on each call so
/// callers (the picus facade, library users) can flip the knob at
/// runtime via [`crate::config::ConfigGuard`].
#[inline]
pub fn is_enabled() -> bool {
    crate::config::with(|c| c.profile_enabled)
}

/// RAII timer for a named code site.  Cheap when profiling is disabled.
pub struct ScopedTimer {
    label: &'static str,
    start: Option<Instant>,
    id: u64,
}

impl ScopedTimer {
    #[inline]
    pub fn new(label: &'static str) -> Self {
        if is_enabled() {
            let now = Instant::now();
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            if let Ok(mut a) = active().lock() {
                a.insert(id, (label, now));
            }
            Self { label, start: Some(now), id }
        } else {
            Self { label, start: None, id: 0 }
        }
    }
}

impl Drop for ScopedTimer {
    #[inline]
    fn drop(&mut self) {
        if let Some(start) = self.start {
            let elapsed = start.elapsed();
            if let Ok(mut t) = table().lock() {
                let s = t.entry(self.label).or_default();
                s.total += elapsed;
                s.count += 1;
            }
            if let Ok(mut a) = active().lock() {
                a.remove(&self.id);
            }
        }
    }
}

/// Take the current accumulated profile, clearing the table.  Returns rows
/// sorted by total time descending.
pub fn take() -> Vec<(&'static str, Duration, u64)> {
    let mut rows: Vec<(&'static str, Duration, u64)> = if let Ok(mut t) = table().lock() {
        let snapshot: Vec<_> = t.iter().map(|(&k, &v)| (k, v.total, v.count)).collect();
        t.clear();
        snapshot
    } else {
        Vec::new()
    };
    rows.sort_by(|a, b| b.1.cmp(&a.1));
    rows
}

/// Dump the accumulated profile to stderr in a fixed-width table.  No-op
/// when the accumulated table and in-flight set are both empty (which is
/// the case whenever profiling was never enabled for the current thread).
pub fn dump_to_stderr(header: &str) {
    // Snapshot in-flight timers so we can show where we are right now.
    let in_flight: Vec<(&'static str, Duration)> = if let Ok(a) = active().lock() {
        a.values().map(|(label, start)| (*label, start.elapsed())).collect()
    } else {
        Vec::new()
    };
    let rows = take();
    if rows.is_empty() && in_flight.is_empty() {
        return;
    }
    let total: Duration = rows.iter().map(|r| r.1).sum();
    eprintln!("\n=== picus-solver profile: {} ===", header);
    eprintln!(
        "{:<40} {:>12} {:>10} {:>10}",
        "site", "total_ms", "count", "share"
    );
    for (label, dur, count) in rows {
        let ms = dur.as_secs_f64() * 1e3;
        let share = if total.is_zero() {
            0.0
        } else {
            dur.as_secs_f64() / total.as_secs_f64() * 100.0
        };
        eprintln!("{:<40} {:>12.2} {:>10} {:>9.1}%", label, ms, count, share);
    }
    if !in_flight.is_empty() {
        eprintln!("--- in-flight (not yet returned) ---");
        let mut sorted = in_flight;
        sorted.sort_by(|a, b| b.1.cmp(&a.1));
        for (label, dur) in sorted {
            eprintln!("{:<40} {:>12.2} ms (running)", label, dur.as_secs_f64() * 1e3);
        }
    }
    eprintln!("=== end profile ({:.2}ms completed wall) ===", total.as_secs_f64() * 1e3);
}

#[cfg(test)]
#[path = "profile_tests.rs"]
mod tests;
