//! Sprint 2.0.3 — Buchberger statistics collector.
//!
//! Records per-call counts (S-pair reductions, inter-reductions, top-level entries)
//! into a process-global accumulator.  Enabled only when `is_enabled()` is
//! true (the picus-cli `--profile gb` flag flips it on).
//!
//! Cheap when disabled (one atomic load per callback).
//!
//! Usage:
//! ```ignore
//! gb_stats::enable();
//! // ... run buchberger with `&mut GbStatsObserver::default()` ...
//! gb_stats::dump_to_stderr();
//! ```
//!
//! Composes with other observers via [`ChainedObserver`].

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use feanor_math::algorithms::buchberger::BuchbergerObserver;
use feanor_math::ring::{El, RingStore};
use feanor_math::rings::multivariate::MultivariatePolyRing;

static ENABLED: AtomicBool = AtomicBool::new(false);

// Global counters (reset by `take`).
static N_BUCHBERGER_CALLS: AtomicU64 = AtomicU64::new(0);
static N_INITIAL_BASIS_TOTAL: AtomicU64 = AtomicU64::new(0);
static N_NEW_POLY: AtomicU64 = AtomicU64::new(0);
static N_INTER_REDUCE: AtomicU64 = AtomicU64::new(0);
// Sprint 2.3.5: running-sugar counters.
//   N_SUGAR_SAMPLES   — total `on_running_sugar` events (S-pair count).
//   N_SUGAR_TIGHTENED — events where final_sugar > initial_sugar
//                       (running update materially changed the value).
//   N_SUGAR_RAISES    — sum of n_raises across all events
//                       (total `Sugar::my_update` strict-raise calls).
static N_SUGAR_SAMPLES: AtomicU64 = AtomicU64::new(0);
static N_SUGAR_TIGHTENED: AtomicU64 = AtomicU64::new(0);
static N_SUGAR_RAISES: AtomicU64 = AtomicU64::new(0);

// Sprint 2.6b: per-batch zero-reduction tally.
//   N_BATCHES         — number of sugar batches processed (across ALL
//                       buchberger calls in this snapshot window).
//   N_BATCH_PAIRS     — total S-pairs processed (sum of n_pairs across
//                       all batches; redundant with sugar_samples but
//                       kept for direct comparability).
//   N_BATCH_ZEROS     — total S-pairs that reduced to zero
//                       (the prime target of Hilbert pair-pruning).
//   N_BATCH_PAIRS_HIGH — pairs in batches with sugar > HIGH_SUGAR_THRESHOLD
//                       (tracks the "expensive tail" Hilbert would prune).
//   MAX_SUGAR_SEEN    — highest sugar batch dispatched.
static N_BATCHES: AtomicU64 = AtomicU64::new(0);
static N_BATCH_PAIRS: AtomicU64 = AtomicU64::new(0);
static N_BATCH_ZEROS: AtomicU64 = AtomicU64::new(0);
static N_BATCH_PAIRS_HIGH: AtomicU64 = AtomicU64::new(0);
static MAX_SUGAR_SEEN: AtomicU64 = AtomicU64::new(0);

/// Threshold above which a sugar batch counts as "high sugar" for the
/// `N_BATCH_PAIRS_HIGH` tally.  Hardcoded to 6 because the cyclic-6
/// profile shows pair counts triple between sugar 7 and 8 and the
/// zero-reduction ratio jumps above 80% from sugar 8 onwards.
const HIGH_SUGAR_THRESHOLD: usize = 6;

/// Returns true when GB stats collection is active.
#[inline]
pub fn is_enabled() -> bool {
    ENABLED.load(Ordering::Relaxed)
}

/// Force-enable GB stats collection (e.g. from a CLI flag).
pub fn enable() {
    ENABLED.store(true, Ordering::Relaxed);
}

/// Snapshot of the current counters; clears them.
#[derive(Debug, Default, Clone, Copy)]
pub struct GbStatsSnapshot {
    pub buchberger_calls: u64,
    pub initial_basis_total: u64,
    pub new_polys: u64,
    pub inter_reductions: u64,
    /// Sprint 2.3.5: total S-pairs whose running sugar was sampled.
    pub sugar_samples: u64,
    /// Sprint 2.3.5: S-pairs where running update *raised* the sugar.
    pub sugar_tightened: u64,
    /// Sprint 2.3.5: total `Sugar::my_update` strict-raise events.
    pub sugar_raises: u64,
    /// Sprint 2.6b: number of sugar batches dispatched.
    pub batches: u64,
    /// Sprint 2.6b: total S-pairs across all batches.
    pub batch_pairs: u64,
    /// Sprint 2.6b: total S-pairs that reduced to zero.
    pub batch_zeros: u64,
    /// Sprint 2.6b: total S-pairs in batches with sugar > HIGH_SUGAR_THRESHOLD.
    pub batch_pairs_high: u64,
    /// Sprint 2.6b: highest sugar batch dispatched.
    pub max_sugar_seen: u64,
}

pub fn take() -> GbStatsSnapshot {
    GbStatsSnapshot {
        buchberger_calls: N_BUCHBERGER_CALLS.swap(0, Ordering::Relaxed),
        initial_basis_total: N_INITIAL_BASIS_TOTAL.swap(0, Ordering::Relaxed),
        new_polys: N_NEW_POLY.swap(0, Ordering::Relaxed),
        inter_reductions: N_INTER_REDUCE.swap(0, Ordering::Relaxed),
        sugar_samples: N_SUGAR_SAMPLES.swap(0, Ordering::Relaxed),
        sugar_tightened: N_SUGAR_TIGHTENED.swap(0, Ordering::Relaxed),
        sugar_raises: N_SUGAR_RAISES.swap(0, Ordering::Relaxed),
        batches: N_BATCHES.swap(0, Ordering::Relaxed),
        batch_pairs: N_BATCH_PAIRS.swap(0, Ordering::Relaxed),
        batch_zeros: N_BATCH_ZEROS.swap(0, Ordering::Relaxed),
        batch_pairs_high: N_BATCH_PAIRS_HIGH.swap(0, Ordering::Relaxed),
        max_sugar_seen: MAX_SUGAR_SEEN.swap(0, Ordering::Relaxed),
    }
}

/// Dump the current counters to stderr in a fixed-width table.  No-op when
/// the collector is disabled or no calls have been recorded.
pub fn dump_to_stderr(header: &str) {
    if !is_enabled() {
        return;
    }
    let s = take();
    if s.buchberger_calls == 0 {
        return;
    }
    eprintln!("\n=== picus-solver GB stats: {} ===", header);
    eprintln!("{:<32} {:>12}", "metric", "value");
    eprintln!("{:<32} {:>12}", "buchberger_calls", s.buchberger_calls);
    eprintln!("{:<32} {:>12}", "initial_basis_total", s.initial_basis_total);
    // Sprint 2.9 — relabeled.  Pre-2.8b, every restart triggered a
    // recursive `buchberger_observed` call, so `buchberger_calls - 1`
    // approximated "restart count".  Since 2.8b made restarts in-place,
    // this metric counts only **extra top-level entries** from
    // picus-solver's split DFS (not Buchberger's internal restart
    // trigger, which is rarely hit on the 17-bench workload).
    eprintln!("{:<32} {:>12}", "extra_top_level_calls", s.buchberger_calls.saturating_sub(1));
    eprintln!("{:<32} {:>12}", "new_polys (S-pair reductions ≠ 0)", s.new_polys);
    eprintln!("{:<32} {:>12}", "inter_reductions", s.inter_reductions);
    eprintln!("(note: inter_reductions remains 0 until feanor invokes on_inter_reduce)");
    // Sprint 2.3.5: running-sugar usage.
    eprintln!("{:<32} {:>12}", "sugar_samples (S-pairs)", s.sugar_samples);
    eprintln!("{:<32} {:>12}", "sugar_tightened (raised >0)", s.sugar_tightened);
    eprintln!("{:<32} {:>12}", "sugar_raises (my_update hits)", s.sugar_raises);
    if s.sugar_samples > 0 {
        let pct = 100.0 * (s.sugar_tightened as f64) / (s.sugar_samples as f64);
        eprintln!("{:<32} {:>11.2}%", "sugar_tightened/samples", pct);
    }
    // Sprint 2.6b: per-batch tally — use this to estimate Hilbert pair-pruning value.
    eprintln!("{:<32} {:>12}", "batches", s.batches);
    eprintln!("{:<32} {:>12}", "batch_pairs (S-pair total)", s.batch_pairs);
    eprintln!("{:<32} {:>12}", "batch_zeros (→ 0 reductions)", s.batch_zeros);
    if s.batch_pairs > 0 {
        let pct = 100.0 * (s.batch_zeros as f64) / (s.batch_pairs as f64);
        eprintln!("{:<32} {:>11.2}%", "batch_zeros/batch_pairs", pct);
    }
    eprintln!("{:<32} {:>12}", "max_sugar_seen", s.max_sugar_seen);
    eprintln!("{:<32} {:>12}",
        format!("pairs at sugar > {}", HIGH_SUGAR_THRESHOLD), s.batch_pairs_high);
    if s.batch_pairs > 0 {
        let pct = 100.0 * (s.batch_pairs_high as f64) / (s.batch_pairs as f64);
        eprintln!("{:<32} {:>11.2}%", "batch_pairs_high/batch_pairs", pct);
    }
    eprintln!("=== end GB stats ===");
}

/// Buchberger observer that increments the global counters.  Cheap when
/// `is_enabled()` is false.  Use as `&mut GbStatsObserver` or chain via
/// [`ChainedObserver`].
#[derive(Default)]
pub struct GbStatsObserver;

impl<P: RingStore> BuchbergerObserver<P> for GbStatsObserver
where
    P::Type: MultivariatePolyRing,
{
    fn on_initial_basis(&mut self, count: usize) {
        if !is_enabled() {
            return;
        }
        N_BUCHBERGER_CALLS.fetch_add(1, Ordering::Relaxed);
        N_INITIAL_BASIS_TOTAL.fetch_add(count as u64, Ordering::Relaxed);
    }

    fn on_new_poly(&mut self, _parent_indices: &[usize], _result: &El<P>) {
        if !is_enabled() {
            return;
        }
        N_NEW_POLY.fetch_add(1, Ordering::Relaxed);
    }

    fn on_inter_reduce(&mut self, _index: usize, _new_form: &El<P>) {
        if !is_enabled() {
            return;
        }
        N_INTER_REDUCE.fetch_add(1, Ordering::Relaxed);
    }

    fn on_running_sugar(&mut self, initial_sugar: usize, final_sugar: usize, n_raises: usize) {
        if !is_enabled() {
            return;
        }
        N_SUGAR_SAMPLES.fetch_add(1, Ordering::Relaxed);
        if final_sugar > initial_sugar {
            N_SUGAR_TIGHTENED.fetch_add(1, Ordering::Relaxed);
        }
        N_SUGAR_RAISES.fetch_add(n_raises as u64, Ordering::Relaxed);
    }

    fn on_sugar_batch_end(
        &mut self,
        sugar: usize,
        n_pairs_processed: usize,
        n_new_polys: usize,
        n_zero_reductions: usize,
        _basis_size_after: usize,
    ) {
        if !is_enabled() {
            return;
        }
        N_BATCHES.fetch_add(1, Ordering::Relaxed);
        N_BATCH_PAIRS.fetch_add(n_pairs_processed as u64, Ordering::Relaxed);
        N_BATCH_ZEROS.fetch_add(n_zero_reductions as u64, Ordering::Relaxed);
        debug_assert_eq!(n_new_polys + n_zero_reductions, n_pairs_processed,
            "GbStatsObserver: sugar batch invariant violated");
        if sugar > HIGH_SUGAR_THRESHOLD {
            N_BATCH_PAIRS_HIGH.fetch_add(n_pairs_processed as u64, Ordering::Relaxed);
        }
        // Monotone-max via CAS loop.
        let s64 = sugar as u64;
        let mut cur = MAX_SUGAR_SEEN.load(Ordering::Relaxed);
        while s64 > cur {
            match MAX_SUGAR_SEEN.compare_exchange_weak(
                cur, s64, Ordering::Relaxed, Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(actual) => cur = actual,
            }
        }
    }
}

/// Pair two observers; both receive every callback, in order.
pub struct ChainedObserver<'a, A, B> {
    pub first: &'a mut A,
    pub second: &'a mut B,
}

impl<'a, A, B> ChainedObserver<'a, A, B> {
    pub fn new(first: &'a mut A, second: &'a mut B) -> Self {
        Self { first, second }
    }
}

impl<'a, P, A, B> BuchbergerObserver<P> for ChainedObserver<'a, A, B>
where
    P: RingStore,
    P::Type: MultivariatePolyRing,
    A: BuchbergerObserver<P>,
    B: BuchbergerObserver<P>,
{
    fn on_initial_basis(&mut self, count: usize) {
        self.first.on_initial_basis(count);
        self.second.on_initial_basis(count);
    }

    fn on_new_poly(&mut self, parent_indices: &[usize], result: &El<P>) {
        self.first.on_new_poly(parent_indices, result);
        self.second.on_new_poly(parent_indices, result);
    }

    fn on_inter_reduce(&mut self, index: usize, new_form: &El<P>) {
        self.first.on_inter_reduce(index, new_form);
        self.second.on_inter_reduce(index, new_form);
    }

    fn on_running_sugar(&mut self, initial_sugar: usize, final_sugar: usize, n_raises: usize) {
        self.first.on_running_sugar(initial_sugar, final_sugar, n_raises);
        self.second.on_running_sugar(initial_sugar, final_sugar, n_raises);
    }

    fn on_sugar_batch_start(&mut self, sugar: usize, n_pairs_to_process: usize, basis_size: usize) {
        self.first.on_sugar_batch_start(sugar, n_pairs_to_process, basis_size);
        self.second.on_sugar_batch_start(sugar, n_pairs_to_process, basis_size);
    }

    fn on_sugar_batch_end(
        &mut self,
        sugar: usize,
        n_pairs_processed: usize,
        n_new_polys: usize,
        n_zero_reductions: usize,
        basis_size_after: usize,
    ) {
        self.first.on_sugar_batch_end(sugar, n_pairs_processed, n_new_polys, n_zero_reductions, basis_size_after);
        self.second.on_sugar_batch_end(sugar, n_pairs_processed, n_new_polys, n_zero_reductions, basis_size_after);
    }
}
