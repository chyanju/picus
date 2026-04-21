//! Solver statistics tracking.
//!
//! Mirrors cvc5's `FfStatistics` class: tracks GB computation counts/times,
//! model construction metrics, and branching strategy usage.

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// Statistics for the finite field solver.
#[derive(Debug, Default)]
pub struct SolverStats {
    /// Number of Groebner basis computations (reasoning, not model construction).
    pub num_gb_runs: AtomicU64,
    /// Cumulative time in GB computations (nanoseconds).
    pub time_gb_nanos: AtomicU64,
    /// Number of times the ideal was trivially UNSAT (1 ∈ GB).
    pub num_trivial_unsat: AtomicU64,
    /// Cumulative time in model construction (nanoseconds).
    pub time_model_nanos: AtomicU64,
    /// Number of model construction failures.
    pub num_construction_errors: AtomicU64,
    /// Number of times the ideal was zero-dimensional (used minimal polynomial).
    pub num_ideal_minpoly: AtomicU64,
    /// Number of times the ideal was positive-dimensional (used round-robin).
    pub num_ideal_posdim: AtomicU64,
}

impl SolverStats {
    pub fn new() -> Self { Self::default() }

    /// Record a GB computation with its duration.
    pub fn record_gb_run(&self, duration: Duration) {
        self.num_gb_runs.fetch_add(1, Ordering::Relaxed);
        self.time_gb_nanos.fetch_add(duration.as_nanos() as u64, Ordering::Relaxed);
    }

    /// Record a trivial UNSAT.
    pub fn record_trivial_unsat(&self) {
        self.num_trivial_unsat.fetch_add(1, Ordering::Relaxed);
    }

    /// Record model construction time.
    pub fn record_model_construction(&self, duration: Duration) {
        self.time_model_nanos.fetch_add(duration.as_nanos() as u64, Ordering::Relaxed);
    }

    /// Record a model construction failure.
    pub fn record_construction_error(&self) {
        self.num_construction_errors.fetch_add(1, Ordering::Relaxed);
    }

    /// Record use of minimal polynomial (zero-dim ideal).
    pub fn record_minpoly(&self) {
        self.num_ideal_minpoly.fetch_add(1, Ordering::Relaxed);
    }

    /// Record use of round-robin (positive-dim ideal).
    pub fn record_posdim(&self) {
        self.num_ideal_posdim.fetch_add(1, Ordering::Relaxed);
    }

    /// Format as a human-readable summary.
    pub fn summary(&self) -> String {
        let gb_runs = self.num_gb_runs.load(Ordering::Relaxed);
        let gb_ms = self.time_gb_nanos.load(Ordering::Relaxed) / 1_000_000;
        let trivial = self.num_trivial_unsat.load(Ordering::Relaxed);
        let model_ms = self.time_model_nanos.load(Ordering::Relaxed) / 1_000_000;
        let errors = self.num_construction_errors.load(Ordering::Relaxed);
        let minpoly = self.num_ideal_minpoly.load(Ordering::Relaxed);
        let posdim = self.num_ideal_posdim.load(Ordering::Relaxed);
        format!(
            "GB runs: {} ({} ms), trivial UNSAT: {}, model: {} ms ({} errors), minpoly: {}, posdim: {}",
            gb_runs, gb_ms, trivial, model_ms, errors, minpoly, posdim
        )
    }
}

/// RAII timer that records elapsed time on drop.
pub struct Timer<'a> {
    start: Instant,
    target: &'a AtomicU64,
}

impl<'a> Timer<'a> {
    pub fn start(target: &'a AtomicU64) -> Self {
        Timer { start: Instant::now(), target }
    }
}

impl<'a> Drop for Timer<'a> {
    fn drop(&mut self) {
        let elapsed = self.start.elapsed().as_nanos() as u64;
        self.target.fetch_add(elapsed, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stats_basic() {
        let stats = SolverStats::new();
        stats.record_gb_run(Duration::from_millis(10));
        stats.record_gb_run(Duration::from_millis(20));
        stats.record_trivial_unsat();
        assert_eq!(stats.num_gb_runs.load(Ordering::Relaxed), 2);
        assert_eq!(stats.num_trivial_unsat.load(Ordering::Relaxed), 1);
        let summary = stats.summary();
        assert!(summary.contains("GB runs: 2"));
    }
}
