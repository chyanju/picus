//! Lightweight, zero-external-deps phase profiler.
//!
//! Enabled by setting the `PICUS_PROFILE` environment variable to any value.
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
//! `PICUS_PROFILE` is set.
//!
//! The profiler is intentionally *coarse* — it accumulates wall-clock time per
//! named site, with reentrancy support (nested calls to the same site are
//! credited to the inner timer; outer-only time is `outer - inner`).  Use it
//! to find which phases dominate, then drop in finer-grained timers as needed.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

static ENABLED: AtomicBool = AtomicBool::new(false);
static INIT: OnceLock<()> = OnceLock::new();
/// Monotonic id for active timers.
static NEXT_ID: AtomicU64 = AtomicU64::new(1);

fn init_from_env() {
    INIT.get_or_init(|| {
        if std::env::var_os("PICUS_PROFILE").is_some() {
            ENABLED.store(true, Ordering::Relaxed);
        }
    });
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

/// Returns true when profiling is active.
#[inline]
pub fn is_enabled() -> bool {
    init_from_env();
    ENABLED.load(Ordering::Relaxed)
}

/// Force-enable the profiler (e.g. from a CLI flag).
pub fn enable() {
    init_from_env();
    ENABLED.store(true, Ordering::Relaxed);
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

/// Dump the accumulated profile to stderr in a fixed-width table.  No-op when
/// the profiler is disabled or the table is empty.
pub fn dump_to_stderr(header: &str) {
    if !is_enabled() {
        return;
    }
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
