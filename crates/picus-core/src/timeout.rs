//! Cooperative timeout support.
//!
//! Provides a `CancelToken` (an `Arc<AtomicBool>`) that can be checked at
//! yield points throughout the solver to abort long-running computations.
//!
//! The token is designed to be shared across threads: the solver checks it
//! periodically, and an external timer or user thread sets it to cancel.
//!
//! # Usage
//!
//! ```rust,ignore
//! use std::time::Duration;
//! let token = CancelToken::with_timeout(Duration::from_secs(5));
//! // pass token.clone() into solver functions
//! // solver functions call token.is_cancelled() at yield points
//! ```

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

/// A cooperative cancellation token.
///
/// The solver checks `is_cancelled()` at yield points; an external thread
/// or timer calls `cancel()` to request early termination. A token is
/// cancelled when any of: its flag is set, its deadline (if any) has
/// passed, or any combined source ([`Self::either`]) is cancelled. Timeouts
/// and combination are evaluated lazily in `is_cancelled()` — no background
/// timer or watcher thread is spawned, so creating many short-lived tokens
/// (e.g. one per `solve` call) does not accumulate detached threads.
#[derive(Clone)]
pub struct CancelToken {
    inner: Arc<Inner>,
}

struct Inner {
    flag: AtomicBool,
    /// Cancel once `Instant::now() >= deadline`.
    deadline: Option<Instant>,
    /// Cancel if any source is cancelled (for [`CancelToken::either`]).
    sources: Vec<CancelToken>,
}

impl CancelToken {
    /// Create a new token that is not cancelled.
    pub fn new() -> Self {
        CancelToken {
            inner: Arc::new(Inner { flag: AtomicBool::new(false), deadline: None, sources: Vec::new() }),
        }
    }

    /// Create a token that becomes cancelled once `duration` elapses.
    ///
    /// The deadline is checked lazily in [`Self::is_cancelled`]; no thread
    /// is spawned.
    pub fn with_timeout(duration: Duration) -> Self {
        CancelToken {
            inner: Arc::new(Inner {
                flag: AtomicBool::new(false),
                deadline: Instant::now().checked_add(duration),
                sources: Vec::new(),
            }),
        }
    }

    /// Create a token that is already cancelled (useful for testing).
    pub fn cancelled() -> Self {
        let t = Self::new();
        t.cancel();
        t
    }

    /// Create a token that will never be cancelled.
    pub fn none() -> Self {
        Self::new()
    }

    /// Check whether cancellation has been requested.
    #[inline]
    pub fn is_cancelled(&self) -> bool {
        if self.inner.flag.load(Ordering::Acquire) {
            return true;
        }
        if let Some(dl) = self.inner.deadline {
            if Instant::now() >= dl {
                return true;
            }
        }
        self.inner.sources.iter().any(|s| s.is_cancelled())
    }

    /// Request cancellation.
    pub fn cancel(&self) {
        self.inner.flag.store(true, Ordering::Release);
    }

    /// Combine two cancellation sources into a single token that is
    /// cancelled when **either** source is. Evaluated lazily (no watcher
    /// thread): the combined token holds clones of both sources and
    /// consults them in [`Self::is_cancelled`].
    pub fn either(a: &CancelToken, b: &CancelToken) -> Self {
        CancelToken {
            inner: Arc::new(Inner {
                flag: AtomicBool::new(false),
                deadline: None,
                sources: vec![a.clone(), b.clone()],
            }),
        }
    }
}

impl Default for CancelToken {
    fn default() -> Self { Self::new() }
}

/// Error type for cancelled operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cancelled;

impl std::fmt::Display for Cancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "operation cancelled (timeout)")
    }
}

impl std::error::Error for Cancelled {}

#[cfg(test)]
#[path = "timeout_tests.rs"]
mod tests;
