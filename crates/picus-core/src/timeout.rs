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
mod tests {
    use super::*;

    #[test]
    fn test_cancel_token_basic() {
        let t = CancelToken::new();
        assert!(!t.is_cancelled());
        t.cancel();
        assert!(t.is_cancelled());
    }

    #[test]
    fn test_cancel_token_clone_shares_state() {
        let t1 = CancelToken::new();
        let t2 = t1.clone();
        assert!(!t2.is_cancelled());
        t1.cancel();
        assert!(t2.is_cancelled());
    }

    #[test]
    fn test_cancel_token_timeout() {
        let t = CancelToken::with_timeout(Duration::from_millis(50));
        assert!(!t.is_cancelled());
        std::thread::sleep(Duration::from_millis(100));
        assert!(t.is_cancelled());
    }

    #[test]
    fn test_cancel_token_pre_cancelled() {
        let t = CancelToken::cancelled();
        assert!(t.is_cancelled());
    }

    #[test]
    fn either_fires_when_first_source_fires() {
        let a = CancelToken::new();
        let b = CancelToken::new();
        let c = CancelToken::either(&a, &b);
        assert!(!c.is_cancelled());
        a.cancel();
        // `either` is lazy: the combined token reflects its sources
        // synchronously in `is_cancelled`, so no wait is needed.
        assert!(c.is_cancelled(), "combined token should fire when a fires");
    }

    #[test]
    fn either_fires_when_second_source_fires() {
        let a = CancelToken::new();
        let b = CancelToken::new();
        let c = CancelToken::either(&a, &b);
        b.cancel();
        assert!(c.is_cancelled(), "combined token should fire when b fires");
    }

    #[test]
    fn either_fast_path_when_source_pre_cancelled() {
        let a = CancelToken::cancelled();
        let b = CancelToken::new();
        // No sleep — pre-cancelled source is the fast path.
        let c = CancelToken::either(&a, &b);
        assert!(c.is_cancelled());
    }

    #[test]
    fn either_with_timeout_short_circuits_on_external() {
        // Internal timeout is generous; external cancel fires almost
        // immediately. The combined token should reflect the external,
        // not wait for the timeout.
        let external = CancelToken::new();
        let timeout = CancelToken::with_timeout(Duration::from_secs(60));
        let combined = CancelToken::either(&external, &timeout);
        assert!(!combined.is_cancelled());
        external.cancel();
        std::thread::sleep(Duration::from_millis(20));
        assert!(combined.is_cancelled());
    }
}
