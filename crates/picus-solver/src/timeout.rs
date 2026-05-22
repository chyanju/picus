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
use std::time::Duration;

/// A cooperative cancellation token.
///
/// Internally wraps an `Arc<AtomicBool>`.  The solver checks `is_cancelled()`
/// at yield points; an external thread or timer calls `cancel()` to request
/// early termination.
#[derive(Clone)]
pub struct CancelToken {
    flag: Arc<AtomicBool>,
}

impl CancelToken {
    /// Create a new token that is not cancelled.
    pub fn new() -> Self {
        CancelToken { flag: Arc::new(AtomicBool::new(false)) }
    }

    /// Create a token that will be cancelled after `duration`.
    ///
    /// Spawns a background thread that sleeps for `duration` then sets the
    /// flag.  The thread is detached and will terminate when the `Arc` is
    /// dropped (though the flag may be set after the solver is done — this
    /// is harmless).
    pub fn with_timeout(duration: Duration) -> Self {
        let token = Self::new();
        let flag = token.flag.clone();
        std::thread::spawn(move || {
            std::thread::sleep(duration);
            flag.store(true, Ordering::Release);
        });
        token
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
        self.flag.load(Ordering::Acquire)
    }

    /// Request cancellation.
    pub fn cancel(&self) {
        self.flag.store(true, Ordering::Release);
    }

    /// Combine two cancellation sources into a single token that
    /// fires when **either** source fires.
    ///
    /// A lightweight background watcher polls both source flags with
    /// exponential backoff (1 ms → 50 ms cap). When either source
    /// fires, the watcher sets the new token's flag and exits.
    ///
    /// If both sources become unreachable (their `Arc`s drop to the
    /// watcher's clones only), the watcher exits without firing — a
    /// dangling token that simply never gets cancelled, which is the
    /// expected behaviour when nobody can request cancellation.
    pub fn either(a: &CancelToken, b: &CancelToken) -> Self {
        let combined = Self::new();
        // Fast path: if either is already cancelled, skip the thread.
        if a.is_cancelled() || b.is_cancelled() {
            combined.cancel();
            return combined;
        }
        let combined_flag = combined.flag.clone();
        let a_flag = a.flag.clone();
        let b_flag = b.flag.clone();
        std::thread::spawn(move || {
            let mut delay = Duration::from_millis(1);
            let cap = Duration::from_millis(50);
            loop {
                if a_flag.load(Ordering::Acquire) || b_flag.load(Ordering::Acquire) {
                    combined_flag.store(true, Ordering::Release);
                    return;
                }
                // Exit when both sources are unreachable from anyone
                // other than us; nobody can fire either token, so
                // there's nothing left to watch. `strong_count == 1`
                // means our clone is the only `Arc` remaining.
                if Arc::strong_count(&a_flag) == 1 && Arc::strong_count(&b_flag) == 1 {
                    return;
                }
                std::thread::sleep(delay);
                delay = (delay * 2).min(cap);
            }
        });
        combined
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
        // Allow the watcher one polling tick (≤ 1 ms initial delay + slack).
        std::thread::sleep(Duration::from_millis(20));
        assert!(c.is_cancelled(), "combined token should fire when a fires");
    }

    #[test]
    fn either_fires_when_second_source_fires() {
        let a = CancelToken::new();
        let b = CancelToken::new();
        let c = CancelToken::either(&a, &b);
        b.cancel();
        std::thread::sleep(Duration::from_millis(20));
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
