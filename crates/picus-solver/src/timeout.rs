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
}
