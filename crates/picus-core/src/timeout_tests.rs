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
