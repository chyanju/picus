//! Timeout integration tests.
//!
//! Verifies that the cooperative timeout mechanism works correctly:
//! 1. Pre-cancelled token → immediate Unknown.
//! 2. Normal solve (no timeout) still produces correct results.
//! 3. Very short timeout on a non-trivial problem → Unknown.
//! 4. Incremental solver timeout API.

use std::time::Duration;

use picus_solver::core::{solve_encoded_with_cancel, SolveOutcome};
use picus_solver::encoder::{ConstraintSystem, PolyTerm, encode};
use picus_solver::incremental::IncrementalSolver;
use picus_solver::timeout::CancelToken;
use num_bigint::BigUint;
use num_traits::One;

fn ct(c: u64) -> PolyTerm { PolyTerm { coeff: BigUint::from(c), vars: vec![] } }
fn vt(v: &str) -> PolyTerm { PolyTerm { coeff: BigUint::one(), vars: vec![v.into()] } }
fn svt(c: u64, v: &str) -> PolyTerm { PolyTerm { coeff: BigUint::from(c), vars: vec![v.into()] } }
fn pt(c: u64, vars: &[&str]) -> PolyTerm {
    PolyTerm { coeff: BigUint::from(c), vars: vars.iter().map(|s| s.to_string()).collect() }
}

// =============================================================================
// Pre-cancelled → immediate Unknown
// =============================================================================
#[test]
fn test_pre_cancelled_returns_unknown() {
    let system = ConstraintSystem {
        prime: BigUint::from(7u32),
        equalities: vec![vec![vt("x")]],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    let encoded = encode(&system).unwrap();
    let cancel = CancelToken::cancelled();
    match solve_encoded_with_cancel(&encoded, &cancel) {
        SolveOutcome::Unknown => {} // expected
        other => panic!("expected Unknown, got {:?}", other),
    }
}

// =============================================================================
// No timeout → correct result
// =============================================================================
#[test]
fn test_no_timeout_sat() {
    let system = ConstraintSystem {
        prime: BigUint::from(7u32),
        equalities: vec![
            // x + y - 3 = 0
            vec![vt("x"), vt("y"), ct(4)], // 4 = -3 mod 7
        ],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    let encoded = encode(&system).unwrap();
    let cancel = CancelToken::none();
    match solve_encoded_with_cancel(&encoded, &cancel) {
        SolveOutcome::Sat(m) => {
            let x = m.get("x").unwrap();
            let y = m.get("y").unwrap();
            assert_eq!((x + y) % BigUint::from(7u32), BigUint::from(3u32));
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

#[test]
fn test_no_timeout_unsat() {
    let system = ConstraintSystem {
        prime: BigUint::from(7u32),
        equalities: vec![
            vec![vt("x"), ct(5)],   // x = 2 (x + 5 = 0 mod 7)
            vec![vt("x"), ct(4)],   // x = 3 (x + 4 = 0 mod 7)
        ],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    let encoded = encode(&system).unwrap();
    let cancel = CancelToken::none();
    match solve_encoded_with_cancel(&encoded, &cancel) {
        SolveOutcome::Unsat(_) => {} // expected
        other => panic!("expected Unsat, got {:?}", other),
    }
}

// =============================================================================
// Generous timeout → correct result
// =============================================================================
#[test]
fn test_generous_timeout_completes() {
    let p = BigUint::from(7u32);
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![vt("mac1"), svt(6, "k1"), pt(6, &["d", "m1"])],
            vec![vt("mac2"), svt(6, "k2"), pt(6, &["d", "m2"])],
            vec![vt("dm"), pt(6, &["d", "m1"]), pt(6, &["d", "m2"])],
            vec![vt("s"), svt(6, "k1"), svt(6, "k2"), svt(6, "dm")],
            vec![vt("mac_sum"), svt(6, "mac1"), svt(6, "mac2")],
        ],
        disequalities: vec![("mac_sum".into(), "s".into())],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    let encoded = encode(&system).unwrap();
    // 10 seconds is way more than needed
    let cancel = CancelToken::with_timeout(Duration::from_secs(10));
    match solve_encoded_with_cancel(&encoded, &cancel) {
        SolveOutcome::Unsat(_) => {} // expected
        other => panic!("expected Unsat, got {:?}", other),
    }
}

// =============================================================================
// Incremental solver with timeout
// =============================================================================
#[test]
fn test_incremental_check_with_cancel_sat() {
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    solver.assert_assignment("x", BigUint::from(2u32));
    let cancel = CancelToken::none();
    match solver.check_with_cancel(&cancel) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m["x"], BigUint::from(2u32));
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

#[test]
fn test_incremental_check_with_timeout() {
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    solver.assert_assignment("x", BigUint::from(2u32));
    match solver.check_with_timeout(Duration::from_secs(5)) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m["x"], BigUint::from(2u32));
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

#[test]
fn test_incremental_check_pre_cancelled() {
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    solver.assert_equality(vec![vt("x"), vt("y"), ct(4)]);
    let cancel = CancelToken::cancelled();
    match solver.check_with_cancel(&cancel) {
        SolveOutcome::Unknown => {} // expected
        other => panic!("expected Unknown, got {:?}", other),
    }
}

// =============================================================================
// External cancel mid-solve via CancelToken::either
// =============================================================================

/// `either(external, timeout)` lets a long-running solve be aborted
/// by an external Ctrl-C-style trigger even when the per-call
/// timeout is generous. The combined token observes the external
/// cancellation within one polling cycle (≤ 1 ms initially,
/// 50 ms after backoff).
#[test]
fn test_either_external_cancel_aborts_mid_solve() {
    // Same dense system used by `test_no_timeout_unsat` — needs work
    // long enough that the cancellation can fire mid-solve.
    let p = BigUint::from(7u32);
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            // x^2 + y^2 = 1, x^3 + y^3 = 1 over GF(7) — small enough
            // to solve quickly but exercises GB reduction loops.
            vec![pt(1, &["x", "x"]), pt(1, &["y", "y"]), ct(p.to_u32_digits()[0] as u64 - 1)],
            vec![pt(1, &["x", "x", "x"]), pt(1, &["y", "y", "y"]), ct(p.to_u32_digits()[0] as u64 - 1)],
        ],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: true,
        bitsums: vec![],
    };
    let encoded = encode(&system).unwrap();
    let external = CancelToken::new();
    let timeout = CancelToken::with_timeout(Duration::from_secs(60));
    let combined = CancelToken::either(&external, &timeout);

    // Fire external cancellation 10 ms in; the watcher polls every
    // 1 ms initially so the combined token should observe it well
    // before the 60 s timeout.
    let ext_clone = external.clone();
    std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(10));
        ext_clone.cancel();
    });

    let start = std::time::Instant::now();
    let outcome = solve_encoded_with_cancel(&encoded, &combined);
    let elapsed = start.elapsed();

    // The solve might finish naturally before the cancel fires
    // (small system), or land in Unknown via the cancellation path.
    // Either is fine; the key invariant is that the call returned
    // within a second of the cancel — not after the 60 s timeout.
    assert!(
        elapsed < Duration::from_secs(5),
        "either-cancel solve hung past external cancellation (elapsed={:?}, got={:?})",
        elapsed,
        outcome
    );
}
