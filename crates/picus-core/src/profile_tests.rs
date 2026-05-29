use super::*;
use crate::config::ConfigGuard;

// `metric::*!` take the typed counter path and lower to a gated direct
// atomic update. Per-test gating is the thread-local gb_stats flag; each
// test uses a *distinct* SPLIT_DFS counter (no other picus-core test
// touches these), so an exact before/after delta is reliable.
fn load(c: &AtomicU64) -> u64 {
    c.load(Ordering::Relaxed)
}

#[test]
fn metric_incr_adds_one_to_typed_counter() {
    let _g = ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let before = load(&SPLIT_DFS.branches_tried);
    crate::metric::incr!(SPLIT_DFS.branches_tried);
    crate::metric::incr!(SPLIT_DFS.branches_tried);
    assert_eq!(load(&SPLIT_DFS.branches_tried) - before, 2);
}

#[test]
fn metric_add_adds_n_to_typed_counter() {
    let _g = ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let before = load(&SPLIT_DFS.nogood_subsumption_hits);
    crate::metric::add!(SPLIT_DFS.nogood_subsumption_hits, 5u64);
    assert_eq!(load(&SPLIT_DFS.nogood_subsumption_hits) - before, 5);
}

#[test]
fn metric_max_takes_running_max_not_sum() {
    let _g = ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    // Use a fresh maximum so no concurrent writer interferes (this is the
    // only test touching max_dfs_depth in this binary).
    let base = load(&SPLIT_DFS.max_dfs_depth);
    crate::metric::max!(SPLIT_DFS.max_dfs_depth, base + 100);
    assert_eq!(
        load(&SPLIT_DFS.max_dfs_depth),
        base + 100,
        "took the larger"
    );
    crate::metric::max!(SPLIT_DFS.max_dfs_depth, base + 50);
    assert_eq!(
        load(&SPLIT_DFS.max_dfs_depth),
        base + 100,
        "ignored the smaller (max, not sum)"
    );
}

#[test]
fn metric_timer_adds_elapsed_to_typed_counter() {
    let _g = ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let before = load(&SPLIT_DFS.time_in_basis_clone_ns);
    {
        crate::metric::timer!(SPLIT_DFS.time_in_basis_clone_ns);
        std::thread::sleep(Duration::from_millis(1));
    }
    assert!(
        load(&SPLIT_DFS.time_in_basis_clone_ns) > before,
        "timer must add a positive elapsed-ns on drop"
    );
}

#[test]
fn metric_with_flag_off_is_a_noop() {
    // No ConfigGuard ⇒ gb_stats off on this thread. points_returned is
    // touched by no other picus-core test, so the delta must be exactly 0.
    let before = load(&SPLIT_DFS.points_returned);
    crate::metric::incr!(SPLIT_DFS.points_returned);
    {
        crate::metric::timer!(SPLIT_DFS.time_in_split_gb_extend_ns);
        std::thread::sleep(Duration::from_millis(1));
    }
    assert_eq!(
        load(&SPLIT_DFS.points_returned),
        before,
        "flag off ⇒ no event"
    );
}
