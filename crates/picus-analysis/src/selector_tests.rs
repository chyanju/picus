//! Spec-driven tests for the selector module.
//!
//! Doc spec (verbatim from `selector.rs`):
//!   * `SelectorKind::First`   — smallest wire index in the pool, NOT
//!     `iter().next()` (HashSet order is nondeterministic, would be
//!     irreproducible). `min()` over the pool.
//!   * `SelectorKind::Counter` — highest `connectivity + weight`,
//!     ties broken by smallest wire index. Determinism follows from
//!     `(c+w, Reverse(sig))` being unique per signal.
//!   * `feedback(Skip)` on a Counter selector decrements that signal's
//!     weight by 1; `feedback(Skip)` on a First selector is a no-op
//!     (and Counter ignores `Verified` per the `let SolverFeedback::Skip`
//!     guard).
//!   * `select` on an empty pool returns `None`.
//!   * `FromStr` for `SelectorKind` accepts only "first" and "counter"
//!     (unknown ⇒ Err).

use super::*;
use std::collections::{HashMap, HashSet};

fn pool(items: &[usize]) -> HashSet<usize> {
    items.iter().copied().collect()
}

fn conn(pairs: &[(usize, usize)]) -> HashMap<usize, usize> {
    pairs.iter().copied().collect()
}

// ---------------------------------------------------------------------------
// SelectorKind::from_str
// ---------------------------------------------------------------------------

#[test]
fn prop_selector_kind_from_str_known() {
    assert_eq!("first".parse::<SelectorKind>().unwrap(), SelectorKind::First);
    assert_eq!(
        "counter".parse::<SelectorKind>().unwrap(),
        SelectorKind::Counter
    );
}

#[test]
fn prop_selector_kind_from_str_unknown_errors() {
    assert!("bogus".parse::<SelectorKind>().is_err());
    assert!("".parse::<SelectorKind>().is_err());
    // Spec only matches exact lowercase strings — uppercase is unknown.
    assert!("First".parse::<SelectorKind>().is_err());
    assert!("COUNTER".parse::<SelectorKind>().is_err());
}

// ---------------------------------------------------------------------------
// select on empty pool
// ---------------------------------------------------------------------------

#[test]
fn prop_select_empty_pool_first_is_none() {
    let mut s = SelectorState::new(SelectorKind::First, HashMap::new());
    assert_eq!(s.select(&HashSet::new()), None);
}

#[test]
fn prop_select_empty_pool_counter_is_none() {
    let mut s = SelectorState::new(SelectorKind::Counter, HashMap::new());
    assert_eq!(s.select(&HashSet::new()), None);
}

// ---------------------------------------------------------------------------
// First selector: smallest index
// ---------------------------------------------------------------------------

/// `First` picks the smallest signal index, regardless of insertion order.
#[test]
fn prop_first_selects_smallest_index() {
    let mut s = SelectorState::new(SelectorKind::First, HashMap::new());
    let p = pool(&[5, 2, 9, 7, 3]);
    assert_eq!(s.select(&p), Some(2));
}

/// `First` is reproducible across distinct equal-content HashSets:
/// repeated calls return the same min regardless of insertion order
/// (the doc explicitly motivates `min()` for this).
#[test]
fn prop_first_is_reproducible() {
    let mut s1 = SelectorState::new(SelectorKind::First, HashMap::new());
    let mut s2 = SelectorState::new(SelectorKind::First, HashMap::new());
    let mut p1 = HashSet::new();
    p1.insert(7);
    p1.insert(3);
    p1.insert(11);
    let mut p2 = HashSet::new();
    p2.insert(11);
    p2.insert(3);
    p2.insert(7);
    assert_eq!(s1.select(&p1), s2.select(&p2));
    assert_eq!(s1.select(&p1), Some(3));
}

/// Single-element pool — returns the unique element.
#[test]
fn prop_first_single_element() {
    let mut s = SelectorState::new(SelectorKind::First, HashMap::new());
    assert_eq!(s.select(&pool(&[42])), Some(42));
}

// ---------------------------------------------------------------------------
// Counter selector: highest connectivity+weight, smallest index on tie
// ---------------------------------------------------------------------------

/// `Counter` picks the wire with the highest connectivity when weights
/// are all zero.
#[test]
fn prop_counter_prefers_high_connectivity() {
    let mut s = SelectorState::new(
        SelectorKind::Counter,
        conn(&[(1, 1), (2, 5), (3, 2)]),
    );
    assert_eq!(s.select(&pool(&[1, 2, 3])), Some(2));
}

/// `Counter` falls back to connectivity = 0 for wires not in the map.
#[test]
fn prop_counter_missing_connectivity_treated_as_zero() {
    let mut s = SelectorState::new(SelectorKind::Counter, conn(&[(7, 4)]));
    // Wires 1 and 2 have connectivity 0; wire 7 has 4 ⇒ picks 7.
    assert_eq!(s.select(&pool(&[1, 2, 7])), Some(7));
}

/// Counter tie-break rule: equal (connectivity + weight) ⇒ smallest index.
/// This is the spec ("ties broken by smallest wire index") and the only
/// reason the implementation folds the index into the key.
#[test]
fn prop_counter_tie_broken_by_smallest_index() {
    let mut s = SelectorState::new(
        SelectorKind::Counter,
        conn(&[(1, 3), (5, 3), (9, 3)]),
    );
    assert_eq!(s.select(&pool(&[1, 5, 9])), Some(1));
}

/// Counter is reproducible: repeated calls with the same state and an
/// equal-content pool yield the same pick.
#[test]
fn prop_counter_is_reproducible_across_pools() {
    let c = conn(&[(1, 2), (2, 2), (3, 2)]);
    let mut s1 = SelectorState::new(SelectorKind::Counter, c.clone());
    let mut s2 = SelectorState::new(SelectorKind::Counter, c);
    let p1 = pool(&[1, 2, 3]);
    let p2 = pool(&[3, 2, 1]); // distinct insertion order
    assert_eq!(s1.select(&p1), s2.select(&p2));
    // All connectivity equal ⇒ smallest index wins ⇒ 1.
    assert_eq!(s1.select(&p1), Some(1));
}

/// Single-element pool — returns the unique element regardless of map.
#[test]
fn prop_counter_single_element() {
    let mut s = SelectorState::new(SelectorKind::Counter, HashMap::new());
    assert_eq!(s.select(&pool(&[42])), Some(42));
}

// ---------------------------------------------------------------------------
// feedback semantics
// ---------------------------------------------------------------------------

/// `feedback(Skip)` on Counter decrements the signal's weight by 1.
/// After enough skips, a high-connectivity wire is overtaken by a
/// lower-connectivity one with neutral weight.
#[test]
fn prop_counter_skip_decrements_weight() {
    let mut s = SelectorState::new(
        SelectorKind::Counter,
        conn(&[(1, 5), (2, 3)]),
    );
    // Initially wire 1 (conn=5) beats wire 2 (conn=3).
    assert_eq!(s.select(&pool(&[1, 2])), Some(1));
    // Three skips push wire 1's effective score to 5-3=2 < 3.
    s.feedback(1, SolverFeedback::Skip);
    s.feedback(1, SolverFeedback::Skip);
    s.feedback(1, SolverFeedback::Skip);
    assert_eq!(s.select(&pool(&[1, 2])), Some(2));
}

/// A single Skip is enough to overtake when the gap is exactly 1.
#[test]
fn prop_counter_single_skip_can_flip_pick() {
    let mut s = SelectorState::new(
        SelectorKind::Counter,
        conn(&[(1, 4), (2, 3)]),
    );
    assert_eq!(s.select(&pool(&[1, 2])), Some(1));
    s.feedback(1, SolverFeedback::Skip);
    // Now scores are (4-1)=3 and 3 — tie ⇒ smallest index ⇒ 1.
    assert_eq!(s.select(&pool(&[1, 2])), Some(1));
    s.feedback(1, SolverFeedback::Skip);
    // Now (4-2)=2 < 3 ⇒ wire 2 wins.
    assert_eq!(s.select(&pool(&[1, 2])), Some(2));
}

/// `feedback(Verified)` on Counter does NOT mutate weights — the guard
/// in `feedback` matches only `Skip`.
#[test]
fn prop_counter_verified_does_not_change_weight() {
    let mut s = SelectorState::new(
        SelectorKind::Counter,
        conn(&[(1, 4), (2, 3)]),
    );
    s.feedback(1, SolverFeedback::Verified);
    s.feedback(1, SolverFeedback::Verified);
    s.feedback(1, SolverFeedback::Verified);
    // Weights still empty ⇒ pick driven by connectivity alone.
    assert_eq!(s.select(&pool(&[1, 2])), Some(1));
    assert!(
        s.weights.is_empty(),
        "Verified must not create or mutate any weight entry"
    );
}

/// `feedback(Skip)` on a First selector is a no-op — the guard
/// `self.kind == SelectorKind::Counter` excludes it.
#[test]
fn prop_first_feedback_is_noop() {
    let mut s = SelectorState::new(SelectorKind::First, HashMap::new());
    s.feedback(1, SolverFeedback::Skip);
    s.feedback(2, SolverFeedback::Skip);
    s.feedback(5, SolverFeedback::Verified);
    // Pick is still purely by min index — feedback didn't change behaviour.
    assert_eq!(s.select(&pool(&[1, 2, 5])), Some(1));
    // And weights stayed unset.
    assert!(s.weights.is_empty(), "First selector should not record weights");
}

/// Pool can skip a wire's pick: if `select` returned `sid` but the
/// caller removes it from `uspool` and calls again, the next-best
/// candidate is returned. This is the DPVL inner-loop pattern.
#[test]
fn prop_counter_returns_next_after_pool_removal() {
    let mut s = SelectorState::new(
        SelectorKind::Counter,
        conn(&[(1, 5), (2, 3), (3, 1)]),
    );
    let mut p = pool(&[1, 2, 3]);
    let first = s.select(&p).unwrap();
    assert_eq!(first, 1);
    p.remove(&first);
    let second = s.select(&p).unwrap();
    assert_eq!(second, 2);
    p.remove(&second);
    assert_eq!(s.select(&p), Some(3));
    p.remove(&3);
    assert_eq!(s.select(&p), None);
}
