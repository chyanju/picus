//! Tests for `RangeValue` lattice operations + `initial_ranges` seed.
//!
//! Spec invariants (from doc comments in `range.rs`):
//!   - `Bottom` = unconstrained top; `Values(set)` = finite enumeration;
//!     empty set encodes contradiction.
//!   - `intersect`: Bottom adopts new set wholesale; Values intersects.
//!   - `is_singleton`: exactly one element.
//!   - `is_binary`: NON-EMPTY subset of {0, 1}. Bottom and empty are NOT
//!     binary (so a consumer can't admit a "bit" on vacuously-true range).
//!   - `is_empty`: empty set (NOT Bottom).
//!   - `excludes_zero`: Bottom = false; empty = false (contradictory
//!     state, drawing conclusions is unsafe); otherwise checks no zero.
//!   - `initial_ranges`: seeds wire 0 -> {1}. Wire 0 = R1CS one-wire.

use crate::propagation::range::{initial_ranges, RangeValue};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::collections::HashSet;

fn vals(items: &[u32]) -> HashSet<BigUint> {
    items.iter().map(|&v| BigUint::from(v)).collect()
}

// ───── is_singleton ──────────────────────────────────────────────

#[test]
fn prop_is_singleton_bottom_is_false() {
    assert!(!RangeValue::Bottom.is_singleton());
}

#[test]
fn prop_is_singleton_empty_is_false() {
    assert!(!RangeValue::Values(HashSet::new()).is_singleton());
}

#[test]
fn prop_is_singleton_one_element_is_true() {
    assert!(RangeValue::Values(vals(&[5])).is_singleton());
}

#[test]
fn prop_is_singleton_two_elements_is_false() {
    assert!(!RangeValue::Values(vals(&[0, 1])).is_singleton());
}

// ───── is_binary ─────────────────────────────────────────────────

#[test]
fn prop_is_binary_bottom_is_false() {
    // Doc: "Bottom (unconstrained) ... not binary"
    assert!(!RangeValue::Bottom.is_binary());
}

#[test]
fn prop_is_binary_empty_is_false() {
    // Doc: "empty set (contradictory) ... not binary" — soundness
    assert!(!RangeValue::Values(HashSet::new()).is_binary());
}

#[test]
fn prop_is_binary_zero_one_is_true() {
    assert!(RangeValue::Values(vals(&[0, 1])).is_binary());
}

#[test]
fn prop_is_binary_singleton_zero_is_true() {
    assert!(RangeValue::Values(vals(&[0])).is_binary());
}

#[test]
fn prop_is_binary_singleton_one_is_true() {
    assert!(RangeValue::Values(vals(&[1])).is_binary());
}

#[test]
fn prop_is_binary_contains_two_is_false() {
    assert!(!RangeValue::Values(vals(&[0, 1, 2])).is_binary());
}

#[test]
fn prop_is_binary_singleton_two_is_false() {
    assert!(!RangeValue::Values(vals(&[2])).is_binary());
}

// ───── is_empty ──────────────────────────────────────────────────

#[test]
fn prop_is_empty_bottom_is_false() {
    // Doc: empty means Values({}) only, not Bottom.
    assert!(!RangeValue::Bottom.is_empty());
}

#[test]
fn prop_is_empty_empty_set_is_true() {
    assert!(RangeValue::Values(HashSet::new()).is_empty());
}

#[test]
fn prop_is_empty_nonempty_is_false() {
    assert!(!RangeValue::Values(vals(&[0])).is_empty());
}

// ───── excludes_zero ─────────────────────────────────────────────

#[test]
fn prop_excludes_zero_bottom_is_false() {
    // Doc: "Bottom (unconstrained) ... return false"
    assert!(!RangeValue::Bottom.excludes_zero());
}

#[test]
fn prop_excludes_zero_empty_is_false() {
    // Soundness: empty set is contradictory; drawing further conclusions
    // is unsafe.
    assert!(!RangeValue::Values(HashSet::new()).excludes_zero());
}

#[test]
fn prop_excludes_zero_contains_zero_is_false() {
    assert!(!RangeValue::Values(vals(&[0, 5])).excludes_zero());
}

#[test]
fn prop_excludes_zero_no_zero_is_true() {
    assert!(RangeValue::Values(vals(&[1, 5])).excludes_zero());
}

#[test]
fn prop_excludes_zero_singleton_nonzero_is_true() {
    assert!(RangeValue::Values(vals(&[7])).excludes_zero());
}

// ───── intersect ─────────────────────────────────────────────────

#[test]
fn prop_intersect_bottom_adopts_wholesale() {
    let mut r = RangeValue::Bottom;
    r.intersect(vals(&[1, 2, 3]));
    match r {
        RangeValue::Values(v) => {
            assert_eq!(v, vals(&[1, 2, 3]));
        }
        RangeValue::Bottom => panic!("Bottom must transition to Values"),
    }
}

#[test]
fn prop_intersect_values_intersects() {
    let mut r = RangeValue::Values(vals(&[0, 1, 2]));
    r.intersect(vals(&[1, 2, 3]));
    match r {
        RangeValue::Values(v) => {
            assert_eq!(v, vals(&[1, 2]));
        }
        RangeValue::Bottom => panic!("must stay Values"),
    }
}

#[test]
fn prop_intersect_disjoint_yields_empty() {
    let mut r = RangeValue::Values(vals(&[0, 1]));
    r.intersect(vals(&[2, 3]));
    assert!(r.is_empty(), "disjoint intersect must be empty");
}

#[test]
fn prop_intersect_idempotent() {
    let mut r = RangeValue::Values(vals(&[0, 1]));
    r.intersect(vals(&[0, 1]));
    match r {
        RangeValue::Values(v) => assert_eq!(v, vals(&[0, 1])),
        RangeValue::Bottom => panic!("must stay Values"),
    }
}

#[test]
fn prop_intersect_with_empty_yields_empty() {
    let mut r = RangeValue::Values(vals(&[0, 1, 2]));
    r.intersect(HashSet::new());
    assert!(r.is_empty(), "intersect with empty must collapse to empty");
}

// ───── initial_ranges ────────────────────────────────────────────

#[test]
fn prop_initial_ranges_pins_wire0_to_one() {
    let r = initial_ranges();
    let v = r.get(&0).expect("wire 0 must be seeded");
    assert!(v.is_singleton(), "wire 0 must be a singleton");
    assert!(v.is_binary(), "{{1}} ⊆ {{0,1}} so it must be binary");
    assert!(v.excludes_zero(), "wire 0 = 1 ≠ 0");
    match v {
        RangeValue::Values(set) => {
            assert!(set.contains(&BigUint::one()));
            assert!(!set.contains(&BigUint::zero()));
        }
        RangeValue::Bottom => panic!("wire 0 must be Values"),
    }
}

#[test]
fn prop_initial_ranges_only_seeds_wire_zero() {
    let r = initial_ranges();
    // Only wire 0 is structurally pinned by the IR.
    assert_eq!(r.len(), 1, "initial_ranges seeds exactly wire 0");
}
