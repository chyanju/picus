//! Per-wire range constraints shared by every propagation lemma.
//!
//! Lemmas read and write `ctx.ranges` keyed by wire index. The DPVL
//! driver seeds the map with [`initial_ranges`] before the first
//! propagation pass; lemmas tighten entries as they fire (e.g. binary01
//! pins a wire to `{0, 1}`, basis2 propagates known bits).
//!
//! Moved out of `binary01` in phase 3 so adding a new range-aware
//! lemma in its own file does not require reaching into binary01 or
//! flipping the layering inside out.

use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;
use num_traits::{One, Zero};

/// Finite-set constraint on a wire's value.
///
/// `Bottom` is the unconstrained lattice top — no information yet
/// available. `Values(set)` is a finite enumeration of possible field
/// elements; the empty set encodes a contradictory state.
#[derive(Debug, Clone)]
pub enum RangeValue {
    /// Unconstrained.
    Bottom,
    /// Finite enumeration of the wire's possible values.
    Values(HashSet<BigUint>),
}

impl RangeValue {
    /// Tighten this range by intersecting with `new_vals`. A `Bottom`
    /// range adopts `new_vals` wholesale.
    pub fn intersect(&mut self, new_vals: HashSet<BigUint>) {
        match self {
            RangeValue::Bottom => *self = RangeValue::Values(new_vals),
            RangeValue::Values(existing) => {
                *existing = existing.intersection(&new_vals).cloned().collect();
            }
        }
    }

    /// Range pins the wire to exactly one value.
    #[must_use]
    pub fn is_singleton(&self) -> bool {
        matches!(self, RangeValue::Values(v) if v.len() == 1)
    }

    /// Range is a subset of `{0, 1}`. `Bottom` is not binary.
    #[must_use]
    pub fn is_binary(&self) -> bool {
        match self {
            RangeValue::Bottom => false,
            RangeValue::Values(v) => v.iter().all(|x| x.is_zero() || x == &BigUint::one()),
        }
    }

    /// Range is the empty set — every constraint is violated.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        matches!(self, RangeValue::Values(v) if v.is_empty())
    }

    /// Proves the wire's value is not zero in every satisfying witness.
    /// `Bottom` (unconstrained) and an empty value set both return
    /// `false`: an empty set encodes a contradictory state, where
    /// drawing further conclusions risks unsoundness if the
    /// contradiction is later resolved by other learned facts.
    #[must_use]
    pub fn excludes_zero(&self) -> bool {
        match self {
            RangeValue::Bottom => false,
            RangeValue::Values(v) => !v.is_empty() && !v.contains(&BigUint::zero()),
        }
    }
}

/// Seed `ctx.ranges` with the values forced by the IR's structural
/// pins (wire 0 = 1). Called once by the DPVL driver before the
/// propagation loop starts.
pub fn initial_ranges() -> HashMap<usize, RangeValue> {
    let mut ranges = HashMap::new();
    ranges.insert(
        0,
        RangeValue::Values([BigUint::from(1u32)].into_iter().collect()),
    );
    ranges
}
