//! Shared brancher for model construction and split-GB search.
//!
//! Lazily produces `(var_idx, value)` candidates for backtracking search.
//! Used by both `model.rs` (single-GB findZero) and `split_gb.rs`
//! (split-GB splitZeroExtend).

use crate::ff::field::PrimeField;
use crate::ff::field::FieldElem;

/// Brancher: lazily produces (var_idx, value) candidates.
///
/// Two modes:
/// - `Roots`: pre-computed root list (from univariate factoring or min-poly).
/// - `RoundRobin`: lazily generates (var, val) from an index counter.
pub enum Brancher {
    /// Pre-computed root list: iterate from back via `pop()`.
    Roots(Vec<(usize, FieldElem)>),
    /// Round-robin: lazily generates (var, val) from index counter.
    RoundRobin {
        unassigned: Vec<usize>,
        idx: u64,
        total: u64,
        /// True iff `total` covers every (var, value) pair in F_p^n.
        /// On large primes `per_var = u64::MAX`, which means brancher
        /// exhaustion is NOT a proof of UNSAT.
        exhaustive: bool,
    },
}

impl Brancher {
    pub fn next(&mut self, field: &PrimeField) -> Option<(usize, FieldElem)> {
        match self {
            Brancher::Roots(v) => v.pop(),
            Brancher::RoundRobin { unassigned, idx, total, .. } => {
                if *idx >= *total || unassigned.is_empty() {
                    return None;
                }
                let which_var = (*idx as usize) % unassigned.len();
                let which_val = *idx / (unassigned.len() as u64);
                *idx += 1;
                let val_bi = num_bigint::BigUint::from(which_val);
                Some((unassigned[which_var], field.from_biguint(&val_bi)))
            }
        }
    }

    /// Whether exhausting this brancher constitutes a proof that no
    /// extension exists.  `Roots` is always exhaustive (we computed
    /// every root over F_p); `RoundRobin` is exhaustive only when the
    /// per-variable cap covers F_p (i.e. small primes).
    pub fn is_exhaustive(&self) -> bool {
        match self {
            Brancher::Roots(_) => true,
            Brancher::RoundRobin { exhaustive, .. } => *exhaustive,
        }
    }
}
