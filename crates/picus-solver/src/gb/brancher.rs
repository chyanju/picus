//! Shared brancher for model construction and split-GB search.
//!
//! Lazily produces `(var_idx, value)` candidates for backtracking search.
//! Used by both `model.rs` (single-GB findZero) and `split_gb.rs`
//! (split-GB splitZeroExtend).

use crate::ff::field::{FieldElem, PrimeField};
use crate::poly::{FfPolyRing, Poly};
use num_bigint::BigUint;
use std::collections::HashMap;

/// Brancher: lazily produces (var_idx, value) candidates.
///
/// Three modes:
/// - `Roots`: pre-computed root list (from univariate factoring or min-poly).
/// - `RoundRobin`: lazily generates (var, val) from an index counter.
/// - `ProvedUnsat`: empty + exhaustive; signals a sub-ideal with no F_p
///   solution (e.g. FGLM Lex-walk + triangular DFS exhausted every
///   branch). Distinct from `Roots(Vec::new())` only in intent and in
///   diagnostics; the search loop treats it identically (next ⇒ None,
///   is_exhaustive ⇒ true ⇒ backtrack contributes to Unsat verdict).
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
    /// Sound UNSAT for the current sub-ideal under F_p; produced by
    /// FGLM-to-Lex + triangular-DFS exhaustion on a zero-dimensional
    /// ideal. Always exhaustive; `next` returns `None` immediately.
    ProvedUnsat,
}

impl Brancher {
    /// Round-robin brancher over the `unassigned` variables. `exhaustive`
    /// (set iff `prime` fits in 16 bits) is the load-bearing predicate
    /// deciding whether brancher exhaustion proves UNSAT — single source
    /// for both model construction (`gb::model`) and the split-GB DFS
    /// (`split_gb::branching`). Large primes set `per_var = u64::MAX` and
    /// `exhaustive = false`, so termination relies on the cancel token.
    pub(crate) fn round_robin(unassigned: Vec<usize>, prime: &BigUint) -> Brancher {
        let exhaustive = prime.bits() <= 16;
        let per_var: u64 = if exhaustive {
            prime.iter_u64_digits().next().unwrap_or(2).max(2)
        } else {
            u64::MAX
        };
        let total = per_var.saturating_mul(unassigned.len() as u64);
        Brancher::RoundRobin { unassigned, idx: 0, total, exhaustive }
    }

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
            Brancher::ProvedUnsat => None,
        }
    }

    /// Whether exhausting this brancher constitutes a proof that no
    /// extension exists.  `Roots` is always exhaustive (we computed
    /// every root over F_p); `RoundRobin` is exhaustive only when the
    /// per-variable cap covers F_p (i.e. small primes); `ProvedUnsat`
    /// is exhaustive by construction.
    pub fn is_exhaustive(&self) -> bool {
        match self {
            Brancher::Roots(_) => true,
            Brancher::RoundRobin { exhaustive, .. } => *exhaustive,
            Brancher::ProvedUnsat => true,
        }
    }
}

/// Coefficient vector (lowest degree first) of `p` viewed as a univariate
/// polynomial in `var_idx`; `None` if any other variable appears. Shared
/// by model construction (`gb::model`) and the split-GB DFS
/// (`split_gb::branching`) so the two stay identical.
pub(crate) fn univariate_coeffs(
    poly_ring: &FfPolyRing,
    p: &Poly,
    var_idx: usize,
) -> Option<Vec<FieldElem>> {
    let ring = &poly_ring.ring;
    let fp = &poly_ring.field();
    let appearing = ring.appearing_indeterminates(p);
    for (v, _) in &appearing {
        if *v != var_idx {
            return None;
        }
    }
    let mut coeffs: HashMap<usize, FieldElem> = HashMap::new();
    let mut max_deg = 0usize;
    for (c, m) in ring.terms(p) {
        let d = ring.exponent_at(&m, var_idx);
        if d > max_deg {
            max_deg = d;
        }
        let entry = coeffs.entry(d).or_insert_with(|| fp.zero());
        fp.add_assign(entry, fp.clone_el(c));
    }
    let mut out = Vec::with_capacity(max_deg + 1);
    for d in 0..=max_deg {
        out.push(coeffs.remove(&d).unwrap_or_else(|| fp.zero()));
    }
    Some(out)
}

#[cfg(test)]
#[path = "brancher_tests.rs"]
mod tests;
