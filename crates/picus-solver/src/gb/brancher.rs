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
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;

    fn field7() -> PrimeField {
        PrimeField::new(BigUint::from(7u32))
    }

    fn pr() -> FfPolyRing {
        FfPolyRing::new(field7(), vec!["x".into(), "y".into()])
    }

    // ────────── Brancher::Roots ──────────

    #[test]
    fn roots_brancher_pops_lifo_and_exhausts() {
        let f = field7();
        let mut b = Brancher::Roots(vec![(0, f.from_int(2)), (0, f.from_int(3))]);
        // pop pulls from the back (LIFO).
        let (v, val) = b.next(&f).expect("first");
        assert_eq!(v, 0);
        assert_eq!(f.to_biguint(&val), BigUint::from(3u32));
        let (v, val) = b.next(&f).expect("second");
        assert_eq!(v, 0);
        assert_eq!(f.to_biguint(&val), BigUint::from(2u32));
        assert!(b.next(&f).is_none());
    }

    #[test]
    fn roots_brancher_is_always_exhaustive() {
        let b = Brancher::Roots(vec![]);
        assert!(b.is_exhaustive());
        let f = field7();
        let b = Brancher::Roots(vec![(0, f.from_int(0))]);
        assert!(b.is_exhaustive());
    }

    // ────────── Brancher::round_robin ──────────

    #[test]
    fn round_robin_small_prime_is_exhaustive() {
        let b = Brancher::round_robin(vec![0, 1], &BigUint::from(7u32));
        assert!(b.is_exhaustive());
    }

    #[test]
    fn round_robin_large_prime_is_non_exhaustive() {
        // BN128 prime (~254 bits) → non-exhaustive (per-var cap = u64::MAX).
        let large = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        ).unwrap();
        let b = Brancher::round_robin(vec![0], &large);
        assert!(!b.is_exhaustive());
    }

    #[test]
    fn round_robin_enumerates_variable_first_then_value() {
        let f = field7();
        let mut b = Brancher::round_robin(vec![0, 1], &BigUint::from(7u32));
        // First two candidates: (0, 0), (1, 0) — same value, alternating var.
        let (v, val) = b.next(&f).expect("0");
        assert_eq!(v, 0);
        assert_eq!(f.to_biguint(&val), BigUint::from(0u32));
        let (v, val) = b.next(&f).expect("1");
        assert_eq!(v, 1);
        assert_eq!(f.to_biguint(&val), BigUint::from(0u32));
        // Then (0, 1), (1, 1).
        let (v, val) = b.next(&f).expect("2");
        assert_eq!(v, 0);
        assert_eq!(f.to_biguint(&val), BigUint::from(1u32));
    }

    #[test]
    fn round_robin_exhausts_after_total() {
        // GF(7) × 1 var → 7 candidates total then None.
        let f = field7();
        let mut b = Brancher::round_robin(vec![0], &BigUint::from(7u32));
        for _ in 0..7 {
            assert!(b.next(&f).is_some());
        }
        assert!(b.next(&f).is_none());
    }

    #[test]
    fn round_robin_empty_unassigned_yields_none() {
        let f = field7();
        let mut b = Brancher::round_robin(vec![], &BigUint::from(7u32));
        assert!(b.next(&f).is_none());
    }

    // ────────── univariate_coeffs ──────────

    #[test]
    fn univariate_coeffs_pure_univariate() {
        // p(x) = 2x^2 + 3x + 5 over GF(7) → [5, 3, 2]
        let pr = pr();
        let f = pr.field();
        let xx = pr.mul(pr.var(0), pr.var(0));
        let coeffs_poly = pr.add(
            pr.add(pr.scale(f.from_int(2), xx), pr.scale(f.from_int(3), pr.var(0))),
            pr.constant(f.from_int(5)),
        );
        let cs = univariate_coeffs(&pr, &coeffs_poly, 0).expect("univariate");
        assert_eq!(cs.len(), 3);
        assert_eq!(f.to_biguint(&cs[0]), BigUint::from(5u32));
        assert_eq!(f.to_biguint(&cs[1]), BigUint::from(3u32));
        assert_eq!(f.to_biguint(&cs[2]), BigUint::from(2u32));
    }

    #[test]
    fn univariate_coeffs_returns_none_when_other_var_appears() {
        let pr = pr();
        // p = x + y → not univariate in x or y alone.
        let p = pr.add(pr.var(0), pr.var(1));
        assert!(univariate_coeffs(&pr, &p, 0).is_none());
        assert!(univariate_coeffs(&pr, &p, 1).is_none());
    }

    #[test]
    fn univariate_coeffs_constant_poly_in_variable() {
        // p = 5 viewed in x: returns Some([5]) (constant treated as deg-0
        // poly with no x dependence).
        let pr = pr();
        let f = pr.field();
        let p = pr.constant(f.from_int(5));
        let cs = univariate_coeffs(&pr, &p, 0).expect("constant is univariate");
        assert_eq!(cs.len(), 1);
        assert_eq!(f.to_biguint(&cs[0]), BigUint::from(5u32));
    }
}
