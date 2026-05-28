//! Split Groebner Basis solver.
//!
//! Implements the algorithm from "Split Groebner Bases for Satisfiability
//! Modulo Finite Fields" (Ozdemir et al., CAV 2023).
//!
//! Instead of one big GB over all polynomials, maintain `k` GBs over
//! disjoint subsets, sharing only admissible polynomials between them.
//! The default split is two ideals:
//!
//!   - **ideal 0** ("linear"):    accepts all polynomials with `deg <= 1`.
//!   - **ideal 1** ("nonlinear"): accepts polynomials with `deg <= 1` and
//!                                `numTerms <= 2`.
//!
//! Submodules:
//!
//! * [`fixpoint`] — [`split_gb_cancel`] (from-scratch driver) and
//!   [`split_gb_extend_cancel`] (incremental driver). Shared body in
//!   `run_fixpoint`.
//! * [`search`] — [`split_zero_extend_cancel`], the stack-based DFS that
//!   extends a split GB to a complete model.
//! * [`branching`] — [`apply_rule`] and `apply_rule_multi`, the
//!   univariate / zero-dim / round-robin branching heuristics.
//!
//! This module hosts the shared types, the public entry points
//! ([`split_find_zero`], [`split_find_zero_cancel`]), and the trivial
//! helpers (`admit`, `total_degree`, `num_terms`).

mod branching;
mod fixpoint;
mod search;

pub use branching::apply_rule;
pub use fixpoint::{split_gb, split_gb_cancel, split_gb_cancel_traced, TracedSplitGb};
pub(crate) use fixpoint::split_gb_extend_cancel;
pub use search::{split_zero_extend, split_zero_extend_cancel};

use crate::frontend::bitprop::BitProp;
use crate::ff::field::FieldElem;
use crate::gb::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::{CancelToken, Cancelled};

/// A split Groebner basis: one [`Ideal`] per partition.
pub type SplitGb<'r> = Vec<Ideal<'r>>;

/// A partial assignment of variable indices to field values.
pub type PartialPoint = Vec<Option<FieldElem>>;

/// Result of [`split_zero_extend`].
pub enum ZeroExtendResult {
    /// A complete assignment was found.
    Point(Vec<FieldElem>),
    /// A conflict polynomial: not in `bases[0]` but evaluates to non-zero
    /// under the partial assignment.
    Conflict(Poly),
    /// No common zeros exist that extend the current partial assignment.
    /// `exhaustive = true` means the search proved UNSAT; `false` means
    /// the search exhausted a non-exhaustive round-robin brancher on a
    /// large prime and the result is inconclusive (`Unknown`), not UNSAT.
    NoZero { exhaustive: bool },
    /// Computation was cancelled (timeout).
    Cancelled,
}

/// Outcome of [`split_find_zero`] / [`split_find_zero_cancel`].
///
/// `Unknown` means the search exhausted its bounded round-robin cap on
/// a large prime field; the formula may still be SAT outside the range
/// tried. Callers must NOT treat `Unknown` as UNSAT.
#[derive(Debug)]
pub enum SplitFindZeroOutcome {
    Sat(Vec<FieldElem>),
    Unsat,
    Unknown,
}

/// Default split-admission predicate.
///
/// `admit(i, p) = deg(p) <= 1 && (i == 0 || numTerms(p) <= 2)`
///
///   - basis 0 (linear):    admits `p` iff `deg(p) <= 1`.
///   - basis 1 (nonlinear): admits `p` iff `deg(p) <= 1` and
///                          `numTerms(p) <= 2`.
///   - any other index: never admit.
pub fn admit(_pr: &FfPolyRing, idx: usize, p: &Poly) -> bool {
    if total_degree(p) > 1 { return false; }
    match idx {
        0 => true,
        1 => num_terms(p) <= 2,
        _ => false,
    }
}

/// Build the default two-partition split-GB generator sets and their
/// per-generator provenance.
///
///   - basis 0 (linear):    the bitsum definition polys, then every
///                          original admitted by `admit(_, 0, _)`.
///   - basis 1 (nonlinear): all originals, in order.
///
/// The returned `(gens, provenance)` are index-parallel within each basis:
/// `provenance[b][i]` is `Some(orig_idx)` when `gens[b][i]` is original
/// input `orig_idx`, or `None` for an encoder-introduced bitsum definition
/// (which contributes no UNSAT-core dependency). Single source of the
/// partition layout shared by the conjunctive (`core::solve_split_gb_cancel`)
/// and cached (`incremental_context`) build paths; callers that don't trace
/// dependencies ignore the provenance.
pub(crate) fn build_partitions(
    poly_ring: &FfPolyRing,
    originals: &[Poly],
    bitsums: &[Poly],
) -> (Vec<Vec<Poly>>, Vec<Vec<Option<usize>>>) {
    let nl_gens: Vec<Poly> = originals.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
    let nl_prov: Vec<Option<usize>> = (0..originals.len()).map(Some).collect();

    let mut l_gens: Vec<Poly> = Vec::new();
    let mut l_prov: Vec<Option<usize>> = Vec::new();
    for p in bitsums {
        l_gens.push(poly_ring.ring.clone_el(p));
        l_prov.push(None);
    }
    for (i, p) in originals.iter().enumerate() {
        if admit(poly_ring, 0, p) {
            l_gens.push(poly_ring.ring.clone_el(p));
            l_prov.push(Some(i));
        }
    }

    (vec![l_gens, nl_gens], vec![l_prov, nl_prov])
}

/// Outcome of classifying a candidate poly against one partition during
/// the propagation fixpoint. Shared by all three fixpoint drivers
/// (`fixpoint::run_fixpoint`, `run_fixpoint_traced`,
/// `incremental_context::continue_partial`).
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub(crate) enum Propagate {
    /// `p` doesn't fit partition `j`'s degree/term shape.
    NotAdmitted,
    /// `(p, j)` already memoised as in-ideal — skip.
    MemoHit,
    /// `contains` confirmed `p ∈ I_j` — skip (now memoised).
    InBasis,
    /// `p ∉ I_j` — caller should queue `p` as a new generator of `j`.
    NewGenerator,
}

/// Classify whether candidate `p` (with precomputed `p_hash`) should be
/// queued as a new generator of partition `j`, updating `contains_memo`.
///
/// The memo records `(p_hash, j)` both when `p` is found in the basis and
/// when it is about to be added: after the next iteration's `extend`,
/// `p ∈ I_j`, so re-checking it would be wasted. This pre-record is the
/// subtle, must-stay-identical step across the three drivers, so it lives
/// here as the single source rather than being hand-copied three times.
pub(crate) fn classify_propagation(
    poly_ring: &FfPolyRing,
    basis_j: &Ideal,
    j: usize,
    p: &Poly,
    p_hash: u64,
    contains_memo: &mut std::collections::HashSet<(u64, usize)>,
    cancel: &CancelToken,
) -> Propagate {
    if !admit(poly_ring, j, p) {
        return Propagate::NotAdmitted;
    }
    let key = (p_hash, j);
    if contains_memo.contains(&key) {
        return Propagate::MemoHit;
    }
    let in_basis = basis_j.contains_with_cancel(p, cancel);
    contains_memo.insert(key);
    if in_basis {
        Propagate::InBasis
    } else {
        Propagate::NewGenerator
    }
}

/// Seed the cross-iteration containment memo with self-membership: every
/// polynomial already in partition `j`'s basis trivially satisfies
/// `contains(p, j)`. Shared by the from-scratch, traced, and incremental
/// fixpoint drivers so the memo key derivation stays defined once.
pub(crate) fn seed_self_membership(
    contains_memo: &mut std::collections::HashSet<(u64, usize)>,
    split_basis: &[Ideal<'_>],
) {
    for (j, ideal) in split_basis.iter().enumerate() {
        for p in &ideal.basis {
            contains_memo.insert((p.content_hash(), j));
        }
    }
}

/// Iteration cap for the split-GB propagation fixpoint as a function of
/// the partition count `k`. A safety bound against pathological
/// propagation loops on degenerate inputs: the cancel token also bounds
/// the loop, but this cap gives a deterministic exit independent of wall
/// time. Shared by the from-scratch, traced, and incremental propagation
/// drivers.
pub(crate) fn max_fixpoint_iters(k: usize) -> u64 {
    (k * 64).max(256) as u64
}

/// Total degree of a polynomial.
pub fn total_degree(p: &Poly) -> usize {
    p.total_degree() as usize
}

/// Number of terms in a polynomial.
pub fn num_terms(p: &Poly) -> usize {
    p.num_terms()
}

/// Triangular model construction (cvc5 `multi_roots` analogue) for the default
/// split path, gated by `config.split_triangular`. When the combined system
/// `all_gens` is zero-dimensional, decide it completely via
/// [`crate::gb::model::find_zero_cancel`] (univariate roots + back-substitution
/// over the exhaustive zero-dim branchers) instead of the brancher DFS.
///
/// Returns `Some(Sat(verified point))`, `Some(Unsat)` (a complete
/// zero-dimensional enumeration found no `GF(p)` solution), or `None` to fall
/// back to the DFS — when the system is positive-dimensional, the search was
/// inconclusive (`Unknown`), the witness failed verification, or the GB build
/// was cancelled. Sound: SAT is a verified witness; UNSAT comes only from a
/// complete zero-dimensional enumeration; every other case defers to the DFS.
fn try_split_triangular<'r>(
    poly_ring: &'r FfPolyRing,
    all_gens: &[Poly],
    cancel: &CancelToken,
) -> Option<SplitFindZeroOutcome> {
    let gens: Vec<Poly> = all_gens.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
    let ideal = Ideal::new_with_cancel(poly_ring, gens, cancel).ok()?;
    if !ideal.is_zero_dim() {
        return None; // positive-dimensional → the DFS handles it
    }
    match crate::gb::model::find_zero_cancel(poly_ring, &ideal.basis, cancel) {
        crate::gb::model::FindZeroOutcome::Sat(model) => {
            // The witness must satisfy the original combined system.
            if !crate::gb::model::verify_model(poly_ring, all_gens, &model) {
                return None;
            }
            let mut pt = Vec::with_capacity(poly_ring.n_vars());
            for name in poly_ring.var_names() {
                pt.push(poly_ring.field().from_biguint(model.get(name)?));
            }
            Some(SplitFindZeroOutcome::Sat(pt))
        }
        crate::gb::model::FindZeroOutcome::Unsat => Some(SplitFindZeroOutcome::Unsat),
        crate::gb::model::FindZeroOutcome::Unknown => None, // fall back to the DFS
    }
}

/// Encode `(orig_polys, bitsums)` into a split GB, run the propagation
/// fixpoint, then [`split_zero_extend`] to extract a model.
pub fn split_find_zero<'r>(
    poly_ring: &'r FfPolyRing,
    split_basis: SplitGb<'r>,
    bit_prop: &mut BitProp<'r>,
) -> SplitFindZeroOutcome {
    match split_find_zero_cancel(poly_ring, split_basis, bit_prop, &CancelToken::none()) {
        Ok(o) => o,
        Err(_) => SplitFindZeroOutcome::Unknown,
    }
}

/// Cancel-aware model search. Returns `Sat / Unsat / Unknown` on
/// success; `Err(Cancelled)` on timeout.
pub fn split_find_zero_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    split_basis: SplitGb<'r>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<SplitFindZeroOutcome, Cancelled> {
    let mut split_basis = split_basis;
    loop {
        if cancel.is_cancelled() { return Err(Cancelled); }

        let mut all_gens: Vec<Poly> = Vec::new();
        for b in &split_basis {
            for p in &b.basis {
                all_gens.push(poly_ring.ring.clone_el(p));
            }
        }

        // Triangular model construction (config-gated, default off): when the
        // combined system is zero-dimensional, decide it completely via
        // `gb::model::find_zero` instead of the brancher DFS below.
        if crate::config::with(|c| c.split_triangular) {
            if let Some(outcome) = try_split_triangular(poly_ring, &all_gens, cancel) {
                return Ok(outcome);
            }
        }

        let null_partial: PartialPoint = vec![None; poly_ring.n_vars()];

        let cur_bases: SplitGb<'r> = split_basis.iter()
            .map(|b| {
                let basis_clone: Vec<Poly> = b.basis.iter()
                    .map(|p| poly_ring.ring.clone_el(p))
                    .collect();
                Ideal::from_gb(poly_ring, basis_clone)
            })
            .collect();

        let result = split_zero_extend_cancel(
            poly_ring, &all_gens, cur_bases, null_partial, bit_prop, cancel,
        );
        match result {
            ZeroExtendResult::Conflict(c) => {
                let new_polys: Vec<Vec<Poly>> = split_basis.iter()
                    .map(|_| vec![poly_ring.ring.clone_el(&c)])
                    .collect();
                split_basis = split_gb_extend_cancel(
                    poly_ring, split_basis, new_polys, bit_prop, cancel,
                )?;
            }
            ZeroExtendResult::NoZero { exhaustive: true } => {
                return Ok(SplitFindZeroOutcome::Unsat);
            }
            ZeroExtendResult::NoZero { exhaustive: false } => {
                return Ok(SplitFindZeroOutcome::Unknown);
            }
            ZeroExtendResult::Cancelled => {
                return Err(Cancelled);
            }
            ZeroExtendResult::Point(pt) => return Ok(SplitFindZeroOutcome::Sat(pt)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use num_bigint::BigUint;

    fn ff(p: u32) -> PrimeField { PrimeField::new(BigUint::from(p)) }

    #[test]
    fn test_admit() {
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let lin1 = pr.var(0); // 1 term, deg 1 -> admit by both
        let lin2 = pr.add(pr.var(0), pr.var(1)); // 2 terms, deg 1
        let nonlin = pr.mul(pr.var(0), pr.var(1));
        let lin3 = pr.add(pr.add(pr.var(0), pr.var(1)), pr.one()); // 3 terms, deg 1
        assert!(admit(&pr, 0, &lin1));
        assert!(admit(&pr, 1, &lin1));
        assert!(admit(&pr, 0, &lin2));
        assert!(admit(&pr, 1, &lin2));
        assert!(!admit(&pr, 0, &nonlin));
        assert!(!admit(&pr, 1, &nonlin));
        // lin3: 3 terms, deg 1 -> basis 0 admits (deg<=1), basis 1 rejects (terms>2)
        assert!(admit(&pr, 0, &lin3));
        assert!(!admit(&pr, 1, &lin3));
    }

    #[test]
    fn test_split_gb_simple_sat() {
        // x*y - 1 = 0,  x = 2  →  y = 4 in GF(7)
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p1 = pr.sub(xy, pr.one());
        let two = pr.field().from_int(2);
        let p2 = pr.sub(pr.var(0), pr.constant(two));

        let mut bp = BitProp::new(&pr);
        let gens: Vec<Vec<Poly>> = vec![vec![pr.clone_poly(&p2)], vec![p1, p2]];
        let basis = split_gb(&pr, gens, &mut bp);
        assert!(!basis.iter().any(|b| b.is_whole_ring()));
        let pt = match split_find_zero(&pr, basis, &mut bp) {
            SplitFindZeroOutcome::Sat(pt) => pt,
            other => panic!("expected SAT, got {:?}", other),
        };
        // Check x = 2, y = 4 (or the other valid roots; should satisfy x*y=1).
        let x_val = pr.field().to_biguint(&pt[0]);
        let y_val = pr.field().to_biguint(&pt[1]);
        assert_eq!(x_val, BigUint::from(2u32));
        let prod = (x_val * y_val) % BigUint::from(7u32);
        assert_eq!(prod, BigUint::from(1u32));
    }

    #[test]
    fn test_split_gb_unsat() {
        // x = 2, x = 3 in GF(7): UNSAT
        let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
        let two = pr.field().from_int(2);
        let three = pr.field().from_int(3);
        let p1 = pr.sub(pr.var(0), pr.constant(two));
        let p2 = pr.sub(pr.var(0), pr.constant(three));
        let mut bp = BitProp::new(&pr);
        let basis = split_gb(&pr, vec![vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
                                       vec![p1, p2]], &mut bp);
        assert!(basis.iter().any(|b| b.is_whole_ring()));
    }

    #[test]
    fn test_apply_rule_round_robin_interleaves() {
        // Positive-dim ideal: empty (no constraints) over GF(5), 2 vars.
        // Should fall through to round-robin. Verify the order:
        // (x,0), (y,0), (x,1), (y,1), (x,2), (y,2), (x,3), (y,3), (x,4), (y,4).
        let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
        let gb: Ideal = Ideal::from_gb(&pr, vec![]);
        let r: PartialPoint = vec![None, None];
        let mut brancher = apply_rule(&pr, &gb, &r);
        // first 2 candidates should be (0, 0) and (1, 0): same val, different var.
        let c0 = brancher.next(&pr.field()).unwrap();
        assert_eq!(c0.0, 0);
        assert_eq!(pr.field().to_biguint(&c0.1), num_bigint::BigUint::from(0u32));
        let c1 = brancher.next(&pr.field()).unwrap();
        assert_eq!(c1.0, 1);
        assert_eq!(pr.field().to_biguint(&c1.1), num_bigint::BigUint::from(0u32));
        // third candidate: var 0 again, val 1.
        let c2 = brancher.next(&pr.field()).unwrap();
        assert_eq!(c2.0, 0);
        assert_eq!(pr.field().to_biguint(&c2.1), num_bigint::BigUint::from(1u32));
    }

    #[test]
    fn test_apply_rule_univariate() {
        // GB has y^2 - 4 = 0; should enumerate roots of y over GF(7) (i.e., 2 and 5).
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let four = pr.field().from_int(4);
        let y_sq = pr.mul(pr.var(1), pr.var(1));
        let p = pr.sub(y_sq, pr.constant(four));
        let gb = Ideal::new(&pr, vec![p]);
        let r: PartialPoint = vec![None, None];
        let mut brancher = apply_rule(&pr, &gb, &r);
        let mut cands = Vec::new();
        while let Some(c) = brancher.next(&pr.field()) {
            cands.push(c);
        }
        assert!(cands.iter().all(|(v, _)| *v == 1));
        let vals: Vec<num_bigint::BigUint> =
            cands.iter().map(|(_, v)| pr.field().to_biguint(v)).collect();
        assert!(vals.contains(&num_bigint::BigUint::from(2u32)));
        assert!(vals.contains(&num_bigint::BigUint::from(5u32)));
    }
}
