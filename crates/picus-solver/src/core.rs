//! UNSAT core type and high-level solving API.
//!
//! An UNSAT core is a list of input fact indices that are jointly
//! unsatisfiable. The single-GB solver uses Buchberger observer hooks
//! (via [`crate::gb::tracer::GbTracer`]) to track which input polynomials
//! contribute to the UNSAT proof. The split-GB solver returns the traced
//! dependency core when the whole-ring element can be attributed to a
//! subset of inputs, and the all-input core as a sound fallback otherwise.

use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;

use crate::frontend::bitprop::BitProp;
use crate::frontend::encoder::EncodedSystem;
use crate::gb::{compute_gb_with_timeout_traced, GbResultTraced};
use crate::gb::ideal::Ideal;
use crate::gb::model;
use crate::frontend::parse;
use crate::poly::{FfPolyRing, Poly};
use crate::split_gb::split_find_zero_cancel;
use crate::timeout::CancelToken;
use std::time::Duration;

/// An UNSAT core: indices into the input fact list that suffice for UNSAT.
pub type UnsatCore = Vec<usize>;

/// Outcome of the core solver.
///
/// `Unsat` and `Unknown` are distinct: `Unsat` is a proof of
/// infeasibility, `Unknown` indicates the search was cancelled or
/// bounded out. Callers may retry on `Unknown` with relaxed bounds.
#[derive(Debug, Clone)]
pub enum SolveOutcome {
    /// SAT — a model assigning every variable a field element (as BigUint).
    Sat(HashMap<String, BigUint>),
    /// UNSAT, with an UNSAT core: indices of input facts.
    Unsat(UnsatCore),
    /// Unknown — the solver was cancelled, or bounded search exhausted
    /// without proving a definite verdict. Distinct from `Unsat`.
    Unknown,
}

/// Populate a `BitProp` by scanning the encoded polynomials for bit
/// constraints (`x*(x-1) = 0`) and bitsum patterns.
pub fn populate_bitprop<'r>(
    poly_ring: &'r FfPolyRing,
    polys: &[Poly],
    bit_prop: &mut BitProp<'r>,
) {
    // Phase 1: detect bit constraints (x^2 - x = 0) → add_bit
    for p in polys {
        if let Some(bc) = parse::bit_constraint(poly_ring, p) {
            bit_prop.add_bit(bc.var);
        }
    }

    // Phase 2: detect bitsums in each polynomial → add_bitsum
    // Collect all known bit variables for the hint set.
    let bits_hint: HashSet<usize> = bit_prop.bits.clone();
    for p in polys {
        if let Some((sums, _residual)) = parse::bit_sums(poly_ring, p, &bits_hint) {
            for bs in &sums {
                if bs.bits.len() >= 2 {
                    bit_prop.add_bitsum(bs.bits.clone());
                }
            }
        }
    }
}

/// Solve a system of polynomial constraints using the Split GB algorithm.
///
/// `original_polys` is the full list of input polynomial generators (in
/// the same order as `encoded.polys`); the returned `UnsatCore` is a list
/// of indices into this slice.
pub fn solve_split_gb<'r>(
    poly_ring: &'r FfPolyRing,
    original_polys: &[Poly],
    bitsum_polys: &[Poly],
) -> SolveOutcome {
    solve_split_gb_cancel(poly_ring, original_polys, bitsum_polys, &CancelToken::none())
}

/// Sub-budget for the monolithic radical-membership GB (config
/// `radical_membership`), capping the futile cost on a GB-bound query so the
/// split path still gets most of the solve timeout.
const RADICAL_MEMBERSHIP_BUDGET: Duration = Duration::from_millis(3000);

/// Monolithic-GB radical Safe fast-path (config `radical_membership`).
///
/// `gens` is the full query system: constraint generators, bitsum
/// definitions, and the query's Rabinowitsch witness `(x_a−x_b)·w − 1`.
/// Computes their *monolithic* Gröbner basis and returns `Some(Unsat)` iff it
/// is the whole ring — i.e. `1 ∈ ⟨I, (x_a−x_b)·w − 1⟩`, so `x_a−x_b ∈ √I`, so
/// the system has no solution over the algebraic closure (hence none over
/// GF(p)) and the disequality query is UNSAT (the output is forced unique =
/// Safe). `n_core` sizes the conservative UNSAT core.
///
/// Bounded by `cancel ⊕ budget`: a GB-bound query exhausts the sub-budget and
/// returns `None`, falling through to the split path. Sound one-directional —
/// only a fully-computed whole-ring GB yields a verdict; a non-whole-ring or
/// cancelled GB is inconclusive.
pub(crate) fn radical_membership_unsat(
    poly_ring: &FfPolyRing,
    gens: Vec<Poly>,
    n_core: usize,
    cancel: &CancelToken,
) -> Option<SolveOutcome> {
    let budget = CancelToken::with_timeout(RADICAL_MEMBERSHIP_BUDGET);
    let tok = CancelToken::either(cancel, &budget);
    match Ideal::new_with_cancel(poly_ring, gens, &tok) {
        Ok(ideal) if ideal.is_whole_ring() => Some(SolveOutcome::Unsat((0..n_core).collect())),
        _ => None,
    }
}

/// Solve an `EncodedSystem` directly.  Convenience wrapper.
pub fn solve_encoded(encoded: &EncodedSystem) -> SolveOutcome {
    solve_encoded_with_cancel(encoded, &CancelToken::none())
}

/// Single Groebner basis solver.
///
/// Uses Buchberger observer hooks to trace which input polynomials
/// contribute to an UNSAT proof.
pub fn solve_single_gb(
    poly_ring: &FfPolyRing,
    polynomials: Vec<Poly>,
) -> SolveOutcome {
    let n_polys = polynomials.len();
    let gb_result = compute_gb_with_timeout_traced(poly_ring, polynomials, None);
    match gb_result {
        GbResultTraced::Trivial(core) => SolveOutcome::Unsat(core),
        GbResultTraced::Timeout => SolveOutcome::Unknown,
        GbResultTraced::NonTrivial(gb) => {
            match model::find_zero(poly_ring, &gb) {
                model::FindZeroOutcome::Sat(m) => {
                    if model::verify_model(poly_ring, &gb, &m) {
                        SolveOutcome::Sat(m)
                    } else {
                        log::warn!("SingleGb model validation failed; reporting Unknown");
                        SolveOutcome::Unknown
                    }
                }
                model::FindZeroOutcome::Unsat => {
                    SolveOutcome::Unsat((0..n_polys).collect())
                }
                model::FindZeroOutcome::Unknown => SolveOutcome::Unknown,
            }
        }
    }
}

/// Solve an `EncodedSystem` with cooperative timeout.
///
/// Returns `SolveOutcome::Unknown` if the cancel token fires.
pub fn solve_encoded_with_cancel(
    encoded: &EncodedSystem,
    cancel: &CancelToken,
) -> SolveOutcome {
    solve_split_gb_cancel(&encoded.poly_ring, &encoded.polynomials, &encoded.bitsum_polys, cancel)
}

/// Solve with cooperative cancellation.
pub fn solve_split_gb_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    original_polys: &[Poly],
    bitsum_polys: &[Poly],
    cancel: &CancelToken,
) -> SolveOutcome {
    // Linear (Gaussian) pre-elimination is applied once at the top level
    // (`PolyIR::pre_eliminate_linear` in the backend), so the generators
    // reaching this conjunctive core — on both the direct and the CDCL(T)
    // per-check paths — are already reduced. This function does not
    // re-eliminate.

    // Pre-GB short-circuit: a generator that is itself a nonzero constant
    // makes the ideal the whole ring (a nonzero field constant is a unit),
    // so the system is UNSAT. This mirrors cvc5's `postRewriteFfEq` folding
    // a `const = const` assertion to `false` before the solver runs, and
    // lets a trivially-contradictory input (an assertion `2 = 1`, or an
    // equality that rewrote to a nonzero constant) skip partition building
    // and the split-GB fixpoint. The `is_whole_ring` check after the
    // fixpoint reaches the same verdict; this short-circuit only moves the
    // detection before partition building, and yields the exact one-element
    // core for this case.
    if let Some(i) = original_polys
        .iter()
        .position(|p| !p.is_zero() && p.is_constant())
    {
        return SolveOutcome::Unsat(vec![i]);
    }

    // Opt-in monolithic radical-membership Safe fast-path: decide the query
    // UNSAT by one whole-ring check on the monolithic GB of the combined
    // system, skipping partition building and the model search (which
    // enumerates exponentially on forced-equal outputs the per-partition
    // whole-ring check below cannot see).
    if crate::config::with(|c| c.radical_membership) {
        let combined: Vec<Poly> = original_polys
            .iter()
            .chain(bitsum_polys.iter())
            .map(|p| poly_ring.ring.clone_el(p))
            .collect();
        if let Some(outcome) =
            radical_membership_unsat(poly_ring, combined, original_polys.len(), cancel)
        {
            return outcome;
        }
    }

    let (gens, provenance) =
        crate::split_gb::build_partitions(poly_ring, original_polys, bitsum_polys);
    // Lower each generator's provenance to its UNSAT-core dependency set: an
    // original input `i` depends on itself; a bitsum definition has none.
    let deps: Vec<Vec<std::collections::BTreeSet<usize>>> = provenance
        .iter()
        .map(|part| {
            part.iter()
                .map(|prov| {
                    let mut s = std::collections::BTreeSet::new();
                    if let Some(i) = prov {
                        s.insert(*i);
                    }
                    s
                })
                .collect()
        })
        .collect();

    let mut bit_prop = BitProp::new(poly_ring);
    populate_bitprop(poly_ring, original_polys, &mut bit_prop);
    populate_bitprop(poly_ring, bitsum_polys, &mut bit_prop);
    let traced = match crate::split_gb::split_gb_cancel_traced(
        poly_ring,
        gens,
        deps,
        &mut bit_prop,
        cancel,
    ) {
        Ok(t) => t,
        Err(_) => return SolveOutcome::Unknown,
    };
    let split_basis = traced.split_basis;

    if split_basis.iter().any(|b| b.is_whole_ring()) {
        let core = traced
            .unsat_core
            .unwrap_or_else(|| (0..original_polys.len()).collect());
        return SolveOutcome::Unsat(core);
    }

    match split_find_zero_cancel(poly_ring, split_basis, &mut bit_prop, cancel) {
        Ok(crate::split_gb::SplitFindZeroOutcome::Sat(point)) => {
            let mut model_map = HashMap::new();
            let field = &poly_ring.field();
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names().len() {
                    model_map.insert(poly_ring.var_names()[idx].clone(), field.to_biguint(val));
                }
            }
            if model::verify_model(poly_ring, original_polys, &model_map)
                && model::verify_model(poly_ring, bitsum_polys, &model_map)
            {
                SolveOutcome::Sat(model_map)
            } else {
                log::warn!("model validation failed; reporting Unknown");
                SolveOutcome::Unknown
            }
        }
        Ok(crate::split_gb::SplitFindZeroOutcome::Unsat) => {
            SolveOutcome::Unsat((0..original_polys.len()).collect())
        }
        Ok(crate::split_gb::SplitFindZeroOutcome::Unknown) => SolveOutcome::Unknown,
        Err(_) => SolveOutcome::Unknown,
    }
}

#[cfg(test)]
#[path = "core_tests.rs"]
mod tests;
