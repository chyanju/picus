//! `compute_gb_by_homog`: GB-by-homogenization driver.
//!
//! Mirrors CoCoA's GB-by-homogenisation (`myGBasisByHomog`):
//!
//! 1. Build extended ring `Ph = P[h]` ([`crate::gb::homog_ring::HomogRing`]).
//! 2. Lift every input `f_i ∈ P` into `Ph`, then homogenize to its top
//!    total degree (so every generator is `d_i`-homogeneous in `Ph`).
//! 3. Run plain DegRevLex Buchberger on `Ph` via the repr-aware raw entry
//!    [`crate::gb::ideal::compute_gb_direct`] (sparse or dense engine per the
//!    active representation — so by-homog stays sparse under the sparse repr).
//!    The raw direct entry (not the dispatching `compute_gb_with_order`)
//!    avoids recursing back into ByHomog on the homogenised ring.
//! 4. Dehomogenize each basis element back to `P` (`h := 1`).
//! 5. Interreduce in `P` (drop LM-divisible duplicates, normal-form survivors).
//!
//! Rationale: in `Ph`, every input is exactly degree `d_i`, so the
//! in-tree sugar-degree S-pair selector ([`ff::buchberger`]) has
//! `sugar = wdeg` without mispredictions; pairs are processed in
//! strict ascending degree, avoiding the "intermediate expression
//! swell" that stalls bit-decomposition ideals.

use crate::ff::monomial::MonomialOrder;
use crate::gb::homog_ring::HomogRing;
use crate::gb::ideal::{compute_gb_direct, interreduce_basis};
use crate::metric;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;

/// Compute a DegRevLex Groebner basis of `gens ⊂ P` via the
/// homogenize → GB → dehomogenize → interreduce pipeline.
///
/// Contract:
/// * Input: arbitrary (possibly non-homogeneous) polynomials in `P`.
/// * Output: a Groebner basis of `(gens) ⊂ P` in DegRevLex order on `P`,
///   suitable to be wrapped by `Ideal::from_gb`.
/// * Empty input → empty basis (matches `compute_gb_with_order`).
/// * Cancellation: the inner `compute_gb_direct` already honors
///   `cancel`; if it fires, returns whatever interreduced dehom basis is
///   available (possibly empty).
#[metric]
pub fn compute_gb_by_homog(
    pr: &FfPolyRing,
    gens: Vec<Poly>,
    cancel: &CancelToken,
) -> Vec<Poly> {
    if gens.is_empty() {
        return Vec::new();
    }

    // Step 1: extended ring Ph
    let h = HomogRing::new(pr);

    // Step 2: lift + homogenize, dropping zeros.
    let gh: Vec<Poly> = gens
        .iter()
        .filter(|p| !pr.is_zero(p))
        .map(|p| h.lift_and_homogenize(p))
        .collect();

    if gh.is_empty() {
        return Vec::new();
    }

    if cancel.is_cancelled() {
        return Vec::new();
    }

    // Step 3: plain DegRevLex Buchberger on Ph, routed to the sparse or
    // dense engine per the active representation. The raw direct entry
    // (not the dispatching `compute_gb_with_order`) avoids recursing back
    // into ByHomog on the homogenised ring.
    let gb_h = compute_gb_direct(&h.ext, gh, cancel, MonomialOrder::DegRevLex);

    if cancel.is_cancelled() {
        // Best-effort: dehom + interreduce whatever the cancelled GB call
        // produced; the outer cancel check generally discards it.
    }

    // Step 4: dehom each element back to P.
    let mut gb_p: Vec<Poly> = gb_h
        .iter()
        .map(|q| h.dehom(q))
        .filter(|p| !pr.is_zero(p))
        .collect();

    if gb_p.is_empty() {
        return gb_p;
    }

    // Step 5: interreduce in P.  This (a) drops LM-divisible duplicates
    // produced by the dehom collapse (e.g. `h^2·m` and `h·m` both → `m`),
    // (b) normal-forms survivors, (c) monic-normalizes.
    gb_p = interreduce_basis(pr, gb_p, cancel);
    gb_p
}

#[cfg(test)]
#[path = "gb_homog_tests.rs"]
mod tests;
