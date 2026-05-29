//! Higher-level Gröbner-basis orchestration, layered over the low-level
//! engine in [`crate::ff`]. The split: [`crate::ff`] holds the algorithms
//! (Buchberger, F4, sparse GB, Cantor-Zassenhaus root finding) over
//! [`picus_core::ff`]'s GF(p) data types; this `gb` module groups the
//! work that drives them — the ideal API ([`ideal`]), model construction
//! ([`model`]), root extraction ([`roots`]), the FGLM order change
//! ([`fglm`]), homogenisation ([`gb_homog`] / [`homog_ring`]), incremental
//! push/pop ([`incremental`]), and UNSAT-core tracing ([`tracer`]). Both
//! are named for GF(p) algebra but sit at different layers.
//!
//! The root module itself provides a single-GB solver mode (DegRevLex →
//! Lex) with cooperative timeout — a thin wrapper over
//! `ideal::compute_gb_with_order{,_traced}`.

use std::time::Duration;

use crate::ff::monomial::MonomialOrder;
use crate::gb::ideal::{compute_gb_with_order, compute_gb_with_order_traced};
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;
use crate::gb::tracer::GbTracer;

/// Result of a Groebner basis computation.
pub enum GbResult {
    /// The ideal is trivial (contains a nonzero constant) — UNSAT.
    Trivial,
    /// Non-trivial GB — may be SAT. Contains the Lex-ordered GB.
    NonTrivial(Vec<Poly>),
    /// Computation timed out or was cancelled.
    Timeout,
}

/// Result of a traced Groebner basis computation.
pub enum GbResultTraced {
    /// UNSAT with a traced core: indices into the original input polynomials.
    Trivial(Vec<usize>),
    /// Non-trivial — same as `GbResult::NonTrivial`.
    NonTrivial(Vec<Poly>),
    /// Timeout.
    Timeout,
}

/// Compute a Groebner basis without timeout.
pub fn compute_gb(poly_ring: &FfPolyRing, polynomials: Vec<Poly>) -> GbResult {
    compute_gb_with_timeout(poly_ring, polynomials, None)
}

/// Compute a Groebner basis with optional timeout.
///
/// Phase 1: DegRevLex GB (faster ordering for reduction).
/// Phase 2: Lex GB from Phase 1 output (needed for model extraction).
/// Both phases use the optimized `(2,2)` multiplication table ring and
/// support cooperative cancellation via `CancelToken`.
pub fn compute_gb_with_timeout(
    poly_ring: &FfPolyRing,
    polynomials: Vec<Poly>,
    timeout: Option<Duration>,
) -> GbResult {
    if polynomials.is_empty() {
        return GbResult::NonTrivial(vec![]);
    }

    let cancel = match timeout {
        Some(d) => CancelToken::with_timeout(d),
        None => CancelToken::none(),
    };

    // Phase 1: DegRevLex GB
    let gb_degrevlex = compute_gb_with_order(poly_ring, polynomials, &cancel, MonomialOrder::DegRevLex);

    if cancel.is_cancelled() {
        return GbResult::Timeout;
    }
    if is_trivial(&poly_ring.ring, &gb_degrevlex) {
        return GbResult::Trivial;
    }

    // Phase 2: Lex GB (for model extraction via back-substitution),
    // via FGLM when zero-dimensional.
    let gb_lex = degrevlex_to_lex(poly_ring, gb_degrevlex, &cancel);

    if cancel.is_cancelled() {
        return GbResult::Timeout;
    }
    if is_trivial(&poly_ring.ring, &gb_lex) {
        return GbResult::Trivial;
    }

    GbResult::NonTrivial(gb_lex)
}

/// Like [`compute_gb_with_timeout`], but with UNSAT core tracing enabled.
///
/// When the DegRevLex phase produces a trivial basis (UNSAT), the tracer
/// is used to extract the minimal set of input polynomial indices
/// responsible for the conflict.
pub fn compute_gb_with_timeout_traced(
    poly_ring: &FfPolyRing,
    polynomials: Vec<Poly>,
    timeout: Option<Duration>,
) -> GbResultTraced {
    let n_inputs = polynomials.len();
    if polynomials.is_empty() {
        return GbResultTraced::NonTrivial(vec![]);
    }

    let cancel = match timeout {
        Some(d) => CancelToken::with_timeout(d),
        None => CancelToken::none(),
    };

    // Phase 1: DegRevLex GB with tracing
    let mut tracer = GbTracer::new(n_inputs);
    let gb_degrevlex = compute_gb_with_order_traced(
        poly_ring, polynomials, &cancel, MonomialOrder::DegRevLex, &mut tracer,
    );

    if cancel.is_cancelled() {
        return GbResultTraced::Timeout;
    }

    if find_trivial_element(&poly_ring.ring, &gb_degrevlex).is_some() {
        // UNSAT — extract the core from the tracer.
        //
        // Note: `find_trivial_element` indexes into the *finalized* basis
        // (which collapses to `[1]` for any trivial GB and discards
        // tracer-correlated indices). The actual contradictory polynomial
        // in the tracer's history is the LAST one pushed before
        // `abort_on_trivial` returned: `tracer.basis_count() - 1`.
        let core = if tracer.basis_count() > 0 {
            tracer.unsat_core_for(tracer.basis_count() - 1)
        } else {
            (0..n_inputs).collect()
        };
        return GbResultTraced::Trivial(core);
    }

    // Phase 2: Lex GB (no tracing needed — only used for model extraction),
    // via FGLM when zero-dimensional.
    let gb_lex = degrevlex_to_lex(poly_ring, gb_degrevlex, &cancel);

    if cancel.is_cancelled() {
        return GbResultTraced::Timeout;
    }
    if is_trivial(&poly_ring.ring, &gb_lex) {
        // Became trivial in Lex phase — no trace info, return trivial core
        return GbResultTraced::Trivial((0..n_inputs).collect());
    }

    GbResultTraced::NonTrivial(gb_lex)
}

/// Convert a DegRevLex Gröbner basis to a Lex GB for model extraction.
///
/// Uses FGLM order conversion ([`crate::gb::fglm`]) when the ideal is
/// zero-dimensional — linear algebra in the finite quotient `R/I`, far
/// cheaper than a second Buchberger run — and falls back to a direct Lex
/// Buchberger computation otherwise.
fn degrevlex_to_lex(
    poly_ring: &FfPolyRing,
    gb_degrevlex: Vec<Poly>,
    cancel: &CancelToken,
) -> Vec<Poly> {
    let ideal = crate::gb::ideal::Ideal::from_gb(poly_ring, gb_degrevlex);
    match crate::gb::fglm::fglm_to_lex(&ideal) {
        Some(lex) => lex,
        None => {
            let basis = ideal.basis;
            compute_gb_with_order(poly_ring, basis, cancel, MonomialOrder::Lex)
        }
    }
}

/// Check if a GB is trivial (ideal = whole ring).
fn is_trivial(ring: &crate::poly::PolyRingType, gb: &[Poly]) -> bool {
    find_trivial_element(ring, gb).is_some()
}

/// Find the index of a nonzero constant in the basis, if any.
fn find_trivial_element(ring: &crate::poly::PolyRingType, gb: &[Poly]) -> Option<usize> {
    for (i, p) in gb.iter().enumerate() {
        if !ring.is_zero(p) {
            let vars = ring.appearing_indeterminates(p);
            if vars.is_empty() {
                return Some(i);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests;

// Submodules: ideal operations, incremental GB, root finding, homogenization
// pipeline, model construction, branching, and UNSAT-core tracing.
pub mod fglm;
pub mod ideal;
pub mod incremental;
pub mod linsolve;
pub mod roots;
pub(crate) mod gb_homog;
pub(crate) mod homog_ring;
pub(crate) mod model;
pub(crate) mod brancher;
pub(crate) mod tracer;
