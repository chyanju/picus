//! Groebner Basis computation over GF(p) using the in-tree Buchberger
//! algorithm (`crate::ff::buchberger`, exposed via `crate::ideal`).
//!
//! Provides a single-GB solver mode (DegRevLex → Lex) with cooperative
//! timeout. Thin wrapper over `ideal::compute_gb_with_order{,_traced}`.

use std::time::Duration;

use crate::ff::monomial::MonomialOrder;
use crate::ideal::{compute_gb_with_order, compute_gb_with_order_traced};
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;
use crate::tracer::GbTracer;

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

    // Phase 2: Lex GB (for model extraction via back-substitution)
    let gb_lex = compute_gb_with_order(poly_ring, gb_degrevlex, &cancel, MonomialOrder::Lex);

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

    // Phase 2: Lex GB (no tracing needed — only used for model extraction)
    let gb_lex = compute_gb_with_order(poly_ring, gb_degrevlex, &cancel, MonomialOrder::Lex);

    if cancel.is_cancelled() {
        return GbResultTraced::Timeout;
    }
    if is_trivial(&poly_ring.ring, &gb_lex) {
        // Became trivial in Lex phase — no trace info, return trivial core
        return GbResultTraced::Trivial((0..n_inputs).collect());
    }

    GbResultTraced::NonTrivial(gb_lex)
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
mod tests {
    use super::*;
    use crate::field::FfField;
    use num_bigint::BigUint;

    #[test]
    fn test_trivial_gb() {
        // x = 0 and x = 1 over GF(17) → UNSAT
        let field = FfField::new(&BigUint::from(17u32));
        let pr = FfPolyRing::new(field, vec!["x".into()]);

        let x = pr.var(0);
        let p1 = pr.clone_poly(&x);
        let p2 = pr.sub(x, pr.one());

        match compute_gb(&pr, vec![p1, p2]) {
            GbResult::Trivial => {}
            GbResult::NonTrivial(_) | GbResult::Timeout => panic!("expected trivial GB"),
        }
    }

    #[test]
    fn test_nontrivial_gb() {
        // x * y = 1 over GF(17) → SAT
        let field = FfField::new(&BigUint::from(17u32));
        let pr = FfPolyRing::new(field, vec!["x".into(), "y".into()]);

        let xy = pr.mul(pr.var(0), pr.var(1));
        let p = pr.sub(xy, pr.one());

        match compute_gb(&pr, vec![p]) {
            GbResult::Trivial | GbResult::Timeout => panic!("expected non-trivial"),
            GbResult::NonTrivial(gb) => assert!(!gb.is_empty()),
        }
    }
}
