//! Groebner Basis computation over GF(p) using feanor-math's Buchberger algorithm.
//!
//! Provides a single-GB solver mode (DegRevLex → Lex) with optional timeout.
//! This is the simpler alternative to the Split GB approach.

use std::time::{Duration, Instant};

use feanor_math::ring::*;
use feanor_math::algorithms::buchberger::*;
use feanor_math::rings::multivariate::*;

use crate::poly::{FfPolyRing, Poly};

/// Result of a Groebner basis computation.
pub enum GbResult {
    /// The ideal is trivial (contains a nonzero constant) — UNSAT.
    Trivial,
    /// Non-trivial GB — may be SAT. Contains the Lex-ordered GB.
    NonTrivial(Vec<Poly>),
    /// Computation timed out.
    Timeout,
}

/// Compute a Groebner basis with optional timeout.
pub fn compute_gb(poly_ring: &FfPolyRing, polynomials: Vec<Poly>) -> GbResult {
    compute_gb_with_timeout(poly_ring, polynomials, None)
}

/// Compute a Groebner basis with a timeout deadline.
pub fn compute_gb_with_timeout(
    poly_ring: &FfPolyRing,
    polynomials: Vec<Poly>,
    timeout: Option<Duration>,
) -> GbResult {
    if polynomials.is_empty() {
        return GbResult::NonTrivial(vec![]);
    }

    let ring = &poly_ring.ring;
    let deadline = timeout.map(|t| Instant::now() + t);

    // Phase 1: DegRevLex GB (faster)
    let gb_degrevlex = buchberger_simple(ring, polynomials, DegRevLex);

    if let Some(d) = deadline {
        if Instant::now() > d {
            return GbResult::Timeout;
        }
    }

    if is_trivial(ring, &gb_degrevlex) {
        return GbResult::Trivial;
    }

    // Phase 2: Lex GB (for model extraction)
    let gb_lex = buchberger_simple(ring, gb_degrevlex, Lex);

    if let Some(d) = deadline {
        if Instant::now() > d {
            return GbResult::Timeout;
        }
    }

    if is_trivial(ring, &gb_lex) {
        return GbResult::Trivial;
    }

    GbResult::NonTrivial(gb_lex)
}

/// Check if a GB is trivial (ideal = whole ring).
fn is_trivial(ring: &crate::poly::PolyRingType, gb: &[Poly]) -> bool {
    for p in gb {
        if !ring.is_zero(p) {
            let vars = ring.appearing_indeterminates(p);
            if vars.is_empty() {
                return true;
            }
        }
    }
    false
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
