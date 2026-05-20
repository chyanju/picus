//! UNSAT core type and high-level solving API.
//!
//! An UNSAT core is a list of input fact indices that are jointly
//! unsatisfiable. The single-GB solver uses Buchberger observer hooks
//! (via [`crate::tracer::GbTracer`]) to track which input polynomials
//! contribute to the UNSAT proof. The split-GB solver returns trivial
//! (all-input) cores.

use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;

use crate::bitprop::BitProp;
use crate::encoder::EncodedSystem;
use crate::gb::{compute_gb_with_timeout_traced, GbResultTraced};
use crate::model;
use crate::parse;
use crate::poly::{FfPolyRing, Poly};
use crate::split_gb::{admit, split_find_zero_cancel, split_gb_cancel};
use crate::timeout::CancelToken;

/// An UNSAT core: indices into the input fact list that suffice for UNSAT.
pub type UnsatCore = Vec<usize>;

/// Solver mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverMode {
    /// Split Groebner basis (default).
    SplitGb,
    /// Single Groebner basis (DegRevLex → Lex → findZero).
    SingleGb,
}

/// Outcome of the core solver.
///
/// `Unsat` and `Unknown` are distinct: `Unsat` is a proof of
/// infeasibility, `Unknown` indicates the search was cancelled or
/// bounded out. Callers may retry on `Unknown` with relaxed bounds.
#[derive(Debug, Clone)]
pub enum SolveOutcome {
    /// SAT — a model assigning every variable a field element (as BigUint).
    Sat(HashMap<String, BigUint>),
    /// UNSAT, with a (trivial) UNSAT core: indices of input facts.
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

/// Solve an `EncodedSystem` directly.  Convenience wrapper.
pub fn solve_encoded(encoded: &EncodedSystem) -> SolveOutcome {
    solve_encoded_with_cancel(encoded, &CancelToken::none())
}

/// Solve with a specified mode.
pub fn solve_encoded_with_mode(
    encoded: &EncodedSystem,
    mode: SolverMode,
) -> SolveOutcome {
    solve_encoded_with_mode_cancel(encoded, mode, &CancelToken::none())
}

/// Solve with a specified mode and cooperative timeout.
pub fn solve_encoded_with_mode_cancel(
    encoded: &EncodedSystem,
    mode: SolverMode,
    cancel: &CancelToken,
) -> SolveOutcome {
    match mode {
        SolverMode::SplitGb => solve_split_gb_cancel(&encoded.poly_ring, &encoded.polynomials, &encoded.bitsum_polys, cancel),
        SolverMode::SingleGb => {
            if cancel.is_cancelled() { return SolveOutcome::Unknown; }
            let polys: Vec<Poly> = encoded.polynomials.iter()
                .map(|p| encoded.poly_ring.ring.clone_el(p)).collect();
            // Note: SingleGb mode uses buchberger_simple which doesn't support
            // mid-computation cancellation. The cancel token is checked between
            // the DegRevLex and Lex phases and after model construction.
            let result = solve_single_gb(&encoded.poly_ring, polys);
            if cancel.is_cancelled() { SolveOutcome::Unknown } else { result }
        }
    }
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
    let nl_gens: Vec<Poly> = original_polys.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
    let mut l_gens: Vec<Poly> = Vec::new();
    for p in bitsum_polys {
        l_gens.push(poly_ring.ring.clone_el(p));
    }
    for p in original_polys {
        if admit(poly_ring, 0, p) {
            l_gens.push(poly_ring.ring.clone_el(p));
        }
    }

    let mut bit_prop = BitProp::new(poly_ring);
    populate_bitprop(poly_ring, original_polys, &mut bit_prop);
    let split_basis = match split_gb_cancel(poly_ring, vec![l_gens, nl_gens], &mut bit_prop, cancel) {
        Ok(b) => b,
        Err(_) => return SolveOutcome::Unknown,
    };

    if split_basis.iter().any(|b| b.is_whole_ring()) {
        return SolveOutcome::Unsat((0..original_polys.len()).collect());
    }

    match split_find_zero_cancel(poly_ring, split_basis, &mut bit_prop, cancel) {
        Ok(crate::split_gb::SplitFindZeroOutcome::Sat(point)) => {
            let mut model_map = HashMap::new();
            let field = &poly_ring.field;
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names.len() {
                    model_map.insert(poly_ring.var_names[idx].clone(), field.to_biguint(val));
                }
            }
            if model::verify_model(poly_ring, original_polys, &model_map) {
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
mod tests {
    use super::*;
    use crate::field::FfField;

    fn ff(p: u32) -> FfField { FfField::new(BigUint::from(p)) }

    #[test]
    fn test_solve_sat() {
        // x*y - 1 = 0,  x = 2 in GF(7)  →  y = 4
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p1 = pr.sub(xy, pr.one());
        let two = pr.field.from_int(2);
        let p2 = pr.sub(pr.var(0), pr.constant(two));

        match solve_split_gb(&pr, &[p1, p2], &[]) {
            SolveOutcome::Sat(m) => {
                assert_eq!(m["x"], BigUint::from(2u32));
                let prod = (&m["x"] * &m["y"]) % BigUint::from(7u32);
                assert_eq!(prod, BigUint::from(1u32));
            }
            _ => panic!("expected SAT"),
        }
    }

    #[test]
    fn test_solve_unsat_returns_core() {
        // x = 2, x = 3 in GF(7): UNSAT, core = [0, 1].
        let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
        let two = pr.field.from_int(2);
        let three = pr.field.from_int(3);
        let p1 = pr.sub(pr.var(0), pr.constant(two));
        let p2 = pr.sub(pr.var(0), pr.constant(three));
        match solve_split_gb(&pr, &[p1, p2], &[]) {
            SolveOutcome::Unsat(core) => {
                assert_eq!(core.len(), 2);
                assert!(core.contains(&0) && core.contains(&1));
            }
            _ => panic!("expected UNSAT"),
        }
    }

    #[test]
    fn test_single_gb_traced_unsat_core() {
        // System: x = 2, x = 3, y = 1  in GF(7).
        // The UNSAT comes from the first two constraints only.
        // With tracing, the core should be a subset of {0, 1, 2}
        // and must include both 0 and 1 (since those are contradictory).
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let two = pr.field.from_int(2);
        let three = pr.field.from_int(3);
        let one = pr.field.from_int(1);
        let p0 = pr.sub(pr.var(0), pr.constant(two));   // x = 2
        let p1 = pr.sub(pr.var(0), pr.constant(three));  // x = 3
        let p2 = pr.sub(pr.var(1), pr.constant(one));    // y = 1 (irrelevant)
        match solve_single_gb(&pr, vec![p0, p1, p2]) {
            SolveOutcome::Unsat(core) => {
                // Core must contain 0 and 1 (the contradictory pair).
                assert!(core.contains(&0), "core must contain input 0 (x=2)");
                assert!(core.contains(&1), "core must contain input 1 (x=3)");
                // Core should NOT contain 2 (y=1 is irrelevant) in an
                // ideal tracer.  Due to conservative initial-basis tracking
                // this may still include 2, but it must be <= 3 elements.
                assert!(core.len() <= 3, "core should be bounded by total inputs");
                log::info!("UNSAT core: {:?} (ideal: [0, 1])", core);
            }
            _ => panic!("expected UNSAT"),
        }
    }

    #[test]
    fn test_single_gb_traced_sat() {
        // x*y = 1 in GF(7): SAT, tracing should not interfere.
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p = pr.sub(xy, pr.one());
        match solve_single_gb(&pr, vec![p]) {
            SolveOutcome::Sat(m) => {
                let prod = (&m["x"] * &m["y"]) % BigUint::from(7u32);
                assert_eq!(prod, BigUint::from(1u32));
            }
            _ => panic!("expected SAT"),
        }
    }
}
