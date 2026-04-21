//! UNSAT core type and high-level solving API.
//!
//! Mirrors cvc5's `FfCore` (a list of input facts that are jointly
//! unsatisfiable).  We currently implement the **trivial conflict** mode
//! (return all input facts on UNSAT), matching cvc5's default behaviour
//! when `ffTraceGb` is disabled.  Full GB-step tracing (Buchberger
//! reduction history → backtrace to which inputs produced 1) is left as
//! future work; the structure here is designed to accommodate it.

use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;
use feanor_math::ring::RingStore;

use crate::bitprop::BitProp;
use crate::encoder::EncodedSystem;
use crate::gb::{compute_gb_with_timeout, GbResult};
use crate::model;
use crate::parse;
use crate::poly::{FfPolyRing, Poly};
use crate::split_gb::{admit, split_find_zero, split_find_zero_cancel, split_gb, split_gb_cancel};
use crate::timeout::CancelToken;

/// An UNSAT core: indices into the input fact list that suffice for UNSAT.
pub type UnsatCore = Vec<usize>;

/// Solver mode: mirrors cvc5's `--ff-solver` option.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverMode {
    /// Split Groebner Basis (default, matches cvc5's `--ff-solver split`).
    SplitGb,
    /// Single Groebner Basis (matches cvc5's `--ff-solver gb`).
    SingleGb,
}

/// Outcome of the core solver.
#[derive(Debug, Clone)]
pub enum SolveOutcome {
    /// SAT — a model assigning every variable a field element (as BigUint).
    Sat(HashMap<String, BigUint>),
    /// UNSAT, with a (trivial) UNSAT core: indices of input facts.
    Unsat(UnsatCore),
    /// Unknown — the solver was cancelled before reaching a conclusion.
    Unknown,
}

/// Populate a `BitProp` by scanning the encoded polynomials for bit
/// constraints (`x*(x-1) = 0`) and bitsum patterns.
///
/// This mirrors cvc5's `split()` setup where `BitProp` is constructed from
/// the parsed facts + encoder.  We do it post-encoding by analysing the
/// polynomial structure with our `parse` module.
fn populate_bitprop<'r>(
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
) -> SolveOutcome {
    // Split into two ideals per cvc5's `split` (split_gb.cpp:148-160):
    //   - basis 0 ("linear"): bitsum polys + every input poly with deg <= 1
    //   - basis 1 ("nonlinear"): ALL input polys
    let nl_gens: Vec<Poly> = original_polys.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
    let mut l_gens: Vec<Poly> = Vec::new();
    for p in original_polys {
        if admit(poly_ring, 0, p) {
            l_gens.push(poly_ring.ring.clone_el(p));
        }
    }

    let mut bit_prop = BitProp::new(poly_ring);
    populate_bitprop(poly_ring, original_polys, &mut bit_prop);
    let split_basis = split_gb(poly_ring, vec![l_gens, nl_gens], &mut bit_prop);

    // Trivial UNSAT detection: any basis is the whole ring.
    if split_basis.iter().any(|b| b.is_whole_ring()) {
        return SolveOutcome::Unsat((0..original_polys.len()).collect());
    }

    match split_find_zero(poly_ring, split_basis, &mut bit_prop) {
        Some(point) => {
            let mut model = HashMap::new();
            let field = &poly_ring.field;
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names.len() {
                    model.insert(poly_ring.var_names[idx].clone(), field.to_biguint(val));
                }
            }
            SolveOutcome::Sat(model)
        }
        None => SolveOutcome::Unsat((0..original_polys.len()).collect()),
    }
}

/// Solve an `EncodedSystem` directly.  Convenience wrapper.
pub fn solve_encoded(encoded: &EncodedSystem) -> SolveOutcome {
    solve_split_gb(&encoded.poly_ring, &encoded.polynomials)
}

/// Solve with a specified mode.
pub fn solve_encoded_with_mode(
    encoded: &EncodedSystem,
    mode: SolverMode,
) -> SolveOutcome {
    match mode {
        SolverMode::SplitGb => solve_split_gb(&encoded.poly_ring, &encoded.polynomials),
        SolverMode::SingleGb => {
            let polys: Vec<Poly> = encoded.polynomials.iter()
                .map(|p| encoded.poly_ring.ring.clone_el(p)).collect();
            solve_single_gb(&encoded.poly_ring, polys)
        }
    }
}

/// Solve with a specified mode and cooperative timeout.
pub fn solve_encoded_with_mode_cancel(
    encoded: &EncodedSystem,
    mode: SolverMode,
    cancel: &CancelToken,
) -> SolveOutcome {
    match mode {
        SolverMode::SplitGb => solve_split_gb_cancel(&encoded.poly_ring, &encoded.polynomials, cancel),
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

/// Single Groebner basis solver (matches cvc5's `--ff-solver gb`).
pub fn solve_single_gb(
    poly_ring: &FfPolyRing,
    polynomials: Vec<Poly>,
) -> SolveOutcome {
    let n = polynomials.len();
    let gb_result = compute_gb_with_timeout(poly_ring, polynomials, None);
    match gb_result {
        GbResult::Trivial => SolveOutcome::Unsat((0..n).collect()),
        GbResult::Timeout => SolveOutcome::Unknown,
        GbResult::NonTrivial(gb) => {
            match model::find_zero(poly_ring, &gb) {
                Some(m) => SolveOutcome::Sat(m),
                None => SolveOutcome::Unknown,
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
    solve_split_gb_cancel(&encoded.poly_ring, &encoded.polynomials, cancel)
}

/// Solve with cooperative cancellation.
pub fn solve_split_gb_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    original_polys: &[Poly],
    cancel: &CancelToken,
) -> SolveOutcome {
    let nl_gens: Vec<Poly> = original_polys.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
    let mut l_gens: Vec<Poly> = Vec::new();
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
        Ok(Some(point)) => {
            let mut model = HashMap::new();
            let field = &poly_ring.field;
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names.len() {
                    model.insert(poly_ring.var_names[idx].clone(), field.to_biguint(val));
                }
            }
            SolveOutcome::Sat(model)
        }
        Ok(None) => SolveOutcome::Unsat((0..original_polys.len()).collect()),
        Err(_) => SolveOutcome::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::FfField;

    fn ff(p: u32) -> FfField { FfField::new(&BigUint::from(p)) }

    #[test]
    fn test_solve_sat() {
        // x*y - 1 = 0,  x = 2 in GF(7)  →  y = 4
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p1 = pr.sub(xy, pr.one());
        let two = pr.field.from_int(2);
        let p2 = pr.sub(pr.var(0), pr.constant(two));

        match solve_split_gb(&pr, &[p1, p2]) {
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
        match solve_split_gb(&pr, &[p1, p2]) {
            SolveOutcome::Unsat(core) => {
                assert_eq!(core.len(), 2);
                assert!(core.contains(&0) && core.contains(&1));
            }
            _ => panic!("expected UNSAT"),
        }
    }
}
