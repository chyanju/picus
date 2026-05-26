//! UNSAT core type and high-level solving API.
//!
//! An UNSAT core is a list of input fact indices that are jointly
//! unsatisfiable. The single-GB solver uses Buchberger observer hooks
//! (via [`crate::gb::tracer::GbTracer`]) to track which input polynomials
//! contribute to the UNSAT proof. The split-GB solver returns trivial
//! (all-input) cores.

use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;

use crate::frontend::bitprop::BitProp;
use crate::frontend::encoder::EncodedSystem;
use crate::gb::{compute_gb_with_timeout_traced, GbResultTraced};
use crate::gb::model;
use crate::frontend::parse;
use crate::poly::{FfPolyRing, Poly};
use crate::split_gb::{admit, split_find_zero_cancel};
use crate::timeout::CancelToken;

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
    let nl_gens: Vec<Poly> = original_polys.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
    let mut nl_deps: Vec<std::collections::BTreeSet<usize>> = Vec::with_capacity(original_polys.len());
    for i in 0..original_polys.len() {
        let mut s = std::collections::BTreeSet::new();
        s.insert(i);
        nl_deps.push(s);
    }
    let mut l_gens: Vec<Poly> = Vec::new();
    let mut l_deps: Vec<std::collections::BTreeSet<usize>> = Vec::new();
    for p in bitsum_polys {
        l_gens.push(poly_ring.ring.clone_el(p));
        l_deps.push(std::collections::BTreeSet::new());
    }
    for (i, p) in original_polys.iter().enumerate() {
        if admit(poly_ring, 0, p) {
            l_gens.push(poly_ring.ring.clone_el(p));
            let mut s = std::collections::BTreeSet::new();
            s.insert(i);
            l_deps.push(s);
        }
    }

    let mut bit_prop = BitProp::new(poly_ring);
    populate_bitprop(poly_ring, original_polys, &mut bit_prop);
    populate_bitprop(poly_ring, bitsum_polys, &mut bit_prop);
    let traced = match crate::split_gb::split_gb_cancel_traced(
        poly_ring,
        vec![l_gens, nl_gens],
        vec![l_deps, nl_deps],
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
    use crate::ff::field::PrimeField;

    fn ff(p: u32) -> PrimeField { PrimeField::new(BigUint::from(p)) }

    #[test]
    fn test_solve_sat() {
        // x*y - 1 = 0,  x = 2 in GF(7)  →  y = 4
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p1 = pr.sub(xy, pr.one());
        let two = pr.field().from_int(2);
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
        let two = pr.field().from_int(2);
        let three = pr.field().from_int(3);
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
        let two = pr.field().from_int(2);
        let three = pr.field().from_int(3);
        let one = pr.field().from_int(1);
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
    fn test_split_gb_traced_unsat_core_is_sound_superset() {
        // System: x = 2, x = 3, y = 1  in GF(7).
        // The UNSAT comes from the first two constraints only, so the true
        // minimal core is {0, 1}. The split-GB traced path attributes
        // dependencies by a conservative *over*-approximation (the union of
        // all original inputs feeding the contradictory partition; see
        // `split_gb::fixpoint::run_fixpoint_traced`), so the returned core is
        // guaranteed to be a sound *super-set* of the minimal core — it must
        // contain {0, 1} and stay within the input range, but it may also
        // include the irrelevant input 2 (y=1). This pins only the soundness
        // invariant: the core never drops a generator the contradiction needs.
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let two = pr.field().from_int(2);
        let three = pr.field().from_int(3);
        let one = pr.field().from_int(1);
        let p0 = pr.sub(pr.var(0), pr.constant(two));
        let p1 = pr.sub(pr.var(0), pr.constant(three));
        let p2 = pr.sub(pr.var(1), pr.constant(one));
        match solve_split_gb(&pr, &[p0, p1, p2], &[]) {
            SolveOutcome::Unsat(core) => {
                assert!(core.contains(&0), "core must contain input 0 (x=2)");
                assert!(core.contains(&1), "core must contain input 1 (x=3)");
                assert!(
                    core.iter().all(|&i| i < 3),
                    "core must be a subset of the 3 inputs; got {:?}",
                    core
                );
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

    #[test]
    fn ff_is_zero_unsound_subset_is_sat() {
        // The 3-poly subsystem `{1 - is_zero - m*x, is_zero*m, x}`
        // over F_17 is SAT (model: x=0, is_zero=1, m=0). GB returning
        // UNSAT on this subset would be unsound.
        let pr = FfPolyRing::new(ff(17), vec!["is_zero".into(), "m".into(), "x".into()]);
        // p0 = 1 - is_zero - m*x
        let one = pr.one();
        let mx = pr.mul(pr.var(1), pr.var(2));
        let p0 = pr.sub(pr.sub(one, pr.var(0)), mx);
        // p1 = is_zero * m
        let p1 = pr.mul(pr.var(0), pr.var(1));
        // p2 = x
        let p2 = pr.clone_poly(&pr.var(2));
        match solve_split_gb(&pr, &[p0, p1, p2], &[]) {
            SolveOutcome::Sat(m) => {
                assert_eq!(m["x"], BigUint::from(0u32));
                assert_eq!(m["is_zero"], BigUint::from(1u32));
                assert_eq!(m["m"], BigUint::from(0u32));
            }
            other => panic!("expected SAT, got {:?}", other),
        }
    }

    #[test]
    fn bit_prop_derived_unsat_core_includes_bit_constraints() {
        // Inputs:
        //   p0: x*(x-1) = 0   (bit constraint on x)
        //   p1: y*(y-1) = 0   (bit constraint on y)
        //   p2: x + 2*y - 5 = 0   (bitsum saying x + 2y = 5)
        // With x, y ∈ {0,1} the max of x + 2y is 3, so the system is
        // UNSAT and the UNSAT core must include p0 and p1 (otherwise
        // dropping a bit constraint produces a SAT subset, e.g. p0+p2
        // alone is satisfied by x=5, y=0 in F_7).
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let x = pr.var(0);
        let y = pr.var(1);
        let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let p0 = pr.sub(xx, pr.clone_poly(&x));
        let yy = pr.mul(pr.clone_poly(&y), pr.clone_poly(&y));
        let p1 = pr.sub(yy, pr.clone_poly(&y));
        let two = pr.field().from_int(2);
        let five = pr.field().from_int(5);
        let two_y = pr.scale(two, pr.clone_poly(&y));
        let sum = pr.add(pr.clone_poly(&x), two_y);
        let p2 = pr.sub(sum, pr.constant(five));
        match solve_split_gb(&pr, &[p0, p1, p2], &[]) {
            SolveOutcome::Unsat(core) => {
                assert!(
                    core.contains(&0) && core.contains(&1),
                    "core must include both bit constraints (p0, p1); got {:?}",
                    core
                );
            }
            other => panic!("expected UNSAT, got {:?}", other),
        }
    }

    #[test]
    fn bit_prop_derived_eq_unsat_core_is_sound() {
        // Inputs:
        //   p0: x*(x-1) = 0           (bit constraint on x)
        //   p1: y*(y-1) = 0           (bit constraint on y)
        //   p2: x + 2*y - 1 = 0       (bitsum saying x + 2y = 1 ⇒ x=1, y=0)
        //   p3: y - 1 = 0             (asserts y = 1)
        // Without p0 ∧ p1 the bitsum doesn't fire and {p2, p3}
        // has a SAT model (e.g. x=6, y=1 in F_7). UNSAT only when
        // all four constraints participate, so the core must
        // include every index.
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let x = pr.var(0);
        let y = pr.var(1);
        let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let p0 = pr.sub(xx, pr.clone_poly(&x));
        let yy = pr.mul(pr.clone_poly(&y), pr.clone_poly(&y));
        let p1 = pr.sub(yy, pr.clone_poly(&y));
        let two = pr.field().from_int(2);
        let one = pr.field().from_int(1);
        let two_y = pr.scale(two, pr.clone_poly(&y));
        let sum = pr.add(pr.clone_poly(&x), two_y);
        let p2 = pr.sub(sum, pr.constant(one.clone()));
        let p3 = pr.sub(pr.clone_poly(&y), pr.constant(one));
        match solve_split_gb(&pr, &[p0, p1, p2, p3], &[]) {
            SolveOutcome::Unsat(core) => {
                assert!(
                    core.contains(&0) && core.contains(&1),
                    "core must include both bit constraints (p0, p1); got {:?}",
                    core
                );
                assert!(
                    core.contains(&2),
                    "core must include bitsum p2; got {:?}",
                    core
                );
                assert!(
                    core.contains(&3),
                    "core must include p3 (y=1); got {:?}",
                    core
                );
            }
            other => panic!("expected UNSAT, got {:?}", other),
        }
    }

    #[test]
    fn ff_is_zero_unsound_full_unsat_core_is_sound() {
        // 4-poly system over F_17 that arises during the
        // `cvc5_ff_is_zero_unsound_sat` post_check trail:
        //   p0: 1 - is_zero - m*x = 0
        //   p1: is_zero * m = 0
        //   p2: x = 0
        //   p3: is_zero = 0
        // `{p0, p2, p3}` is the minimum UNSAT subset; dropping p3
        // leaves a SAT subset, so the returned core must name p3.
        let pr = FfPolyRing::new(ff(17), vec!["is_zero".into(), "m".into(), "x".into()]);
        let one = pr.one();
        let mx = pr.mul(pr.var(1), pr.var(2));
        let p0 = pr.sub(pr.sub(one, pr.var(0)), mx);
        let p1 = pr.mul(pr.var(0), pr.var(1));
        let p2 = pr.clone_poly(&pr.var(2));
        let p3 = pr.clone_poly(&pr.var(0));
        match solve_split_gb(&pr, &[p0, p1, p2, p3], &[]) {
            SolveOutcome::Unsat(core) => {
                assert!(
                    core.contains(&3),
                    "core must include is_zero=0 (index 3); got {:?}",
                    core
                );
            }
            other => panic!("expected UNSAT, got {:?}", other),
        }
    }
}
