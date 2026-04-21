//! Split Groebner Basis solver.
//!
//! Implements the algorithm from "Split Groebner Bases for Satisfiability
//! Modulo Finite Fields" (Ozdemir et al., CAV 2023).  Mirrors cvc5's
//! `theory/ff/split_gb.{h,cpp}`.
//!
//! The idea: instead of one big GB over all polynomials, maintain `k` GBs
//! over disjoint subsets, sharing only "small" polynomials between them.
//! The default split is into two ideals:
//!
//!   - **ideal 0** ("linear"):    accepts all polynomials with `deg <= 1`.
//!   - **ideal 1** ("nonlinear"): accepts polynomials with `deg <= 1` and
//!                                `numTerms <= 2` (binomial linear only).
//!
//! `splitGb` computes a fixpoint: each round it (a) adds new generators to
//! each ideal, (b) recomputes each ideal's GB, (c) extracts polynomials that
//! cross the admission boundary and (d) propagates them, including new
//! BitProp-derived equalities.

use std::collections::HashMap;

use feanor_math::ring::*;
use feanor_math::rings::multivariate::*;

use crate::bitprop::BitProp;
use crate::field::FfEl;
use crate::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::{CancelToken, Cancelled};

/// A split Groebner basis: one `Ideal` per partition.
pub type SplitGb<'r> = Vec<Ideal<'r>>;

/// Default split-admission predicate (matches cvc5's `admit`).
///
/// cvc5's `split_gb.cpp:245-249`:
///   `admit(i, p) = deg(p) <= 1 && (i == 0 || numTerms(p) <= 2)`
///
///   - basis 0 (linear):    admits `p` iff `deg(p) <= 1`.
///   - basis 1 (nonlinear): admits `p` iff `deg(p) <= 1` and `numTerms(p) <= 2`.
///   - any other index: never admit.
pub fn admit(pr: &FfPolyRing, idx: usize, p: &Poly) -> bool {
    let ring = &pr.ring;
    let d = total_degree(ring, p);
    if d > 1 { return false; }
    match idx {
        0 => true,
        1 => num_terms(ring, p) <= 2,
        _ => false,
    }
}

/// Total degree of a polynomial.
pub fn total_degree(ring: &crate::poly::PolyRingType, p: &Poly) -> usize {
    let mut max_d = 0usize;
    let n_vars = ring.indeterminate_count();
    for (_, m) in ring.terms(p) {
        let mut d = 0usize;
        for v in 0..n_vars {
            d += ring.exponent_at(m, v);
        }
        if d > max_d { max_d = d; }
    }
    max_d
}

/// Number of terms in a polynomial.
pub fn num_terms(ring: &crate::poly::PolyRingType, p: &Poly) -> usize {
    ring.terms(p).count()
}

/// Compute a split GB.  See cvc5's `splitGb`.
///
/// `generator_sets[i]` is the initial generator set for ideal `i`.
/// The function mutates `bit_prop` (used for propagation across bases).
pub fn split_gb<'r>(
    poly_ring: &'r FfPolyRing,
    generator_sets: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
) -> SplitGb<'r> {
    let k = generator_sets.len();
    split_gb_cancel(poly_ring, generator_sets, bit_prop, &CancelToken::none())
        .unwrap_or_else(|_| {
            (0..k).map(|_| Ideal::from_gb(poly_ring, Vec::new())).collect()
        })
}

/// Cancel-aware split GB computation.
pub fn split_gb_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    generator_sets: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<SplitGb<'r>, Cancelled> {
    let k = generator_sets.len();
    let mut new_polys: Vec<Vec<Poly>> = generator_sets;
    let mut split_basis: SplitGb<'r> = (0..k)
        .map(|_| Ideal::from_gb(poly_ring, Vec::new()))
        .collect();

    loop {
        if cancel.is_cancelled() { return Err(Cancelled); }

        // Add new polys to each basis & recompute GB.
        for i in 0..k {
            if !new_polys[i].is_empty() {
                let mut combined: Vec<Poly> = Vec::new();
                for q in split_basis[i].basis.iter() {
                    combined.push(poly_ring.ring.clone_el(q));
                }
                combined.append(&mut new_polys[i]);
                split_basis[i] = Ideal::new_with_cancel(poly_ring, combined, cancel)?;
            }
        }

        if split_basis.iter().any(|b| b.is_whole_ring()) {
            break;
        }

        let mut to_propagate = bit_prop.get_bit_equalities(&split_basis);
        for b in &split_basis {
            for p in &b.basis {
                to_propagate.push(poly_ring.ring.clone_el(p));
            }
        }

        let mut any_new = false;
        for p in &to_propagate {
            for j in 0..k {
                if admit(poly_ring, j, p) && !split_basis[j].contains(p) {
                    new_polys[j].push(poly_ring.ring.clone_el(p));
                    any_new = true;
                }
            }
        }

        if !any_new { break; }
    }

    Ok(split_basis)
}

/// A partial assignment of variable indices to field values.
pub type PartialPoint = Vec<Option<FfEl>>;

/// Result of the recursive `split_zero_extend`.
pub enum ZeroExtendResult {
    /// A complete assignment was found.
    Point(Vec<FfEl>),
    /// A conflict polynomial: not in `bases[0]` but evaluates to non-zero
    /// under the partial assignment.
    Conflict(Poly),
    /// No common zeros exist that extend the current partial assignment.
    NoZero,
}

/// Build a polynomial of the form `x_var - val`.
fn assignment_poly(pr: &FfPolyRing, var: usize, val: &FfEl) -> Poly {
    let v = pr.var(var);
    let c = pr.constant(pr.field.field().clone_el(val));
    pr.sub(v, c)
}

/// Substitute the partial assignment into a polynomial and check if it's zero.
/// Returns Some(value) if all variables in `p` are assigned (so we can fully
/// evaluate); else None.
fn evaluate_full(pr: &FfPolyRing, p: &Poly, r: &PartialPoint) -> Option<FfEl> {
    let ring = &pr.ring;
    let fp = pr.field.field();
    let mut acc = fp.zero();
    for (c, m) in ring.terms(p) {
        let mut term_val = fp.clone_el(c);
        for v in 0..pr.n_vars {
            let e = ring.exponent_at(m, v);
            if e == 0 { continue; }
            match &r[v] {
                None => return None,
                Some(val) => {
                    for _ in 0..e {
                        term_val = fp.mul_ref(&term_val, val);
                    }
                }
            }
        }
        fp.add_assign(&mut acc, term_val);
    }
    Some(acc)
}

/// Try to extend `cur_r` into a complete zero of the ideal whose generators
/// are `orig_polys`.  Mirrors cvc5's `splitZeroExtend`.
pub fn split_zero_extend<'r>(
    poly_ring: &'r FfPolyRing,
    orig_polys: &[Poly],
    cur_bases: SplitGb<'r>,
    cur_r: PartialPoint,
    bit_prop: &mut BitProp<'r>,
) -> ZeroExtendResult {
    split_zero_extend_cancel(poly_ring, orig_polys, cur_bases, cur_r, bit_prop, &CancelToken::none())
}

/// Cancel-aware version of `split_zero_extend`.
pub fn split_zero_extend_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    orig_polys: &[Poly],
    cur_bases: SplitGb<'r>,
    cur_r: PartialPoint,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> ZeroExtendResult {
    if cancel.is_cancelled() { return ZeroExtendResult::NoZero; }

    // Whole-ring detection: if any basis is the whole ring, the partial
    // assignment is infeasible.  We need to find a conflict polynomial.
    if cur_bases.iter().any(|b| b.is_whole_ring()) {
        for p in orig_polys {
            if let Some(val) = evaluate_full(poly_ring, p, &cur_r) {
                if !poly_ring.field.is_zero(&val) && !cur_bases[0].contains(p) {
                    return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                }
            }
        }
        return ZeroExtendResult::NoZero;
    }

    let n_assigned = cur_r.iter().filter(|v| v.is_some()).count();
    if n_assigned == poly_ring.n_vars {
        let out: Vec<FfEl> = cur_r.into_iter().map(|v| v.unwrap()).collect();
        return ZeroExtendResult::Point(out);
    }

    // Apply branching rule on bases[0]
    let candidates = apply_rule(poly_ring, &cur_bases[0], &cur_r);
    for (var, val) in candidates {
        if cancel.is_cancelled() { return ZeroExtendResult::NoZero; }

        let mut new_r = cur_r.clone();
        new_r[var] = Some(poly_ring.field.field().clone_el(&val));
        let assign_poly = assignment_poly(poly_ring, var, &val);

        // Build new generator sets: each basis + the assignment polynomial
        let mut new_split_gens: Vec<Vec<Poly>> = Vec::with_capacity(cur_bases.len());
        for b in &cur_bases {
            let mut g: Vec<Poly> = b.basis.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
            g.push(poly_ring.ring.clone_el(&assign_poly));
            new_split_gens.push(g);
        }
        let new_bases = match split_gb_cancel(poly_ring, new_split_gens, bit_prop, cancel) {
            Ok(b) => b,
            Err(_) => return ZeroExtendResult::NoZero,
        };
        let result = split_zero_extend_cancel(poly_ring, orig_polys, new_bases, new_r, bit_prop, cancel);
        match result {
            ZeroExtendResult::NoZero => continue, // try next candidate
            other => return other,
        }
    }
    ZeroExtendResult::NoZero
}

/// Apply branching rule.  Returns a list of `(var_idx, value)` to try.
///
/// (1) if `gb` has a univariate polynomial in some unassigned variable,
///     enumerate its roots over GF(p);
/// (2) if `gb` is zero-dimensional, compute the minimal polynomial of an
///     unassigned variable and enumerate its roots;
/// (3) otherwise, round-robin: for each unassigned variable, try every
///     value in `0..p` (capped for large `p`).
pub fn apply_rule<'r>(
    poly_ring: &'r FfPolyRing,
    gb: &Ideal<'r>,
    r: &PartialPoint,
) -> Vec<(usize, FfEl)> {
    let ring = &poly_ring.ring;
    let field = &poly_ring.field;

    // (1) univariate polynomial in an unassigned variable
    for p in &gb.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, _) = appearing[0];
            if r[var_idx].is_none() {
                if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                    let roots = crate::roots::find_roots(field, &coeffs);
                    return roots.into_iter().map(|v| (var_idx, v)).collect();
                }
            }
        }
    }

    // (2) zero-dim: compute minimal polynomial
    if gb.is_zero_dim() {
        for v in 0..poly_ring.n_vars {
            if r[v].is_none() {
                if let Some(coeffs) = gb.min_poly(v) {
                    let roots = crate::roots::find_roots(field, &coeffs);
                    return roots.into_iter().map(|val| (v, val)).collect();
                }
            }
        }
    }

    // (3) round-robin: enumerate (var, val) ∈ unassigned_vars × Fp,
    //     iterating `idx` from 0 upward and decoding
    //         var = unassigned[idx % len], val = idx / len
    //     This matches cvc5's RoundRobinEnumerator (multi_roots.cpp:93).
    let unassigned: Vec<usize> = (0..poly_ring.n_vars).filter(|i| r[*i].is_none()).collect();
    if unassigned.is_empty() { return Vec::new(); }

    let prime = &field.prime;
    // Cap total guesses for tractability on large primes.  cvc5 has no cap,
    // but relies on the resource manager / timeout.  We cap at
    // `min(p, ROUND_ROBIN_CAP_PER_VAR) * num_vars`.
    const ROUND_ROBIN_CAP_PER_VAR: u64 = 256;
    let per_var: u64 = if prime.bits() > 16 {
        ROUND_ROBIN_CAP_PER_VAR
    } else {
        let x = prime.iter_u64_digits().next().unwrap_or(2);
        x.min(ROUND_ROBIN_CAP_PER_VAR).max(2)
    };
    let total = per_var.saturating_mul(unassigned.len() as u64);

    let mut out = Vec::with_capacity(total as usize);
    for idx in 0..total {
        let which_var = (idx as usize) % unassigned.len();
        let which_val = idx / (unassigned.len() as u64);
        let val_bi = num_bigint::BigUint::from(which_val);
        out.push((unassigned[which_var], field.from_biguint(&val_bi)));
    }
    out
}

/// Extract univariate coefficients (assumes only `var_idx` appears in `p`).
fn univariate_coeffs(
    poly_ring: &FfPolyRing,
    p: &Poly,
    var_idx: usize,
) -> Option<Vec<FfEl>> {
    let ring = &poly_ring.ring;
    let fp = poly_ring.field.field();
    let appearing = ring.appearing_indeterminates(p);
    for (v, _) in &appearing {
        if *v != var_idx { return None; }
    }
    let mut coeffs: HashMap<usize, FfEl> = HashMap::new();
    let mut max_deg = 0usize;
    for (c, m) in ring.terms(p) {
        let d = ring.exponent_at(m, var_idx);
        if d > max_deg { max_deg = d; }
        let entry = coeffs.entry(d).or_insert_with(|| fp.zero());
        fp.add_assign(entry, fp.clone_el(c));
    }
    let mut out = Vec::with_capacity(max_deg + 1);
    for d in 0..=max_deg {
        out.push(coeffs.remove(&d).unwrap_or_else(|| fp.zero()));
    }
    Some(out)
}

/// Top-level `split` routine: encode `(orig_polys, bitsums)` into a split
/// GB, run the propagation fixpoint, then `splitFindZero` to extract a
/// model.  Returns `Some(model)` for SAT, `None` for UNSAT.
pub fn split_find_zero<'r>(
    poly_ring: &'r FfPolyRing,
    split_basis: SplitGb<'r>,
    bit_prop: &mut BitProp<'r>,
) -> Option<Vec<FfEl>> {
    split_find_zero_cancel(poly_ring, split_basis, bit_prop, &CancelToken::none())
        .unwrap_or(None)
}

/// Cancel-aware model search.  Returns `Ok(Some(model))` for SAT,
/// `Ok(None)` for UNSAT, `Err(Cancelled)` on timeout.
pub fn split_find_zero_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    split_basis: SplitGb<'r>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<Option<Vec<FfEl>>, Cancelled> {
    let mut split_basis = split_basis;
    loop {
        if cancel.is_cancelled() { return Err(Cancelled); }

        let mut all_gens: Vec<Poly> = Vec::new();
        for b in &split_basis {
            for p in &b.basis {
                all_gens.push(poly_ring.ring.clone_el(p));
            }
        }
        let null_partial: PartialPoint = vec![None; poly_ring.n_vars];

        let cur_bases: SplitGb<'r> = split_basis.iter()
            .map(|b| {
                let basis_clone: Vec<Poly> = b.basis.iter()
                    .map(|p| poly_ring.ring.clone_el(p))
                    .collect();
                Ideal::from_gb(poly_ring, basis_clone)
            })
            .collect();

        let result = split_zero_extend_cancel(poly_ring, &all_gens, cur_bases, null_partial, bit_prop, cancel);
        match result {
            ZeroExtendResult::Conflict(c) => {
                let mut new_gens: Vec<Vec<Poly>> = Vec::new();
                for b in &split_basis {
                    let mut g: Vec<Poly> = b.basis.iter()
                        .map(|p| poly_ring.ring.clone_el(p)).collect();
                    g.push(poly_ring.ring.clone_el(&c));
                    new_gens.push(g);
                }
                split_basis = split_gb_cancel(poly_ring, new_gens, bit_prop, cancel)?;
            }
            ZeroExtendResult::NoZero => {
                if cancel.is_cancelled() { return Err(Cancelled); }
                return Ok(None);
            }
            ZeroExtendResult::Point(pt) => return Ok(Some(pt)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::FfField;
    use num_bigint::BigUint;

    fn ff(p: u32) -> FfField { FfField::new(&BigUint::from(p)) }

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
        let two = pr.field.from_int(2);
        let p2 = pr.sub(pr.var(0), pr.constant(two));

        let mut bp = BitProp::new(&pr);
        let gens: Vec<Vec<Poly>> = vec![vec![pr.clone_poly(&p2)], vec![p1, p2]];
        let basis = split_gb(&pr, gens, &mut bp);
        assert!(!basis.iter().any(|b| b.is_whole_ring()));
        let pt = split_find_zero(&pr, basis, &mut bp).expect("SAT");
        // Check x = 2, y = 4 (or the other valid roots; should satisfy x*y=1).
        let x_val = pr.field.to_biguint(&pt[0]);
        let y_val = pr.field.to_biguint(&pt[1]);
        assert_eq!(x_val, BigUint::from(2u32));
        let prod = (x_val * y_val) % BigUint::from(7u32);
        assert_eq!(prod, BigUint::from(1u32));
    }

    #[test]
    fn test_split_gb_unsat() {
        // x = 2, x = 3 in GF(7): UNSAT
        let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
        let two = pr.field.from_int(2);
        let three = pr.field.from_int(3);
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
        // Should fall through to round-robin.  Verify the order:
        // (x,0), (y,0), (x,1), (y,1), (x,2), (y,2), (x,3), (y,3), (x,4), (y,4).
        let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
        let gb: Ideal = Ideal::from_gb(&pr, vec![]);
        let r: PartialPoint = vec![None, None];
        let cands = apply_rule(&pr, &gb, &r);
        // first 2 candidates should be (0, 0) and (1, 0): same val, different var.
        assert_eq!(cands[0].0, 0);
        assert_eq!(pr.field.to_biguint(&cands[0].1), num_bigint::BigUint::from(0u32));
        assert_eq!(cands[1].0, 1);
        assert_eq!(pr.field.to_biguint(&cands[1].1), num_bigint::BigUint::from(0u32));
        // third candidate: var 0 again, val 1.
        assert_eq!(cands[2].0, 0);
        assert_eq!(pr.field.to_biguint(&cands[2].1), num_bigint::BigUint::from(1u32));
    }

    #[test]
    fn test_apply_rule_univariate() {
        // GB has y^2 - 4 = 0; should enumerate roots of y over GF(7) (i.e., 2 and 5).
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let four = pr.field.from_int(4);
        let y_sq = pr.mul(pr.var(1), pr.var(1));
        let p = pr.sub(y_sq, pr.constant(four));
        let gb = Ideal::new(&pr, vec![p]);
        let r: PartialPoint = vec![None, None];
        let cands = apply_rule(&pr, &gb, &r);
        // All candidates should be for variable 1 (y).
        assert!(cands.iter().all(|(v, _)| *v == 1));
        // Roots should include 2 and 5.
        let vals: Vec<num_bigint::BigUint> = cands.iter().map(|(_, v)| pr.field.to_biguint(v)).collect();
        assert!(vals.contains(&num_bigint::BigUint::from(2u32)));
        assert!(vals.contains(&num_bigint::BigUint::from(5u32)));
    }
}
