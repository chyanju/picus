//! Branching heuristics for the split-GB DFS search.
//!
//! Two entry points:
//!
//! * [`apply_rule`] runs the three-tier branching strategy on a single
//!   ideal: (1) enumerate roots of a univariate polynomial in the basis,
//!   (2) compute and enumerate roots of a minimal polynomial if the
//!   ideal is zero-dimensional, (3) fall back to round-robin enumeration
//!   over unassigned variables.
//! * [`apply_rule_multi`] runs (1) and (2) against every basis in a
//!   [`SplitGb`] before falling back to round-robin on basis 0. Used by
//!   the search-frame branching point in [`super::search`].

use crate::gb::brancher::{univariate_coeffs, Brancher};
use crate::gb::ideal::Ideal;
use crate::metric;
use crate::poly::FfPolyRing;

use super::PartialPoint;

/// Apply branching rule on a single basis.
///
/// (1) if `gb` has a univariate polynomial in some unassigned variable,
///     enumerate its roots over GF(p);
/// (2) if `gb` is zero-dimensional, compute the minimal polynomial of an
///     unassigned variable and enumerate its roots;
/// (3) otherwise, round-robin: for each unassigned variable, try
///     values in `0..min(p, cap)` (lazily generated).
pub fn apply_rule<'r>(
    poly_ring: &'r FfPolyRing,
    gb: &Ideal<'r>,
    r: &PartialPoint,
) -> Brancher {
    let ring = &poly_ring.ring;
    let field = &poly_ring.field();

    // (1) univariate polynomial in an unassigned variable
    for p in &gb.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, _) = appearing[0];
            if r[var_idx].is_none() {
                if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                    let (roots, complete) = crate::gb::roots::find_roots_checked(field, &coeffs);
                    if complete {
                        return Brancher::Roots(
                            roots.into_iter().map(|v| (var_idx, v)).collect()
                        );
                    }
                    // Incomplete root extraction: a partial root set treated as
                    // exhaustive could prune a satisfying assignment (unsound
                    // UNSAT). Fall through to the non-exhaustive round-robin
                    // brancher (→ Unknown on large primes).
                }
            }
        }
    }

    // (2) zero-dim: compute minimal polynomial
    if gb.is_zero_dim() {
        for v in 0..poly_ring.n_vars() {
            if r[v].is_none() {
                if let Some(coeffs) = gb.min_poly(v) {
                    let (roots, complete) = crate::gb::roots::find_roots_checked(field, &coeffs);
                    // A *complete* empty root set proves the ideal inconsistent
                    // under any assignment to this variable (empty Roots ⇒
                    // backtrack). An *incomplete* set must not be trusted as
                    // exhaustive, so fall through to round-robin instead.
                    if complete {
                        return Brancher::Roots(
                            roots.into_iter().map(|val| (v, val)).collect()
                        );
                    }
                }
            }
        }
    }

    // (3) round-robin: lazy enumeration.
    let unassigned: Vec<usize> = (0..poly_ring.n_vars()).filter(|i| r[*i].is_none()).collect();
    if unassigned.is_empty() {
        return Brancher::Roots(Vec::new());
    }
    Brancher::round_robin(unassigned, field.prime())
}

/// Like [`apply_rule`] but checks every basis for univariate / zero-dim
/// structure. The detected branching structure is mathematically valid
/// in any of the bases.
#[metric]
pub(super) fn apply_rule_multi<'r>(
    poly_ring: &'r FfPolyRing,
    bases: &[Ideal<'r>],
    r: &PartialPoint,
) -> Brancher {
    let ring = &poly_ring.ring;
    let field = &poly_ring.field();

    // (1) Check all bases for a univariate polynomial in an unassigned
    // variable.
    for gb in bases {
        for p in &gb.basis {
            let appearing = ring.appearing_indeterminates(p);
            if appearing.len() == 1 {
                let (var_idx, _) = appearing[0];
                if r[var_idx].is_none() {
                    if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                        let (roots, complete) = crate::gb::roots::find_roots_checked(field, &coeffs);
                        if complete {
                            return Brancher::Roots(
                                roots.into_iter().map(|v| (var_idx, v)).collect()
                            );
                        }
                        // Incomplete: fall through rather than risk an unsound
                        // infeasible conclusion (see `apply_rule`).
                    }
                }
            }
        }
    }

    // (2) Check all bases for a zero-dimensional ideal → minimal polynomial.
    for gb in bases {
        if gb.is_zero_dim() {
            for v in 0..poly_ring.n_vars() {
                if r[v].is_none() {
                    if let Some(coeffs) = gb.min_poly(v) {
                        let (roots, complete) = crate::gb::roots::find_roots_checked(field, &coeffs);
                        if complete {
                            return Brancher::Roots(
                                roots.into_iter().map(|val| (v, val)).collect()
                            );
                        }
                        // Incomplete: fall through to round-robin (see `apply_rule`).
                    }
                }
            }
        }
    }

    // (3) Round-robin on basis 0.
    if !bases.is_empty() {
        apply_rule(poly_ring, &bases[0], r)
    } else {
        Brancher::Roots(Vec::new())
    }
}

// `univariate_coeffs` and the round-robin constructor are shared with
// `gb::model` via `gb::brancher`, so the load-bearing `exhaustive`
// predicate has a single source.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use num_bigint::BigUint;

    fn pr_one_var() -> FfPolyRing {
        FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()])
    }

    fn pr_two_vars() -> FfPolyRing {
        FfPolyRing::new(
            PrimeField::new(BigUint::from(7u32)),
            vec!["x".into(), "y".into()],
        )
    }

    // ────────── apply_rule ──────────

    #[test]
    fn apply_rule_empty_basis_yields_round_robin() {
        let pr = pr_one_var();
        let gb = Ideal::from_gb(&pr, vec![]);
        let r: PartialPoint = vec![None];
        let b = apply_rule(&pr, &gb, &r);
        assert!(matches!(b, Brancher::RoundRobin { .. }));
    }

    #[test]
    fn apply_rule_univariate_yields_roots_brancher() {
        // GB = {x^2 - 1} over GF(7): roots are ±1 = {1, 6}.
        let pr = pr_one_var();
        let f = pr.field();
        let x2 = pr.mul(pr.var(0), pr.var(0));
        let p = pr.sub(x2, pr.constant(f.one()));
        let gb = Ideal::new(&pr, vec![p]);
        let r: PartialPoint = vec![None];
        let b = apply_rule(&pr, &gb, &r);
        match b {
            Brancher::Roots(v) => assert_eq!(v.len(), 2),
            _ => panic!("expected Roots(2)"),
        }
    }

    #[test]
    fn apply_rule_all_assigned_yields_empty_roots() {
        let pr = pr_one_var();
        let f = pr.field();
        let gb = Ideal::from_gb(&pr, vec![]);
        let r: PartialPoint = vec![Some(f.from_int(3))];
        let b = apply_rule(&pr, &gb, &r);
        // No unassigned variable → empty Roots (acts as exhaustive sentinel).
        match b {
            Brancher::Roots(v) => assert!(v.is_empty()),
            _ => panic!("expected empty Roots"),
        }
    }

    #[test]
    fn apply_rule_skips_univariate_in_assigned_variable() {
        // GB has a univariate poly in x, but x is already assigned —
        // should fall through to consider other vars or round-robin.
        let pr = pr_two_vars();
        let f = pr.field();
        let p = pr.sub(pr.var(0), pr.constant(f.from_int(3))); // x = 3
        let gb = Ideal::new(&pr, vec![p]);
        let r: PartialPoint = vec![Some(f.from_int(3)), None]; // x assigned
        // Path: (1) univariate-in-unassigned skips (x is assigned); (2)
        // zero-dim → ideal might be zero-dim with x pinned; min_poly(y)
        // returns the y-coordinate's minimal poly, which is `y` alone in
        // R/(x-3), giving roots {0..p-1} → branches.
        let _b = apply_rule(&pr, &gb, &r);
        // Just exercise the path; outcome depends on zero-dim detection.
    }

    // ────────── apply_rule_multi ──────────

    #[test]
    fn apply_rule_multi_empty_bases_yields_empty_roots() {
        let pr = pr_one_var();
        let r: PartialPoint = vec![None];
        let b = apply_rule_multi(&pr, &[], &r);
        match b {
            Brancher::Roots(v) => assert!(v.is_empty()),
            _ => panic!("expected empty Roots"),
        }
    }

    #[test]
    fn apply_rule_multi_picks_univariate_across_bases() {
        // Basis 0 empty; basis 1 has a univariate poly in x.
        let pr = pr_one_var();
        let f = pr.field();
        let p = pr.sub(pr.var(0), pr.constant(f.from_int(2))); // x = 2
        let bases = vec![
            Ideal::from_gb(&pr, vec![]),
            Ideal::new(&pr, vec![p]),
        ];
        let r: PartialPoint = vec![None];
        let b = apply_rule_multi(&pr, &bases, &r);
        match b {
            Brancher::Roots(v) => {
                assert_eq!(v.len(), 1);
                let (var, val) = &v[0];
                assert_eq!(*var, 0);
                assert_eq!(pr.field().to_biguint(val), BigUint::from(2u32));
            }
            _ => panic!("expected Roots with x = 2"),
        }
    }

    #[test]
    fn apply_rule_multi_falls_back_to_round_robin_on_basis_zero() {
        let pr = pr_one_var();
        // No basis has univariate / zero-dim → round-robin on basis 0.
        let bases = vec![Ideal::from_gb(&pr, vec![])];
        let r: PartialPoint = vec![None];
        let b = apply_rule_multi(&pr, &bases, &r);
        assert!(matches!(b, Brancher::RoundRobin { .. }));
    }
}
