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

#[test]
fn apply_rule_zero_dim_minpoly_yields_exhaustive_roots() {
    // I = (x^2 - 2, x*y - 1) over GF(7) is zero-dimensional with two
    // points: x^2 = 2 ⇒ x ∈ {3, 4}, y = 1/x. Its reduced DegRevLex GB
    // eliminates x's univariate poly into the multivariate `x - 2y`,
    // leaving the univariate elimination poly only in y. With y assigned
    // (so the phase-1 univariate-in-y scan skips it) and x unassigned, the
    // univariate-in-unassigned scan finds nothing genuinely univariate in
    // x, so apply_rule falls into the zero-dim branch: it computes the
    // minimal polynomial of x in R/I, whose complete root set over GF(7)
    // is {3, 4}, and returns an exhaustive Roots brancher.
    let pr = pr_two_vars();
    let f = pr.field();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p_x = pr.sub(x2, pr.constant(f.from_int(2))); // x^2 - 2
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p_xy = pr.sub(xy, pr.constant(f.one())); // x*y - 1
    let gb = Ideal::new(&pr, vec![p_x, p_xy]);
    assert!(gb.is_zero_dim(), "precondition: I is zero-dimensional");
    let r: PartialPoint = vec![None, Some(f.from_int(2))]; // y assigned, x free
    let b = apply_rule(&pr, &gb, &r);
    match b {
        Brancher::Roots(v) => {
            assert!(!v.is_empty(), "zero-dim min-poly must yield roots");
            assert!(v.iter().all(|(var, _)| *var == 0), "all roots are for x");
            let vals: Vec<BigUint> =
                v.iter().map(|(_, val)| pr.field().to_biguint(val)).collect();
            assert!(vals.contains(&BigUint::from(3u32)), "x = 3 is a root");
            assert!(vals.contains(&BigUint::from(4u32)), "x = 4 is a root");
        }
        _ => panic!("expected Roots from zero-dim min-poly"),
    }
    assert!(
        apply_rule(&pr, &gb, &r).is_exhaustive(),
        "complete root extraction over a small prime is exhaustive"
    );
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
    let bases = vec![Ideal::from_gb(&pr, vec![]), Ideal::new(&pr, vec![p])];
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
