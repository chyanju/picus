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

use std::collections::HashMap;

use crate::brancher::Brancher;
use crate::field::FfEl;
use crate::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};

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
    let field = &poly_ring.field;

    // (1) univariate polynomial in an unassigned variable
    for p in &gb.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, _) = appearing[0];
            if r[var_idx].is_none() {
                if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                    let roots = crate::roots::find_roots(field, &coeffs);
                    return Brancher::Roots(
                        roots.into_iter().map(|v| (var_idx, v)).collect()
                    );
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
                    // If roots is empty, the ideal is inconsistent under
                    // any assignment to this variable — return empty to
                    // trigger backtracking.
                    return Brancher::Roots(
                        roots.into_iter().map(|val| (v, val)).collect()
                    );
                }
            }
        }
    }

    // (3) round-robin: lazy enumeration.
    let unassigned: Vec<usize> = (0..poly_ring.n_vars).filter(|i| r[*i].is_none()).collect();
    if unassigned.is_empty() {
        return Brancher::Roots(Vec::new());
    }

    let prime = field.prime();
    // No per-variable cap: the count is the field size (saturated to
    // `u64::MAX` for primes larger than 64 bits). Termination on large
    // primes relies on the cancel token / caller timeout.
    let exhaustive = prime.bits() <= 16;
    let per_var: u64 = if exhaustive {
        let x = prime.iter_u64_digits().next().unwrap_or(2);
        x.max(2)
    } else {
        u64::MAX
    };
    let total = per_var.saturating_mul(unassigned.len() as u64);

    Brancher::RoundRobin {
        unassigned,
        idx: 0,
        total,
        exhaustive,
    }
}

/// Like [`apply_rule`] but checks every basis for univariate / zero-dim
/// structure. The detected branching structure is mathematically valid
/// in any of the bases.
pub(super) fn apply_rule_multi<'r>(
    poly_ring: &'r FfPolyRing,
    bases: &[Ideal<'r>],
    r: &PartialPoint,
) -> Brancher {
    let _t = crate::profile::ScopedTimer::new("apply_rule_multi");
    let ring = &poly_ring.ring;
    let field = &poly_ring.field;

    // (1) Check all bases for a univariate polynomial in an unassigned
    // variable.
    for gb in bases {
        for p in &gb.basis {
            let appearing = ring.appearing_indeterminates(p);
            if appearing.len() == 1 {
                let (var_idx, _) = appearing[0];
                if r[var_idx].is_none() {
                    if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                        let roots = crate::roots::find_roots(field, &coeffs);
                        return Brancher::Roots(
                            roots.into_iter().map(|v| (var_idx, v)).collect()
                        );
                    }
                }
            }
        }
    }

    // (2) Check all bases for a zero-dimensional ideal → minimal polynomial.
    for gb in bases {
        if gb.is_zero_dim() {
            for v in 0..poly_ring.n_vars {
                if r[v].is_none() {
                    if let Some(coeffs) = gb.min_poly(v) {
                        let roots = crate::roots::find_roots(field, &coeffs);
                        return Brancher::Roots(
                            roots.into_iter().map(|val| (v, val)).collect()
                        );
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

/// Extract univariate coefficients (assumes only `var_idx` appears in `p`).
fn univariate_coeffs(
    poly_ring: &FfPolyRing,
    p: &Poly,
    var_idx: usize,
) -> Option<Vec<FfEl>> {
    let ring = &poly_ring.ring;
    let fp = &poly_ring.field;
    let appearing = ring.appearing_indeterminates(p);
    for (v, _) in &appearing {
        if *v != var_idx { return None; }
    }
    let mut coeffs: HashMap<usize, FfEl> = HashMap::new();
    let mut max_deg = 0usize;
    for (c, m) in ring.terms(p) {
        let d = ring.exponent_at(&m, var_idx);
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
