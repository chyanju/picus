//! Model construction from a Groebner basis.
//!
//! Implements `findZero` from [OKTB23] (Figure 5): given an ideal, find
//! a common zero of all polynomials using iterative backtracking with
//! ideal augmentation. At each branch point a variable assignment
//! `x = c` is added to the ideal and the GB is recomputed.
//!
//! Stack-based iterative search with three branching strategies:
//! univariate factoring, minimal polynomial, and round-robin
//! enumeration.

use std::collections::HashMap;
use num_bigint::BigUint;

use crate::brancher::Brancher;
use crate::field::{FfField, FfEl};
use crate::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::roots::find_roots;
use crate::timeout::CancelToken;

/// Three-valued outcome of a model search.
///
/// `Unknown` means the search exhausted its bounded round-robin cap on
/// a large prime field; the formula may still be SAT outside the range
/// we tried.  Callers must NOT treat `Unknown` as UNSAT.
#[derive(Debug)]
pub enum FindZeroOutcome {
    Sat(HashMap<String, BigUint>),
    Unsat,
    Unknown,
}

/// Try to find a common zero of the polynomials that generated `initial_gb`.
///
/// At each branch `x - val` is added to the generators and the GB is
/// recomputed. Returns `Sat(model)`, `Unsat`, or `Unknown` (when the
/// search exhausted a non-exhaustive round-robin brancher on a large
/// prime field — the formula could still have a model outside the
/// bounded range).
pub fn find_zero(
    poly_ring: &FfPolyRing,
    initial_gb: &[Poly],
) -> FindZeroOutcome {
    find_zero_cancel(poly_ring, initial_gb, &CancelToken::none())
}

/// Cancel-aware model search.
pub fn find_zero_cancel(
    poly_ring: &FfPolyRing,
    initial_gb: &[Poly],
    cancel: &CancelToken,
) -> FindZeroOutcome {
    // Build initial ideal from the provided GB
    let initial_gens: Vec<Poly> = initial_gb.iter()
        .map(|p| poly_ring.ring.clone_el(p))
        .collect();
    let initial_ideal = Ideal::new(poly_ring, initial_gens);

    // Stack-based iterative search.
    let mut ideals: Vec<Ideal> = vec![initial_ideal];
    let mut branchers: Vec<Brancher> = Vec::new();
    // True iff at least one popped brancher was a non-exhaustive
    // RoundRobin (i.e. we never enumerated its full per-variable range).
    let mut bounded_search_used = false;

    while !ideals.is_empty() {
        if cancel.is_cancelled() { return FindZeroOutcome::Unknown; }

        let ideal = ideals.last().unwrap();

        // Check UNSAT — pop the ideal only (do not pop the brancher).
        if ideal.is_whole_ring() {
            ideals.pop();
            continue;
        }

        // Check if all variables are assigned
        if let Some(model) = try_extract_full_assignment(poly_ring, ideal) {
            return FindZeroOutcome::Sat(model);
        }

        // If this ideal doesn't have a brancher yet, create one
        if ideals.len() > branchers.len() {
            let candidates = compute_candidates(poly_ring, ideal);
            branchers.push(candidates);
        }

        // ideals.len() == branchers.len() — get next candidate
        let brancher = branchers.last_mut().unwrap();
        if let Some((var, val)) = brancher.next(&poly_ring.field) {
            // Add x_var - val to the ideal generators
            let v = poly_ring.var(var);
            let c = poly_ring.constant(poly_ring.field.field().clone_el(&val));
            let assign_poly = poly_ring.sub(v, c);

            let mut new_gens: Vec<Poly> = ideals.last().unwrap().basis.iter()
                .map(|p| poly_ring.ring.clone_el(p))
                .collect();
            new_gens.push(assign_poly);
            let new_ideal = Ideal::new(poly_ring, new_gens);
            ideals.push(new_ideal);
        } else {
            // Brancher exhausted → backtrack.  If it was a non-exhaustive
            // RoundRobin, the bounded search may have missed a real model.
            if !brancher.is_exhaustive() {
                bounded_search_used = true;
            }
            branchers.pop();
            ideals.pop();
        }
    }

    if bounded_search_used {
        FindZeroOutcome::Unknown
    } else {
        FindZeroOutcome::Unsat
    }
}

/// Try to extract a complete assignment from the GB.
/// Returns Some(model) if every variable has a linear assignment `x_i = c`
/// in the basis.
fn try_extract_full_assignment(
    poly_ring: &FfPolyRing,
    ideal: &Ideal,
) -> Option<HashMap<String, BigUint>> {
    let ring = &poly_ring.ring;
    let fp = poly_ring.field.field();
    let n_vars = poly_ring.n_vars;
    let mut assignment: HashMap<usize, FfEl> = HashMap::new();

    for p in &ideal.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, max_deg) = appearing[0];
            if max_deg == 1 {
                if let Some(coeffs) = extract_univariate_coeffs(ring, fp, p, var_idx) {
                    if coeffs.len() == 2 && !fp.is_zero(&coeffs[1]) {
                        let val = fp.negate(fp.div(&coeffs[0], &coeffs[1]).expect("nonzero divisor"));
                        assignment.entry(var_idx).or_insert(val);
                    }
                }
            }
        }
    }

    if assignment.len() == n_vars {
        Some(build_model(&poly_ring.field, poly_ring, &assignment))
    } else {
        None
    }
}

/// Compute branching candidates using the same 3-case strategy as cvc5's
/// `applyRule` (and our `split_gb::apply_rule`).
fn compute_candidates(
    poly_ring: &FfPolyRing,
    ideal: &Ideal,
) -> Brancher {
    let ring = &poly_ring.ring;
    let field = &poly_ring.field;
    let n_vars = poly_ring.n_vars;

    // Determine which variables are already assigned
    let mut assigned = vec![false; n_vars];
    for p in &ideal.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, max_deg) = appearing[0];
            if max_deg == 1 {
                assigned[var_idx] = true;
            }
        }
    }

    // Case 1: univariate polynomial with deg > 1 in an unassigned variable
    for p in &ideal.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, _) = appearing[0];
            if !assigned[var_idx] {
                if let Some(coeffs) = extract_univariate_coeffs(ring, field.field(), p, var_idx) {
                    if coeffs.len() > 2 { // deg > 1
                        let roots = find_roots(field, &coeffs);
                        return Brancher::Roots(
                            roots.into_iter().map(|v| (var_idx, v)).collect()
                        );
                    }
                }
            }
        }
    }

    // Case 2: zero-dimensional ideal → minimal polynomial
    if ideal.is_zero_dim() {
        for v in 0..n_vars {
            if !assigned[v] {
                if let Some(coeffs) = ideal.min_poly(v) {
                    let roots = find_roots(field, &coeffs);
                    return Brancher::Roots(
                        roots.into_iter().map(|val| (v, val)).collect()
                    );
                }
            }
        }
    }

    // Case 3: round-robin — lazy generation
    let unassigned: Vec<usize> = (0..n_vars).filter(|i| !assigned[*i]).collect();
    if unassigned.is_empty() {
        return Brancher::Roots(Vec::new());
    }

    let prime = &field.prime;
    // Match split_gb.rs: no fixed cap. For large primes, set per_var
    // to u64::MAX; the cancel token in the DFS loop handles termination.
    let exhaustive = prime.bits() <= 16;
    let per_var: u64 = if exhaustive {
        prime.iter_u64_digits().next().unwrap_or(2).max(2)
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

/// Extract univariate coefficients w.r.t. `var_idx`.
fn extract_univariate_coeffs(
    ring: &crate::poly::PolyRingType,
    fp: &crate::field::FfFieldType,
    poly: &Poly,
    var_idx: usize,
) -> Option<Vec<FfEl>> {
    let appearing = ring.appearing_indeterminates(poly);
    for &(v, _) in &appearing {
        if v != var_idx { return None; }
    }
    let mut max_deg: usize = 0;
    let mut coeff_map: HashMap<usize, FfEl> = HashMap::new();
    for (coeff, monomial) in ring.terms(poly) {
        let deg = ring.exponent_at(&monomial, var_idx);
        if deg > max_deg { max_deg = deg; }
        let entry = coeff_map.entry(deg).or_insert_with(|| fp.zero());
        fp.add_assign(entry, fp.clone_el(coeff));
    }
    let mut coeffs = Vec::with_capacity(max_deg + 1);
    for d in 0..=max_deg {
        coeffs.push(coeff_map.remove(&d).unwrap_or_else(|| fp.zero()));
    }
    Some(coeffs)
}

/// Build output model from assignment.
fn build_model(
    field: &FfField,
    poly_ring: &FfPolyRing,
    assignment: &HashMap<usize, FfEl>,
) -> HashMap<String, BigUint> {
    let mut model = HashMap::new();
    for (&idx, val) in assignment {
        if idx < poly_ring.var_names.len() {
            model.insert(poly_ring.var_names[idx].clone(), field.to_biguint(val));
        }
    }
    model
}

/// Verify that an assignment satisfies all polynomials.
pub fn verify_model(
    poly_ring: &FfPolyRing,
    polys: &[Poly],
    model: &HashMap<String, BigUint>,
) -> bool {
    let ring = &poly_ring.ring;
    let fp = poly_ring.field.field();

    for p in polys {
        let mut val = fp.zero();
        for (c, m) in ring.terms(p) {
            let mut term_val = fp.clone_el(c);
            for v in 0..poly_ring.n_vars {
                let e = ring.exponent_at(&m, v);
                if e > 0 {
                    let var_name = &poly_ring.var_names[v];
                    let var_val = match model.get(var_name) {
                        Some(bv) => poly_ring.field.from_biguint(bv),
                        None => fp.zero(), // unassigned → 0
                    };
                    let pow = fp.pow_u64(&var_val, e as u64);
                    fp.mul_assign(&mut term_val, &pow);
                }
            }
            fp.add_assign(&mut val, term_val);
        }
        if !fp.is_zero(&val) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_zero_linear() {
        // GB: [x - 3, y - 5] over GF(17)
        let ff = FfField::new(&BigUint::from(17u32));
        let pr = FfPolyRing::new(ff, vec!["x".into(), "y".into()]);

        let three = pr.field.from_biguint(&BigUint::from(3u32));
        let five = pr.field.from_biguint(&BigUint::from(5u32));

        let p1 = pr.sub(pr.var(0), pr.constant(three));
        let p2 = pr.sub(pr.var(1), pr.constant(five));

        let model = match find_zero(&pr, &[p1, p2]) {
            FindZeroOutcome::Sat(m) => m,
            other => panic!("expected Sat, got {:?}", other),
        };
        assert_eq!(model["x"], BigUint::from(3u32));
        assert_eq!(model["y"], BigUint::from(5u32));
    }

    #[test]
    fn test_find_zero_quadratic() {
        // x^2 - 1 = 0 over GF(17) → roots 1, 16
        let ff = FfField::new(&BigUint::from(17u32));
        let pr = FfPolyRing::new(ff, vec!["x".into()]);

        let x2 = pr.mul(pr.var(0), pr.var(0));
        let p = pr.sub(x2, pr.one());

        let model = match find_zero(&pr, &[p]) {
            FindZeroOutcome::Sat(m) => m,
            other => panic!("expected Sat, got {:?}", other),
        };
        let x = &model["x"];
        let x_sq = (x * x) % BigUint::from(17u32);
        assert_eq!(x_sq, BigUint::from(1u32));
    }

    #[test]
    fn test_find_zero_unsat() {
        // x = 0 ∧ x = 1 over GF(17) → UNSAT
        let ff = FfField::new(&BigUint::from(17u32));
        let pr = FfPolyRing::new(ff, vec!["x".into()]);

        let p1 = pr.var(0);
        let p2 = pr.sub(pr.var(0), pr.one());

        assert!(matches!(find_zero(&pr, &[p1, p2]), FindZeroOutcome::Unsat));
    }

    #[test]
    fn test_find_zero_inverse() {
        // x*y = 1 over GF(7) → model where x*y ≡ 1 mod 7
        let ff = FfField::new(&BigUint::from(7u32));
        let pr = FfPolyRing::new(ff, vec!["x".into(), "y".into()]);

        let xy = pr.mul(pr.var(0), pr.var(1));
        let p = pr.sub(xy, pr.one());

        let model = match find_zero(&pr, &[p]) {
            FindZeroOutcome::Sat(m) => m,
            other => panic!("expected Sat, got {:?}", other),
        };
        let prod = (&model["x"] * &model["y"]) % BigUint::from(7u32);
        assert_eq!(prod, BigUint::from(1u32));
    }
}

