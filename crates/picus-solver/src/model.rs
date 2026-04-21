//! Model construction from a Lex Groebner basis.
//!
//! Implements `findZero` from [OKTB23]: extract variable assignments
//! from a Lex GB via back-substitution and univariate root finding.

use std::collections::HashMap;
use num_bigint::BigUint;

use feanor_math::ring::*;
use feanor_math::rings::multivariate::*;
use feanor_math::homomorphism::*;
use feanor_math::field::FieldStore;

use crate::field::{FfField, FfEl};
use crate::poly::{FfPolyRing, Poly, PolyRingType};
use crate::roots::find_roots;

/// Try to extract a model from a Lex Groebner basis.
pub fn find_zero(
    poly_ring: &FfPolyRing,
    gb: &[Poly],
) -> Option<HashMap<String, BigUint>> {
    let n_vars = poly_ring.n_vars;
    let ring = &poly_ring.ring;
    let field = &poly_ring.field;
    let fp = field.field();

    let mut assignment: HashMap<usize, FfEl> = HashMap::new();

    // Phase 1: Extract direct linear assignments (x_i - c) from GB
    for p in gb {
        if let Some((var_idx, value)) = extract_linear_assignment(ring, fp, p, n_vars) {
            assignment.entry(var_idx).or_insert(value);
        }
    }

    if assignment.len() == n_vars {
        return Some(build_model(field, poly_ring, &assignment));
    }

    // Phase 2: Iterative substitution + root finding
    for _ in 0..n_vars * 2 {
        let mut progress = false;

        for p in gb {
            let substituted = substitute_known(ring, fp, p, n_vars, &assignment);
            if ring.is_zero(&substituted) {
                continue;
            }

            // Find which unassigned variables appear
            let appearing = ring.appearing_indeterminates(&substituted);
            let unassigned: Vec<usize> = appearing.iter()
                .map(|&(idx, _)| idx)
                .filter(|idx| !assignment.contains_key(idx))
                .collect();

            if unassigned.len() == 1 {
                let var_idx = unassigned[0];
                if let Some(coeffs) = extract_univariate_coeffs(ring, fp, &substituted, var_idx, n_vars) {
                    let roots = find_roots(field, &coeffs);
                    if let Some(root) = roots.into_iter().next() {
                        assignment.insert(var_idx, root);
                        progress = true;
                    }
                }
            }
        }

        if assignment.len() == n_vars {
            return Some(build_model(field, poly_ring, &assignment));
        }
        if !progress {
            break;
        }
    }

    // Phase 3: Backtracking search for remaining unassigned variables.
    // Try small values (0, 1, 2, ...) for each unassigned variable.
    let unassigned: Vec<usize> = (0..n_vars)
        .filter(|i| !assignment.contains_key(i))
        .collect();

    if !unassigned.is_empty() {
        let max_tries_per_var = 20usize; // limit search space
        if backtrack_assign(ring, fp, field, gb, n_vars, &mut assignment, &unassigned, 0, max_tries_per_var) {
            return Some(build_model(field, poly_ring, &assignment));
        }
    }

    None
}

/// Backtracking search to assign remaining variables.
fn backtrack_assign(
    ring: &PolyRingType,
    fp: &crate::field::FfFieldType,
    field: &FfField,
    gb: &[Poly],
    n_vars: usize,
    assignment: &mut HashMap<usize, FfEl>,
    unassigned: &[usize],
    depth: usize,
    max_tries: usize,
) -> bool {
    if depth == unassigned.len() {
        return verify_assignment(ring, fp, gb, n_vars, assignment);
    }

    let var_idx = unassigned[depth];
    for val in 0..max_tries {
        let el = field.from_int(val as i32);
        assignment.insert(var_idx, el);

        // Quick partial check: do the already-assigned substitutions produce contradictions?
        if backtrack_assign(ring, fp, field, gb, n_vars, assignment, unassigned, depth + 1, max_tries) {
            return true;
        }
    }

    assignment.remove(&var_idx);
    false
}

/// Extract x_i = c from a linear univariate polynomial.
fn extract_linear_assignment(
    ring: &PolyRingType,
    fp: &crate::field::FfFieldType,
    poly: &Poly,
    n_vars: usize,
) -> Option<(usize, FfEl)> {
    let appearing = ring.appearing_indeterminates(poly);
    if appearing.len() != 1 {
        return None;
    }
    let (var_idx, max_deg) = appearing[0];
    if max_deg != 1 {
        return None;
    }

    let coeffs = extract_univariate_coeffs(ring, fp, poly, var_idx, n_vars)?;
    if coeffs.len() != 2 {
        return None;
    }

    let c0 = &coeffs[0];
    let c1 = &coeffs[1];
    if fp.is_zero(c1) {
        return None;
    }

    // x = -c0/c1
    let result = fp.negate(fp.div(c0, c1));
    Some((var_idx, result))
}

/// Extract univariate coefficients w.r.t. `var_idx`.
/// Returns None if other variables appear.
fn extract_univariate_coeffs(
    ring: &PolyRingType,
    fp: &crate::field::FfFieldType,
    poly: &Poly,
    var_idx: usize,
    _n_vars: usize,
) -> Option<Vec<FfEl>> {
    // Check only var_idx appears
    let appearing = ring.appearing_indeterminates(poly);
    for &(v, _) in &appearing {
        if v != var_idx {
            return None;
        }
    }

    // Collect coefficients by degree of var_idx
    let mut max_deg: usize = 0;
    let mut coeff_map: HashMap<usize, FfEl> = HashMap::new();

    for (coeff, monomial) in ring.terms(poly) {
        let deg = ring.exponent_at(monomial, var_idx);
        if deg > max_deg {
            max_deg = deg;
        }
        let entry = coeff_map.entry(deg).or_insert_with(|| fp.zero());
        fp.add_assign(entry, fp.clone_el(coeff));
    }

    let mut coeffs = Vec::with_capacity(max_deg + 1);
    for d in 0..=max_deg {
        coeffs.push(coeff_map.remove(&d).unwrap_or_else(|| fp.zero()));
    }

    Some(coeffs)
}

/// Substitute known values into a polynomial.
fn substitute_known(
    ring: &PolyRingType,
    fp: &crate::field::FfFieldType,
    poly: &Poly,
    _n_vars: usize,
    assignment: &HashMap<usize, FfEl>,
) -> Poly {
    // Use specialize for each assigned variable, one at a time
    let mut result = ring.clone_el(poly);
    for (&var_idx, val) in assignment {
        let val_poly = ring.inclusion().map(fp.clone_el(val));
        result = ring.specialize(&result, var_idx, &val_poly);
    }
    result
}

/// Verify that an assignment satisfies all polynomials.
fn verify_assignment(
    ring: &PolyRingType,
    fp: &crate::field::FfFieldType,
    polys: &[Poly],
    n_vars: usize,
    assignment: &HashMap<usize, FfEl>,
) -> bool {
    for p in polys {
        let substituted = substitute_known(ring, fp, p, n_vars, assignment);
        if !ring.is_zero(&substituted) {
            return false;
        }
    }
    true
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

        let model = find_zero(&pr, &[p1, p2]).unwrap();
        assert_eq!(model["x"], BigUint::from(3u32));
        assert_eq!(model["y"], BigUint::from(5u32));
    }
}
