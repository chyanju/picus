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

use crate::gb::brancher::{univariate_coeffs, Brancher};
use crate::ff::field::{PrimeField, FieldElem};
use crate::gb::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::gb::roots::{find_roots, find_roots_checked};
use crate::timeout::CancelToken;

/// Three-valued outcome of a model search.
///
/// `Unknown` means the search exhausted its bounded round-robin cap on
/// a large prime field; the formula may still be SAT outside the
/// searched range.  Callers must NOT treat `Unknown` as UNSAT.
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
    // Fast path (cvc5 `multi_roots` style): for a zero-dimensional ideal
    // the Lex GB is triangular, so a model can be built by univariate
    // root-finding + substitution + backtracking, without recomputing a
    // Gröbner basis at every branch (the general loop below does). The
    // fast path is self-verifying — it returns only a model it has
    // checked against the GB — so a miss is sound: fall through to the
    // general augmentation search.
    if let Some(model) = try_triangular_solve(poly_ring, initial_gb, cancel) {
        return FindZeroOutcome::Sat(model);
    }

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
        if let Some((var, val)) = brancher.next(&poly_ring.field()) {
            // Add x_var - val to the ideal generators
            let v = poly_ring.var(var);
            let c = poly_ring.constant(poly_ring.field().clone_el(&val));
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

/// Triangular model construction for a zero-dimensional ideal (cvc5
/// `multi_roots` style): solve variable-by-variable using univariate roots
/// of the substituted GB, backtracking on infeasible roots, **without**
/// recomputing a Gröbner basis per branch. Returns a model already
/// verified against `gb`, or `None` if the ideal is not zero-dimensional,
/// no triangular structure is found, or the search exhausts without a
/// model — in which case the caller runs the general augmentation search.
fn try_triangular_solve(
    poly_ring: &FfPolyRing,
    gb: &[Poly],
    cancel: &CancelToken,
) -> Option<HashMap<String, BigUint>> {
    let ideal = Ideal::from_gb(
        poly_ring,
        gb.iter().map(|p| poly_ring.ring.clone_el(p)).collect(),
    );
    if !ideal.is_zero_dim() {
        return None;
    }
    let gb_polys: Vec<Poly> = gb.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
    let mut assignment: HashMap<usize, FieldElem> = HashMap::new();
    if tri_dfs(poly_ring, &gb_polys, &mut assignment, cancel) {
        let model = build_model(&poly_ring.field(), poly_ring, &assignment);
        if verify_model(poly_ring, gb, &model) {
            return Some(model);
        }
    }
    None
}

/// Depth-first triangular search: substitute the partial assignment into
/// the GB (reduce by `{x_i − v_i}`), pick an unassigned variable that has
/// become univariate, try each of its roots, recurse. A nonzero-constant
/// residue means the branch is infeasible.
fn tri_dfs(
    poly_ring: &FfPolyRing,
    gb_polys: &[Poly],
    assignment: &mut HashMap<usize, FieldElem>,
    cancel: &CancelToken,
) -> bool {
    if cancel.is_cancelled() {
        return false;
    }
    if assignment.len() == poly_ring.n_vars() {
        return true;
    }
    let assign_polys: Vec<Poly> = assignment
        .iter()
        .map(|(&v, val)| {
            poly_ring.sub(poly_ring.var(v), poly_ring.constant(poly_ring.field().clone_el(val)))
        })
        .collect();
    let ctx = poly_ring.ctx();
    let subst: Vec<Poly> = gb_polys
        .iter()
        .map(|p| {
            if assign_polys.is_empty() {
                poly_ring.ring.clone_el(p)
            } else {
                p.reduce_by(&assign_polys, ctx)
            }
        })
        .collect();
    let mut chosen: Option<(usize, Vec<FieldElem>)> = None;
    for p in &subst {
        if poly_ring.is_zero(p) {
            continue;
        }
        let appearing = poly_ring.ring.appearing_indeterminates(p);
        if appearing.is_empty() {
            return false; // nonzero constant ⇒ infeasible branch
        }
        if appearing.len() == 1 {
            let (v, _) = appearing.get(0);
            if !assignment.contains_key(&v) {
                if let Some(coeffs) = univariate_coeffs(poly_ring, p, v) {
                    chosen = Some((v, coeffs));
                    break;
                }
            }
        }
    }
    let (v, coeffs) = match chosen {
        Some(c) => c,
        None => return false, // no triangular structure → caller falls back
    };
    for r in find_roots(&poly_ring.field(), &coeffs) {
        assignment.insert(v, r);
        if tri_dfs(poly_ring, gb_polys, assignment, cancel) {
            return true;
        }
        assignment.remove(&v);
    }
    false
}

/// Try to extract a complete assignment from the GB.
/// Returns Some(model) if every variable has a linear assignment `x_i = c`
/// in the basis.
fn try_extract_full_assignment(
    poly_ring: &FfPolyRing,
    ideal: &Ideal,
) -> Option<HashMap<String, BigUint>> {
    let ring = &poly_ring.ring;
    let fp = &poly_ring.field();
    let n_vars = poly_ring.n_vars();
    let mut assignment: HashMap<usize, FieldElem> = HashMap::new();

    for p in &ideal.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, max_deg) = appearing[0];
            if max_deg == 1 {
                if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                    if coeffs.len() == 2 && !fp.is_zero(&coeffs[1]) {
                        let val = fp.negate(fp.div(&coeffs[0], &coeffs[1]).expect("nonzero divisor"));
                        assignment.entry(var_idx).or_insert(val);
                    }
                }
            }
        }
    }

    if assignment.len() == n_vars {
        Some(build_model(&poly_ring.field(), poly_ring, &assignment))
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
    let field = &poly_ring.field();
    let n_vars = poly_ring.n_vars();

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
                if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                    if coeffs.len() > 2 { // deg > 1
                        let (roots, complete) = find_roots_checked(field, &coeffs);
                        if complete {
                            return Brancher::Roots(
                                roots.into_iter().map(|v| (var_idx, v)).collect()
                            );
                        }
                        // Incomplete root extraction: fall through to the
                        // non-exhaustive round-robin brancher rather than
                        // trust a partial set as exhaustive (unsound UNSAT).
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
                    let (roots, complete) = find_roots_checked(field, &coeffs);
                    if complete {
                        return Brancher::Roots(
                            roots.into_iter().map(|val| (v, val)).collect()
                        );
                    }
                    // Incomplete: fall through to round-robin.
                }
            }
        }
    }

    // Case 3: round-robin — lazy generation
    let unassigned: Vec<usize> = (0..n_vars).filter(|i| !assigned[*i]).collect();
    if unassigned.is_empty() {
        return Brancher::Roots(Vec::new());
    }
    Brancher::round_robin(unassigned, field.prime())
}

// Univariate coefficient extraction is shared with the split-GB DFS via
// `gb::brancher::univariate_coeffs`.

/// Build output model from assignment.
fn build_model(
    field: &PrimeField,
    poly_ring: &FfPolyRing,
    assignment: &HashMap<usize, FieldElem>,
) -> HashMap<String, BigUint> {
    let mut model = HashMap::new();
    for (&idx, val) in assignment {
        if idx < poly_ring.var_names().len() {
            model.insert(poly_ring.var_names()[idx].clone(), field.to_biguint(val));
        }
    }
    model
}

/// Verify that an assignment satisfies all polynomials.
///
/// The model must assign every variable appearing in `polys`. A variable
/// missing from the model is treated as "not verified" (returns `false`)
/// rather than defaulted to a value, so an incomplete model cannot
/// vacuously pass this check — this function is the soundness backstop for
/// SAT verdicts, so it fails closed. Current callers always pass a complete
/// assignment over every ring variable.
pub fn verify_model(
    poly_ring: &FfPolyRing,
    polys: &[Poly],
    model: &HashMap<String, BigUint>,
) -> bool {
    let ring = &poly_ring.ring;
    let fp = &poly_ring.field();

    for p in polys {
        let mut val = fp.zero();
        for (c, m) in ring.terms(p) {
            let mut term_val = fp.clone_el(c);
            for v in 0..poly_ring.n_vars() {
                let e = ring.exponent_at(&m, v);
                if e > 0 {
                    let var_name = &poly_ring.var_names()[v];
                    let var_val = match model.get(var_name) {
                        Some(bv) => poly_ring.field().from_biguint(bv),
                        // Fail closed: an appearing variable absent from the
                        // model means the model is incomplete, so we cannot
                        // confirm it satisfies the system. Reject rather than
                        // assume 0 (which could vacuously pass a narrow check).
                        None => {
                            log::warn!(
                                "verify_model: variable {} missing from model; \
                                 treating as unverified",
                                var_name
                            );
                            return false;
                        }
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
        let ff = PrimeField::new(BigUint::from(17u32));
        let pr = FfPolyRing::new(ff, vec!["x".into(), "y".into()]);

        let three = pr.field().from_biguint(&BigUint::from(3u32));
        let five = pr.field().from_biguint(&BigUint::from(5u32));

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
        let ff = PrimeField::new(BigUint::from(17u32));
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
        let ff = PrimeField::new(BigUint::from(17u32));
        let pr = FfPolyRing::new(ff, vec!["x".into()]);

        let p1 = pr.var(0);
        let p2 = pr.sub(pr.var(0), pr.one());

        assert!(matches!(find_zero(&pr, &[p1, p2]), FindZeroOutcome::Unsat));
    }

    #[test]
    fn test_find_zero_triangular_three_vars() {
        // GF(13), zero-dimensional: x^2 - 1, y - x*?, z - ...; use a
        // triangular shape <z^2 - 3, y - z, x - z - 1>. find_zero's
        // triangular fast path must produce a model satisfying all polys.
        let ff = PrimeField::new(BigUint::from(13u32));
        let pr = FfPolyRing::new(ff, vec!["x".into(), "y".into(), "z".into()]);
        let three = pr.field().from_int(3);
        let z2 = pr.mul(pr.var(2), pr.var(2));
        let p0 = pr.sub(z2, pr.constant(three)); // z^2 = 3
        let p1 = pr.sub(pr.var(1), pr.var(2)); // y = z
        let p2 = pr.sub(pr.sub(pr.var(0), pr.var(2)), pr.one()); // x = z + 1
        let model = match find_zero(&pr, &[p0, p1, p2]) {
            FindZeroOutcome::Sat(m) => m,
            other => panic!("expected Sat, got {:?}", other),
        };
        // Verify against the original system.
        assert!(verify_model(&pr, &[
            pr.sub(pr.mul(pr.var(2), pr.var(2)), pr.constant(pr.field().from_int(3))),
            pr.sub(pr.var(1), pr.var(2)),
            pr.sub(pr.sub(pr.var(0), pr.var(2)), pr.one()),
        ], &model));
        let z = &model["z"];
        assert_eq!((z * z) % BigUint::from(13u32), BigUint::from(3u32));
        assert_eq!(model["y"], *z);
    }

    #[test]
    fn test_find_zero_inverse() {
        // x*y = 1 over GF(7) → model where x*y ≡ 1 mod 7
        let ff = PrimeField::new(BigUint::from(7u32));
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

