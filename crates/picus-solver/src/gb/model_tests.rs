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
    assert!(verify_model(
        &pr,
        &[
            pr.sub(
                pr.mul(pr.var(2), pr.var(2)),
                pr.constant(pr.field().from_int(3))
            ),
            pr.sub(pr.var(1), pr.var(2)),
            pr.sub(pr.sub(pr.var(0), pr.var(2)), pr.one()),
        ],
        &model
    ));
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

// ────────── verify_model edge cases ──────────

#[test]
fn verify_model_empty_polys_is_vacuous_true() {
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    let model: HashMap<String, BigUint> = HashMap::new();
    assert!(verify_model(&pr, &[], &model));
}

#[test]
fn verify_model_satisfying_assignment_returns_true() {
    // p = x - 3 with x=3.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    let p = pr.sub(pr.var(0), pr.constant(pr.field().from_int(3)));
    let mut model = HashMap::new();
    model.insert("x".into(), BigUint::from(3u32));
    assert!(verify_model(&pr, &[p], &model));
}

#[test]
fn verify_model_violating_assignment_returns_false() {
    // p = x - 3 with x=5.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    let p = pr.sub(pr.var(0), pr.constant(pr.field().from_int(3)));
    let mut model = HashMap::new();
    model.insert("x".into(), BigUint::from(5u32));
    assert!(!verify_model(&pr, &[p], &model));
}

#[test]
fn verify_model_missing_variable_fails_closed() {
    // p = x - 3 with empty model: appearing variable absent → false.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    let p = pr.sub(pr.var(0), pr.constant(pr.field().from_int(3)));
    let model: HashMap<String, BigUint> = HashMap::new();
    assert!(
        !verify_model(&pr, &[p], &model),
        "missing variable must fail closed, not vacuously pass"
    );
}

#[test]
fn verify_model_quadratic_with_correct_witness() {
    // p = x*y - 6 over GF(7); witness x=2, y=3 satisfies (6 ≡ 6 mod 7).
    let pr = FfPolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
    );
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.constant(pr.field().from_int(6)));
    let mut model = HashMap::new();
    model.insert("x".into(), BigUint::from(2u32));
    model.insert("y".into(), BigUint::from(3u32));
    assert!(verify_model(&pr, &[p], &model));
}

// ────────── find_zero_cancel ──────────

#[test]
fn find_zero_cancel_pre_cancelled_returns_unknown() {
    // Pre-cancelled token + a quadratic that needs branching: the
    // search returns Unknown without exploring.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.one()); // x^2 = 1
    let cancel = CancelToken::cancelled();
    // Either Unknown (cancel hit before any model found) or Sat
    // (triangular fast path completed before the cancel check); the
    // contract is "not panic + not Unsat".
    match find_zero_cancel(&pr, &[p], &cancel) {
        FindZeroOutcome::Unknown | FindZeroOutcome::Sat(_) => {}
        FindZeroOutcome::Unsat => panic!("cancellation must not infer Unsat"),
    }
}

// ────────── compute_candidates ──────────

/// Collect the root values a `Brancher::Roots` would enumerate for a given
/// variable, as biguints, for set comparison.
fn roots_for_var(pr: &FfPolyRing, brancher: &Brancher, var: usize) -> Vec<BigUint> {
    match brancher {
        Brancher::Roots(v) => {
            let mut out: Vec<BigUint> = v
                .iter()
                .filter(|(vi, _)| *vi == var)
                .map(|(_, val)| pr.field().to_biguint(val))
                .collect();
            out.sort();
            out
        }
        _ => panic!("expected Brancher::Roots"),
    }
}

#[test]
fn compute_candidates_all_assigned_returns_empty_roots() {
    // Every variable has a linear assignment in the basis: x - 1, y - 2
    // over GF(7). No unassigned variable remains, so compute_candidates
    // hits the empty-unassigned branch and returns Brancher::Roots([]).
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into(), "y".into()]);
    let bx = pr.sub(pr.var(0), pr.constant(pr.field().from_int(1)));
    let by = pr.sub(pr.var(1), pr.constant(pr.field().from_int(2)));
    let ideal = Ideal::from_gb(&pr, vec![bx, by]);
    let brancher = compute_candidates(&pr, &ideal);
    match brancher {
        Brancher::Roots(v) => assert!(v.is_empty(), "all-assigned ⇒ no candidates"),
        _ => panic!("expected Brancher::Roots([])"),
    }
}

#[test]
fn compute_candidates_case1_univariate_cubic_returns_all_roots() {
    // Case 1: a univariate polynomial of degree > 1 in an unassigned
    // variable. x^3 - 1 over GF(7) has the three cube roots of unity
    // {1, 2, 4} (1^3=1, 2^3=8≡1, 4^3=64≡1). Cantor–Zassenhaus is
    // complete over the prime field, so the brancher carries all three.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()]);
    let x3 = pr.mul(pr.mul(pr.var(0), pr.var(0)), pr.var(0));
    let p = pr.sub(x3, pr.one());
    let ideal = Ideal::from_gb(&pr, vec![p]);
    let brancher = compute_candidates(&pr, &ideal);
    assert_eq!(
        roots_for_var(&pr, &brancher, 0),
        vec![BigUint::from(1u32), BigUint::from(2u32), BigUint::from(4u32)],
    );
}

#[test]
fn compute_candidates_case1_skips_assigned_variable() {
    // y is pinned linearly (y - 2); the only candidate-bearing element is
    // the univariate cubic in x. The assigned-variable marking must keep
    // y out of the brancher, and Case 1 fires for x.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into(), "y".into()]);
    let x3 = pr.mul(pr.mul(pr.var(0), pr.var(0)), pr.var(0));
    let px = pr.sub(x3, pr.one()); // x^3 = 1 → {1,2,4}
    let py = pr.sub(pr.var(1), pr.constant(pr.field().from_int(2)));
    let ideal = Ideal::from_gb(&pr, vec![px, py]);
    let brancher = compute_candidates(&pr, &ideal);
    // No candidate ever names the assigned variable y.
    assert!(
        roots_for_var(&pr, &brancher, 1).is_empty(),
        "assigned variable must not appear in candidates"
    );
    assert_eq!(
        roots_for_var(&pr, &brancher, 0),
        vec![BigUint::from(1u32), BigUint::from(2u32), BigUint::from(4u32)],
    );
}

// ────────── tri_dfs / try_triangular_solve ──────────

#[test]
fn try_triangular_solve_rejects_positive_dimensional() {
    // <x*y - 1> over GF(7) is positive-dimensional (a curve), so the
    // triangular fast path declines and returns None — the caller then
    // runs the general augmentation search.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into(), "y".into()]);
    let p = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let gb = vec![p];
    assert!(try_triangular_solve(&pr, &gb, &CancelToken::none()).is_none());
}

#[test]
fn tri_dfs_solves_chained_substitution() {
    // Triangular zero-dim GB over GF(13): z^2 = 4, y = z + 1, x = z + 1.
    // tri_dfs picks z (univariate before any substitution), assigns a
    // root, then substitution makes y and x univariate in turn —
    // exercising the "intermediate assignment unlocks a new univariate"
    // branch. z^2 = 4 has roots {2, 11} mod 13.
    let pr = FfPolyRing::new(
        PrimeField::new(BigUint::from(13u32)),
        vec!["x".into(), "y".into(), "z".into()],
    );
    let z2 = pr.mul(pr.var(2), pr.var(2));
    let p0 = pr.sub(z2, pr.constant(pr.field().from_int(4))); // z^2 = 4 → z ∈ {2, 11}
    let p1 = pr.sub(pr.var(1), pr.add(pr.var(2), pr.one())); // y = z + 1
    let p2 = pr.sub(pr.sub(pr.var(0), pr.var(2)), pr.one()); // x = z + 1
    let gb = vec![
        pr.ring.clone_el(&p0),
        pr.ring.clone_el(&p1),
        pr.ring.clone_el(&p2),
    ];
    let model = try_triangular_solve(&pr, &gb, &CancelToken::none())
        .expect("triangular zero-dim system must solve");
    // The returned model is self-verified against the GB.
    assert!(verify_model(&pr, &[p0, p1, p2], &model));
    let z = &model["z"];
    assert_eq!((z * z) % BigUint::from(13u32), BigUint::from(4u32));
    // y = z + 1 and x = z + 1 (mod 13).
    let expected = (z + BigUint::from(1u32)) % BigUint::from(13u32);
    assert_eq!(model["y"], expected);
    assert_eq!(model["x"], expected);
}

#[test]
fn tri_dfs_rejects_every_root_then_backtracks_to_none() {
    // GF(7), one var z. z^2 - 4 → z ∈ {2, 5}; z - 3 contradicts both roots.
    // tri_dfs picks z from the degree-2 poly (two roots), and for EACH root
    // the substituted (z - 3) reduces to a nonzero constant (2-3 = -1, 5-3 = 2)
    // → infeasible (the `appearing.is_empty()` reject) → backtrack
    // (`assignment.remove`). Both roots are exhausted regardless of root
    // ordering, so the branch returns false and the triangular fast path
    // declines (None). Deterministically exercises the nonzero-constant
    // reject and the per-root backtrack.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["z".into()]);
    let z2 = pr.mul(pr.var(0), pr.var(0));
    let p0 = pr.sub(z2, pr.constant(pr.field().from_int(4))); // z^2 = 4 → {2, 5}
    let p1 = pr.sub(pr.var(0), pr.constant(pr.field().from_int(3))); // z = 3
    // Zero-dimensional (single var, leading terms z^2 and z), but UNSAT.
    let ideal = Ideal::from_gb(&pr, vec![pr.ring.clone_el(&p0), pr.ring.clone_el(&p1)]);
    assert!(ideal.is_zero_dim());
    let gb = vec![pr.ring.clone_el(&p0), pr.ring.clone_el(&p1)];
    assert!(
        try_triangular_solve(&pr, &gb, &CancelToken::none()).is_none(),
        "every root contradicts z=3 ⇒ triangular fast path returns None"
    );
}

#[test]
fn tri_dfs_backtracks_then_succeeds_on_second_var() {
    // GF(7), vars [y, z]. z^2 - 4 → z ∈ {2, 5}; (y-2)*(y-3) shape pins y to a
    // root; the system is consistent. tri_dfs solves it (success re-descent
    // after assigning z then y), exercising the `tri_dfs(..) == true` return.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["y".into(), "z".into()]);
    let z2 = pr.mul(pr.var(1), pr.var(1));
    let y2 = pr.mul(pr.var(0), pr.var(0));
    let p0 = pr.sub(z2, pr.constant(pr.field().from_int(4))); // z^2 = 4
    let p1 = pr.sub(y2, pr.constant(pr.field().from_int(2))); // y^2 = 2 → {3, 4}
    let gb = vec![pr.ring.clone_el(&p0), pr.ring.clone_el(&p1)];
    let model = try_triangular_solve(&pr, &gb, &CancelToken::none())
        .expect("consistent zero-dim system must solve");
    assert!(verify_model(&pr, &[p0, p1], &model));
    let z = &model["z"];
    assert_eq!((z * z) % BigUint::from(7u32), BigUint::from(4u32));
    let y = &model["y"];
    assert_eq!((y * y) % BigUint::from(7u32), BigUint::from(2u32));
}

#[test]
fn tri_dfs_no_triangular_structure_returns_false() {
    // A single multivariate poly x*y - 1: no nonzero poly is univariate in a
    // lone unassigned variable, so `chosen` stays None and tri_dfs returns
    // false (the "no triangular structure → caller falls back" arm).
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into(), "y".into()]);
    let gb = vec![pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one())];
    let mut assignment: HashMap<usize, FieldElem> = HashMap::new();
    assert!(
        !tri_dfs(&pr, &gb, &mut assignment, &CancelToken::none()),
        "no univariate structure ⇒ tri_dfs returns false"
    );
    assert!(assignment.is_empty(), "failed search leaves no assignment");
}

#[test]
fn try_extract_full_assignment_pins_every_variable() {
    // Direct call: a basis of two linear pins x - 5, y - 6 over GF(7) yields
    // a full assignment with both `or_insert` branches taken.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into(), "y".into()]);
    let bx = pr.sub(pr.var(0), pr.constant(pr.field().from_int(5)));
    let by = pr.sub(pr.var(1), pr.constant(pr.field().from_int(6)));
    let ideal = Ideal::from_gb(&pr, vec![bx, by]);
    let model = try_extract_full_assignment(&pr, &ideal).expect("all vars pinned");
    assert_eq!(model["x"], BigUint::from(5u32));
    assert_eq!(model["y"], BigUint::from(6u32));
}

#[test]
fn try_extract_full_assignment_partial_pin_returns_none() {
    // Only x is linearly pinned (x - 5); y appears only in a quadratic
    // (y^2 - 2). The linear-pin loop records x's `or_insert` value (running
    // the `coeffs.len() == 2 && !is_zero(coeffs[1])` body to its close) but
    // y is never pinned, so `assignment.len() != n_vars` ⇒ None.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into(), "y".into()]);
    let bx = pr.sub(pr.var(0), pr.constant(pr.field().from_int(5)));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let qy = pr.sub(y2, pr.constant(pr.field().from_int(2))); // y^2 = 2, not linear
    let ideal = Ideal::from_gb(&pr, vec![bx, qy]);
    assert!(
        try_extract_full_assignment(&pr, &ideal).is_none(),
        "one variable still unpinned ⇒ no full assignment"
    );
}

// ────────── compute_candidates Case 2 (minimal polynomial) ──────────

#[test]
fn compute_candidates_case2_minimal_polynomial_returns_roots() {
    // Drive Case 2 (zero-dimensional ideal → minimal polynomial). The
    // DegRevLex Groebner basis {x^2 - y, y^2 - x} over GF(7) has every
    // element involving two variables, so the assigned-marking loop marks
    // nothing and Case 1 (univariate deg>1) finds no candidate. The ideal is
    // zero-dimensional (leading monomials x^2 and y^2 are pure single-var
    // powers covering both variables), so Case 2 computes min_poly(x).
    //
    // Powers of x reduce as 1, x, x^2≡y, x^3≡xy, x^4≡x, so the minimal
    // polynomial is x^4 - x = x(x^3 - 1). Over GF(7) it splits completely:
    // x=0 and the cube roots of unity {1, 2, 4} (2^3=8≡1, 4^3=64≡1). Cantor–
    // Zassenhaus is complete here, so Case 2 returns Brancher::Roots with the
    // four roots {0, 1, 2, 4} for x.
    let pr = FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into(), "y".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let g0 = pr.sub(x2, pr.var(1)); // x^2 - y
    let g1 = pr.sub(y2, pr.var(0)); // y^2 - x
    let ideal = Ideal::from_gb(&pr, vec![g0, g1]);
    // Confirm the Case-2 precondition: zero-dimensional, no univariate deg>1.
    assert!(ideal.is_zero_dim(), "{{x^2-y, y^2-x}} must be zero-dimensional");
    let brancher = compute_candidates(&pr, &ideal);
    // Brancher::Roots (Case 2) — a Case-3 RoundRobin would make roots_for_var
    // panic, so reaching this assertion proves Case 2 fired.
    assert_eq!(
        roots_for_var(&pr, &brancher, 0),
        vec![
            BigUint::from(0u32),
            BigUint::from(1u32),
            BigUint::from(2u32),
            BigUint::from(4u32),
        ],
        "min_poly(x) = x^4 - x ⇒ roots {{0,1,2,4}} over GF(7)"
    );
}
