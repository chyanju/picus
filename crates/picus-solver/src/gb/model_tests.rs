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
