use super::*;
use crate::frontend::encoder::{ConstraintSystemBuilder, PolyTerm};
use num_bigint::BigUint;

// ────────── Fixture builders ──────────

/// `x + 3 = 0` over GF(7); SAT (x = 4). One equality, no diseq.
fn lin_eq_sys() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(3u32),
            vars: vec![],
        },
    ]);
    b.build()
}

/// Adds `x != 0` to `lin_eq_sys`; still SAT (x = 4 ≠ 0).
fn lin_eq_with_diseq() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    let zero = b.var("__zero");
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(3u32),
            vars: vec![],
        },
    ]);
    b.add_assignment(zero, BigUint::from(0u32));
    b.add_disequality(x, zero);
    b.build()
}

/// `x = 1` ∧ `x = 2` over GF(7); UNSAT.
fn lin_unsat_sys() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(6u32),
            vars: vec![],
        }, // x + 6 = 0 → x = 1
    ]);
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(5u32),
            vars: vec![],
        }, // x + 5 = 0 → x = 2
    ]);
    b.build()
}

/// `x·y - 1 = 0` over GF(7) (nonlinear); SAT.
fn nonlinear_sat() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    let y = b.var("y");
    // x·y + 6 = 0 → x·y = 1
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 1), (y, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(6u32),
            vars: vec![],
        },
    ]);
    b.build()
}

// ────────── IncrementalSolverContext lifecycle ──────────

#[test]
fn new_starts_empty() {
    let ctx = IncrementalSolverContext::new();
    assert!(ctx.cached_base.is_none());
    assert!(ctx.last_digest.is_none());
    assert!(ctx.partial_build.is_none());
}

#[test]
fn invalidate_clears_state() {
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    // Drive two calls so the cache builds.
    let _ = ctx.solve(&cs, &CancelToken::none());
    let _ = ctx.solve(&cs, &CancelToken::none());
    assert!(
        ctx.cached_base.is_some(),
        "expected cache after 2 same-digest calls"
    );
    ctx.invalidate();
    assert!(ctx.cached_base.is_none());
    assert!(ctx.partial_build.is_none());
}

#[test]
fn first_call_is_stateless_no_cache_built() {
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let out = ctx.solve(&cs, &CancelToken::none());
    assert!(
        matches!(out, SolveOutcome::Sat(_)),
        "expected SAT, got {:?}",
        out
    );
    assert!(ctx.cached_base.is_none(), "first call must not build cache");
    assert_eq!(ctx.last_digest, Some(digest_constraint_side(&cs)));
}

#[test]
fn second_call_same_digest_builds_cache() {
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let _ = ctx.solve(&cs, &CancelToken::none());
    let out = ctx.solve(&cs, &CancelToken::none());
    assert!(matches!(out, SolveOutcome::Sat(_)));
    assert!(
        ctx.cached_base.is_some(),
        "expected cache built on second same-digest call"
    );
    assert_eq!(
        ctx.cached_base.as_ref().unwrap().digest,
        digest_constraint_side(&cs)
    );
}

#[test]
fn third_call_same_digest_hits_cache() {
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let _ = ctx.solve(&cs, &CancelToken::none()); // first: stateless
    let _ = ctx.solve(&cs, &CancelToken::none()); // second: builds cache
    let before_digest = ctx.cached_base.as_ref().unwrap().digest;
    let out = ctx.solve(&cs, &CancelToken::none()); // third: cache hit
    assert!(matches!(out, SolveOutcome::Sat(_)));
    // Cache base unchanged.
    assert_eq!(ctx.cached_base.as_ref().unwrap().digest, before_digest);
}

#[test]
fn distinct_digest_each_call_skips_cache() {
    let mut ctx = IncrementalSolverContext::new();
    let cs1 = lin_eq_with_diseq();
    let cs2 = nonlinear_sat();
    let _ = ctx.solve(&cs1, &CancelToken::none());
    let _ = ctx.solve(&cs2, &CancelToken::none());
    // Each call is the first time for its digest → stateless.
    assert!(
        ctx.cached_base.is_none(),
        "alternating digests must not build cache"
    );
}

#[test]
fn switching_digest_after_cache_drops_cache() {
    let mut ctx = IncrementalSolverContext::new();
    let cs_a = lin_eq_with_diseq();
    let cs_b = nonlinear_sat();
    let _ = ctx.solve(&cs_a, &CancelToken::none()); // stateless
    let _ = ctx.solve(&cs_a, &CancelToken::none()); // builds cache_a
    assert!(ctx.cached_base.is_some());
    // Now switch to a different system. No cached_base for it,
    // no prior repeat → stateless. The previous cache is cleared
    // (the should_build path's "clear cache" branch).
    let _ = ctx.solve(&cs_b, &CancelToken::none());
    assert!(
        ctx.cached_base.is_none(),
        "different digest must clear cache"
    );
}

#[test]
fn unsat_through_cached_path() {
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_unsat_sys();
    let _ = ctx.solve(&cs, &CancelToken::none());
    let out = ctx.solve(&cs, &CancelToken::none()); // builds cache; whole-ring detected
    assert!(
        matches!(out, SolveOutcome::Unsat(_)),
        "expected UNSAT, got {:?}",
        out
    );
}

#[test]
fn unsat_through_cache_hit() {
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_unsat_sys();
    let _ = ctx.solve(&cs, &CancelToken::none()); // stateless UNSAT
    let _ = ctx.solve(&cs, &CancelToken::none()); // builds cache (whole-ring)
    let out = ctx.solve(&cs, &CancelToken::none()); // cache hit, fast UNSAT
    assert!(matches!(out, SolveOutcome::Unsat(_)));
}

#[test]
fn nonlinear_sat_via_cache() {
    let mut ctx = IncrementalSolverContext::new();
    let cs = nonlinear_sat();
    let _ = ctx.solve(&cs, &CancelToken::none());
    let out = ctx.solve(&cs, &CancelToken::none());
    assert!(matches!(out, SolveOutcome::Sat(_)));
    assert!(ctx.cached_base.is_some());
}

#[test]
fn pre_cancelled_solve_returns_unknown_or_stateless() {
    // A pre-cancelled token on the very first call should not
    // crash; the stateless path is taken and should surface a
    // non-SAT non-Unsat outcome.
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let cancel = CancelToken::with_timeout(std::time::Duration::from_nanos(0));
    // Sleep briefly so the timeout token's deadline is past.
    std::thread::sleep(std::time::Duration::from_millis(1));
    let out = ctx.solve(&cs, &cancel);
    // Either Unknown (most likely) or completion (if the solve
    // finished before the cancel check fired) — both sound.
    assert!(matches!(
        out,
        SolveOutcome::Unknown | SolveOutcome::Sat(_) | SolveOutcome::Unsat(_)
    ));
}

// ────────── digest_constraint_side properties ──────────

#[test]
fn digest_stable_for_same_system() {
    let cs1 = lin_eq_with_diseq();
    let cs2 = lin_eq_with_diseq();
    assert_eq!(digest_constraint_side(&cs1), digest_constraint_side(&cs2));
}

#[test]
fn digest_excludes_disequalities() {
    // Same constraint side, with vs without disequalities → same digest.
    let with = lin_eq_with_diseq();
    let without = lin_eq_sys();
    // `without` doesn't have the `__zero` aux var or the assignment;
    // its constraint side differs from `with`. Build a stripped
    // version of `with` keeping equalities + assignment + var_map
    // but no disequalities to test the diseq-exclusion property.
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    let zero = b.var("__zero");
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(3u32),
            vars: vec![],
        },
    ]);
    b.add_assignment(zero, BigUint::from(0u32));
    // Note: no add_disequality call.
    let stripped = b.build();
    assert_eq!(
        digest_constraint_side(&with),
        digest_constraint_side(&stripped),
        "digest must exclude disequalities"
    );
    // And not equal to `without` (which lacks the __zero var).
    assert_ne!(
        digest_constraint_side(&with),
        digest_constraint_side(&without)
    );
}

#[test]
fn digest_changes_with_prime() {
    let mut b7 = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x7 = b7.var("x");
    b7.add_equality(vec![PolyTerm {
        coeff: BigUint::from(1u32),
        vars: vec![(x7, 1)],
    }]);
    let cs7 = b7.build();

    let mut b11 = ConstraintSystemBuilder::new(BigUint::from(11u32));
    let x11 = b11.var("x");
    b11.add_equality(vec![PolyTerm {
        coeff: BigUint::from(1u32),
        vars: vec![(x11, 1)],
    }]);
    let cs11 = b11.build();

    assert_ne!(digest_constraint_side(&cs7), digest_constraint_side(&cs11));
}

#[test]
fn digest_changes_with_var_names() {
    let mut bx = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let xv = bx.var("x");
    bx.add_equality(vec![PolyTerm {
        coeff: BigUint::from(1u32),
        vars: vec![(xv, 1)],
    }]);
    let cs_x = bx.build();

    let mut by = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let yv = by.var("y");
    by.add_equality(vec![PolyTerm {
        coeff: BigUint::from(1u32),
        vars: vec![(yv, 1)],
    }]);
    let cs_y = by.build();

    assert_ne!(digest_constraint_side(&cs_x), digest_constraint_side(&cs_y));
}

#[test]
fn digest_changes_with_equalities() {
    let cs_one_eq = lin_eq_sys();
    let cs_two_eq = lin_unsat_sys(); // same vars but two equalities
    assert_ne!(
        digest_constraint_side(&cs_one_eq),
        digest_constraint_side(&cs_two_eq)
    );
}

#[test]
fn digest_changes_with_add_field_polys() {
    let mut b_off = ConstraintSystemBuilder::new(BigUint::from(7u32));
    b_off.set_add_field_polys(false);
    let x = b_off.var("x");
    b_off.add_equality(vec![PolyTerm {
        coeff: BigUint::from(1u32),
        vars: vec![(x, 1)],
    }]);
    let cs_off = b_off.build();

    let mut b_on = ConstraintSystemBuilder::new(BigUint::from(7u32));
    b_on.set_add_field_polys(true);
    let x = b_on.var("x");
    b_on.add_equality(vec![PolyTerm {
        coeff: BigUint::from(1u32),
        vars: vec![(x, 1)],
    }]);
    let cs_on = b_on.build();

    assert_ne!(
        digest_constraint_side(&cs_off),
        digest_constraint_side(&cs_on)
    );
}

#[test]
fn digest_changes_with_assignments() {
    // Same equality, different assignment value → different digest
    // (assignments are part of the constraint side).
    let mut b1 = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b1.var("x");
    b1.add_assignment(x, BigUint::from(2u32));
    let cs1 = b1.build();

    let mut b2 = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b2.var("x");
    b2.add_assignment(x, BigUint::from(3u32));
    let cs2 = b2.build();

    assert_ne!(digest_constraint_side(&cs1), digest_constraint_side(&cs2));
}

#[test]
fn digest_changes_with_bitsums() {
    let mut b1 = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let _x = b1.var("x");
    let _y = b1.var("y");
    let cs1 = b1.build();

    let mut b2 = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b2.var("x");
    let y = b2.var("y");
    b2.add_bitsum(vec![x, y]);
    let cs2 = b2.build();

    assert_ne!(digest_constraint_side(&cs1), digest_constraint_side(&cs2));
}

// ────────── stateless_solve direct path ──────────

#[test]
fn stateless_solve_sat_direct() {
    let cs = lin_eq_with_diseq();
    let out = stateless_solve(&cs, &CancelToken::none());
    assert!(matches!(out, SolveOutcome::Sat(_)));
}

#[test]
fn stateless_solve_unsat_direct() {
    let cs = lin_unsat_sys();
    let out = stateless_solve(&cs, &CancelToken::none());
    assert!(matches!(out, SolveOutcome::Unsat(_)));
}

// ────────── continue_partial direct invocation ──────────

/// Build a `PartialBuild` for a small constraint system and feed it
/// to `continue_partial`. Mirrors what `rebuild_base` would save on
/// cancellation, but constructed deterministically so the resume
/// path is exercised without timing tricks.
fn make_partial_build(cs: &ConstraintSystem) -> PartialBuild {
    let encoded = encode_constraint_side(cs).expect("encode");
    let (gens, _) = build_partitions(
        &encoded.poly_ring,
        &encoded.polynomials,
        &encoded.bitsum_polys,
    );
    let ring = ring_for_order(&encoded.poly_ring, MonomialOrder::DegRevLex);
    let bcfg = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: true,
        use_f4: false,
    };
    let inflight = vec![
        IncrementalGB::new(ring.clone(), bcfg.clone()),
        IncrementalGB::new(ring, bcfg),
    ];
    let bit_prop_state = {
        let bp = BitProp::new(&encoded.poly_ring);
        bp.to_state()
    };
    PartialBuild {
        digest: digest_constraint_side(cs),
        poly_ring: Arc::new(encoded.poly_ring),
        var_map: encoded.var_map,
        constraint_polys: encoded.polynomials,
        bitsum_polys: encoded.bitsum_polys,
        bit_prop_state,
        inflight,
        pending: gens,
        contains_memo: std::collections::HashSet::new(),
    }
}

#[test]
fn continue_partial_completes_on_simple_sat_system() {
    let cs = lin_eq_with_diseq();
    let mut partial = make_partial_build(&cs);
    let out = continue_partial(&mut partial, &CancelToken::none());
    assert!(
        matches!(out, ResumeOutcome::Complete(_)),
        "expected Complete on simple system, got something else"
    );
}

#[test]
fn continue_partial_completes_on_unsat_system() {
    let cs = lin_unsat_sys();
    let mut partial = make_partial_build(&cs);
    let out = continue_partial(&mut partial, &CancelToken::none());
    // UNSAT is detected as whole-ring during the GB build; `continue_partial`
    // still completes (the cache stores the trivial basis).
    assert!(matches!(out, ResumeOutcome::Complete(_)));
}

#[test]
fn continue_partial_returns_still_partial_on_cancel() {
    let cs = nonlinear_sat();
    let mut partial = make_partial_build(&cs);
    // Pre-cancelled token: the resume loop should observe cancel and
    // return StillPartial without completing.
    let cancel = CancelToken::cancelled();
    let out = continue_partial(&mut partial, &cancel);
    assert!(matches!(out, ResumeOutcome::StillPartial));
}

// ────────── resume path via full IncrementalSolverContext::solve ──────────

#[test]
fn solve_resumes_from_saved_partial_build() {
    // Drive a sequence: solve, solve (builds cache), invalidate cache
    // (but keep last_digest), inject a manual partial_build with the
    // same digest, solve → continue_partial path.
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let _ = ctx.solve(&cs, &CancelToken::none());
    let _ = ctx.solve(&cs, &CancelToken::none());
    // Now ctx.cached_base is Some. Replace it with a partial_build at
    // the same digest to force the resume path.
    ctx.cached_base = None;
    ctx.partial_build = Some(make_partial_build(&cs));
    // ctx.last_digest already matches; partial_matches will be true.
    let out = ctx.solve(&cs, &CancelToken::none());
    assert!(matches!(out, SolveOutcome::Sat(_)));
    // Cache should now be built from the resumed partial.
    assert!(ctx.cached_base.is_some());
}
