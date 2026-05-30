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

/// Two bit variables `b0`, `b1` (each `b*(b-1)=0`) with a bitsum
/// `[b0, b1]` over GF(7). SAT (bits are free). Exercises the bit-prop
/// branch of the resume fixpoint.
fn bitsum_sat_sys() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    // b0^2 - b0 = 0
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(b0, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(6u32),
            vars: vec![(b0, 1)],
        },
    ]);
    // b1^2 - b1 = 0
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(b1, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(6u32),
            vars: vec![(b1, 1)],
        },
    ]);
    b.add_bitsum(vec![b0, b1]);
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

#[test]
fn solve_resume_still_partial_keeps_partial_and_returns_unknown() {
    // continue_partial sees a pre-cancelled token mid-resume and returns
    // StillPartial; solve() then re-stores the partial and returns Unknown.
    let mut ctx = IncrementalSolverContext::new();
    let cs = nonlinear_sat();
    let digest = digest_constraint_side(&cs);
    // Prime last_digest so the resume branch is taken, and inject a
    // matching partial build.
    ctx.last_digest = Some(digest);
    ctx.partial_build = Some(make_partial_build(&cs));
    let out = ctx.solve(&cs, &CancelToken::cancelled());
    assert!(
        matches!(out, SolveOutcome::Unknown),
        "StillPartial resume must return Unknown, got {:?}",
        out
    );
    assert!(
        ctx.partial_build.is_some(),
        "partial build must be retained for the next resume"
    );
    assert!(ctx.cached_base.is_none());
}

// ────────── rebuild_base failure / cancellation (via solve) ──────────

#[test]
fn rebuild_base_pre_cancelled_falls_back_to_stateless() {
    // Second same-digest call triggers the should_build fast path; a
    // pre-cancelled token makes rebuild_base return Err at the post-encode
    // cancel check, so solve() falls back to stateless_solve (Unknown under
    // a cancelled token) and leaves no cache.
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let _ = ctx.solve(&cs, &CancelToken::none()); // first: stateless, sets last_digest
    let out = ctx.solve(&cs, &CancelToken::cancelled()); // should_build → rebuild_base Err
    let direct = stateless_solve(&cs, &CancelToken::cancelled());
    assert_eq!(
        std::mem::discriminant(&out),
        std::mem::discriminant(&direct),
        "cancelled rebuild must fall back to stateless: {:?} vs {:?}",
        out,
        direct
    );
    assert!(ctx.cached_base.is_none(), "no cache on cancelled rebuild");
    assert!(ctx.partial_build.is_none());
}

#[test]
fn rebuild_base_direct_pre_cancel_returns_err() {
    // Direct call: rebuild_base encodes (no cancel check), then the
    // post-encode cancel check returns Err without populating either
    // cached_base or partial_build.
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let digest = digest_constraint_side(&cs);
    let res = ctx.rebuild_base(&cs, digest, &CancelToken::cancelled());
    assert_eq!(res, Err(()));
    assert!(ctx.cached_base.is_none());
    assert!(ctx.partial_build.is_none());
}

#[test]
fn rebuild_base_direct_success_builds_cache() {
    // The Ok path: a non-cancelled rebuild_base populates cached_base with
    // the matching digest and a two-partition split GB.
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let digest = digest_constraint_side(&cs);
    let res = ctx.rebuild_base(&cs, digest, &CancelToken::none());
    assert_eq!(res, Ok(()));
    let cached = ctx.cached_base.as_ref().expect("cache built");
    assert_eq!(cached.digest, digest);
    assert_eq!(cached.split_gb_owned.len(), 2);
    assert!(ctx.partial_build.is_none());
}

// ────────── continue_partial: pending-reduction / completion paths ──────────

/// Build a `PartialBuild` over the given ring, with control over the
/// inflight bases (seeded via `add_generators`) and the pending generator
/// lists, so the pending-reduction branch can be exercised deterministically.
/// The seed/pending polys MUST be built from `poly_ring` so the engine ring
/// and the poly contexts agree.
fn hand_partial(
    poly_ring: Arc<FfPolyRing>,
    seed_per_split: Vec<Vec<Poly>>,
    pending_per_split: Vec<Vec<Poly>>,
) -> PartialBuild {
    let ring = ring_for_order(&poly_ring, MonomialOrder::DegRevLex);
    let cfg = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: true,
        use_f4: false,
    };
    let mut inflight = vec![
        IncrementalGB::new(ring.clone(), cfg.clone()),
        IncrementalGB::new(ring, cfg),
    ];
    for (i, seed) in seed_per_split.into_iter().enumerate() {
        if !seed.is_empty() {
            inflight[i]
                .add_generators(unwrap_dense_vec(seed, poly_ring.ctx()))
                .expect("seed add_generators");
        }
    }
    let mut var_map = HashMap::new();
    for (i, n) in poly_ring.var_names().iter().enumerate() {
        var_map.insert(n.clone(), i);
    }
    let bit_prop_state = BitProp::new(&poly_ring).to_state();
    PartialBuild {
        digest: 0,
        poly_ring,
        var_map,
        constraint_polys: Vec::new(),
        bitsum_polys: Vec::new(),
        bit_prop_state,
        inflight,
        pending: pending_per_split,
        contains_memo: std::collections::HashSet::new(),
    }
}

#[test]
fn continue_partial_reduces_pending_against_nonempty_basis() {
    // Seed basis 0 with `x` (x = 0). Pending: `x` (reduces to 0, filtered)
    // and `y` (reduces to itself, survives and is added). After resume the
    // build completes with both x and y in basis 0's reduced GB.
    let field = crate::ff::field::PrimeField::new(BigUint::from(7u32));
    let pr = Arc::new(FfPolyRing::new(field, vec!["x".into(), "y".into()]));
    let seed = vec![vec![pr.var(0)], vec![]];
    let pending = vec![vec![pr.var(0), pr.var(1)], vec![]];
    let mut partial = hand_partial(pr, seed, pending);
    let out = continue_partial(&mut partial, &CancelToken::none());
    let cached = match out {
        ResumeOutcome::Complete(c) => c,
        _ => panic!("expected Complete"),
    };
    // Basis 0 should encode x = 0 and y = 0 (two linear generators); the
    // redundant copy of x reduces to zero and is filtered.
    let basis0 = &cached.split_gb_owned[0];
    assert_eq!(basis0.len(), 2, "x and y are the two surviving generators");
    assert!(basis0.iter().all(|p| !p.is_zero()));
}

#[test]
fn continue_partial_empty_pending_quiescent_completes() {
    // Both inflight GBs are quiescent (fresh) and pending is empty: the
    // fixpoint loop performs no extend work and converges immediately to a
    // Complete with empty bases.
    let field = crate::ff::field::PrimeField::new(BigUint::from(7u32));
    let pr = Arc::new(FfPolyRing::new(field, vec!["x".into()]));
    let mut partial = hand_partial(pr, vec![vec![], vec![]], vec![vec![], vec![]]);
    let out = continue_partial(&mut partial, &CancelToken::none());
    let cached = match out {
        ResumeOutcome::Complete(c) => c,
        _ => panic!("expected Complete"),
    };
    assert!(cached.split_gb_owned.iter().all(|b| b.is_empty()));
}

#[test]
fn continue_partial_bitsum_system_matches_stateless_verdict() {
    // A system with a bitsum drives the propagation branch of the fixpoint
    // loop. The resumed cache, when queried, must agree with the stateless
    // solve on the same system.
    let cs = bitsum_sat_sys();
    let mut partial = make_partial_build(&cs);
    let out = continue_partial(&mut partial, &CancelToken::none());
    let cached = match out {
        ResumeOutcome::Complete(c) => c,
        _ => panic!("expected Complete"),
    };
    let via_cache = solve_with_cached(&cached, &cs, &CancelToken::none());
    let via_stateless = stateless_solve(&cs, &CancelToken::none());
    assert_eq!(
        std::mem::discriminant(&via_cache),
        std::mem::discriminant(&via_stateless),
        "cached resume verdict must match stateless: cache={:?} stateless={:?}",
        via_cache,
        via_stateless
    );
}

// ────────── solve_with_cached direct paths ──────────

#[test]
fn solve_with_cached_query_var_not_in_cached_falls_back_to_stateless() {
    // Build a cache for the 1-var system `x + 3 = 0` (cached var_map has
    // only "x"). Query with a disequality referencing a fresh var "z" that
    // the cached ring never saw: encode_query_disequalities can't resolve
    // "z" through the cached var_map → Err → solve_with_cached falls back to
    // a fresh stateless solve of the query. The fallback verdict must match
    // a direct stateless solve of the same query.
    let mut ctx = IncrementalSolverContext::new();
    let base = lin_eq_sys();
    let digest = digest_constraint_side(&base);
    ctx.rebuild_base(&base, digest, &CancelToken::none())
        .expect("build cache");
    let cached = ctx.cached_base.as_ref().expect("cache");

    // Query: x + 3 = 0 with a disequality (x, z); "z" is unknown to the cache.
    let mut qb = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = qb.var("x");
    let z = qb.var("z");
    qb.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(3u32),
            vars: vec![],
        },
    ]);
    qb.add_disequality(x, z);
    let q = qb.build();

    let out = solve_with_cached(cached, &q, &CancelToken::none());
    let direct = stateless_solve(&q, &CancelToken::none());
    assert_eq!(
        std::mem::discriminant(&out),
        std::mem::discriminant(&direct),
        "unresolvable query var → stateless fallback; verdict {:?} must match direct stateless {:?}",
        out,
        direct
    );
}

#[test]
fn solve_with_cached_extend_cancel_returns_unknown() {
    // A pre-cancelled token makes split_gb_extend_cancel return Err, so
    // solve_with_cached short-circuits to Unknown.
    let mut ctx = IncrementalSolverContext::new();
    let cs = lin_eq_with_diseq();
    let digest = digest_constraint_side(&cs);
    ctx.rebuild_base(&cs, digest, &CancelToken::none())
        .expect("build cache");
    let cached = ctx.cached_base.as_ref().expect("cache");
    let out = solve_with_cached(cached, &cs, &CancelToken::cancelled());
    assert!(
        matches!(out, SolveOutcome::Unknown),
        "cancelled extend must yield Unknown, got {:?}",
        out
    );
}

#[test]
fn solve_with_cached_sat_verifies_bitsum_polys() {
    // CachedBase whose model (x = 0, pinned by the linear basis) satisfies
    // constraint_polys and bitsum_polys: the SAT path includes bitsum_polys
    // in the verification set and the model passes → Sat.
    let field = crate::ff::field::PrimeField::new(BigUint::from(7u32));
    let pr = Arc::new(FfPolyRing::new(field, vec!["x".into()]));
    let x_basis = pr.var(0); // x  (=> x = 0)
    let x_constraint = pr.var(0);
    let x_bitsum = pr.var(0); // bitsum def also x  (=> x = 0), satisfied by x = 0
    let cached = CachedBase {
        poly_ring: pr.clone(),
        var_map: {
            let mut m = HashMap::new();
            m.insert("x".to_string(), 0usize);
            m
        },
        constraint_polys: vec![x_constraint],
        bitsum_polys: vec![x_bitsum],
        split_gb_owned: vec![vec![x_basis], vec![]],
        bit_prop_state: BitProp::new(&pr).to_state(),
        digest: 0,
    };
    let cs = ConstraintSystemBuilder::new(BigUint::from(7u32)).build();
    let out = solve_with_cached(&cached, &cs, &CancelToken::none());
    assert!(
        matches!(out, SolveOutcome::Sat(_)),
        "model x=0 satisfies constraint + bitsum → Sat, got {:?}",
        out
    );
}

/// `x^2 + 4 = 0` over GF(7) i.e. `x^2 = 3`. 3 is a quadratic non-residue
/// mod 7 (squares mod 7 are {0,1,2,4}), so the system is UNSAT but its GB
/// `{x^2 - 3}` is NOT the whole ring — the cached path reaches the
/// root-enumeration `split_find_zero_cancel`, which proves UNSAT.
fn quadratic_no_root_unsat() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(4u32),
            vars: vec![],
        }, // x^2 + 4 = 0 → x^2 = 3 (no GF(7) root)
    ]);
    b.build()
}

#[test]
fn solve_with_cached_find_zero_unsat_when_no_root() {
    // The split GB of x^2 = 3 over GF(7) is not whole-ring, so the cached
    // path falls through the whole-ring check and `split_find_zero_cancel`
    // returns Unsat (exhaustive zero-dim enumeration finds no GF(7) point).
    // Exercises the `SplitFindZeroOutcome::Unsat` arm of solve_with_cached.
    let mut ctx = IncrementalSolverContext::new();
    let cs = quadratic_no_root_unsat();
    let digest = digest_constraint_side(&cs);
    ctx.rebuild_base(&cs, digest, &CancelToken::none())
        .expect("build cache");
    let cached = ctx.cached_base.as_ref().expect("cache");
    // The cached split GB must not already be the whole ring (else the
    // find_zero arm would be skipped).
    assert!(
        !cached
            .split_gb_owned
            .iter()
            .any(|b| b.iter().any(|p| !p.is_zero() && p.is_constant())),
        "x^2 = 3 GB is non-trivial; UNSAT must come from root enumeration"
    );
    let out = solve_with_cached(cached, &cs, &CancelToken::none());
    let direct = stateless_solve(&cs, &CancelToken::none());
    assert!(
        matches!(out, SolveOutcome::Unsat(_)),
        "no-root quadratic must be UNSAT via find_zero, got {:?}",
        out
    );
    assert_eq!(
        std::mem::discriminant(&out),
        std::mem::discriminant(&direct),
        "cached find_zero verdict must match stateless"
    );
}

#[test]
fn solve_with_cached_sat_rejected_by_bitsum_returns_unknown() {
    // CachedBase whose linear basis pins x = 0, but bitsum_polys carries
    // `x - 1` (violated by x = 0). The model found by the search satisfies
    // the bases but fails verification against the full set including the
    // bitsum def, so solve_with_cached returns Unknown instead of Sat.
    let field = crate::ff::field::PrimeField::new(BigUint::from(7u32));
    let pr = Arc::new(FfPolyRing::new(field, vec!["x".into()]));
    let x_basis = pr.var(0); // x => x = 0
    // x - 1 : violated by x = 0.
    let x_minus_one = pr.sub(pr.var(0), pr.one());
    let cached = CachedBase {
        poly_ring: pr.clone(),
        var_map: {
            let mut m = HashMap::new();
            m.insert("x".to_string(), 0usize);
            m
        },
        constraint_polys: vec![pr.var(0)],
        bitsum_polys: vec![x_minus_one],
        split_gb_owned: vec![vec![x_basis], vec![]],
        bit_prop_state: BitProp::new(&pr).to_state(),
        digest: 0,
    };
    let cs = ConstraintSystemBuilder::new(BigUint::from(7u32)).build();
    let out = solve_with_cached(&cached, &cs, &CancelToken::none());
    assert!(
        matches!(out, SolveOutcome::Unknown),
        "model fails bitsum verification → Unknown, got {:?}",
        out
    );
}

// ────────── encode-failure fallbacks ──────────

/// `var_names = ["x"]` but the single equality references var index 5.
/// `compact_used_vars` collects `{5}` whose count equals `var_names.len()`,
/// so it early-returns the system unchanged (never indexing `var_names[5]`);
/// the rewriter and bitsum extractor also leave it intact (the term is a
/// bare linear monomial, not a `b·(b-1)` bit constraint). `encode_impl`
/// then rejects the out-of-range index. Used to drive the encode-error
/// branches without constructing >5000 variables.
fn out_of_range_eq_sys() -> ConstraintSystem {
    ConstraintSystem {
        prime: BigUint::from(7u32),
        var_names: vec!["x".to_string()],
        equalities: vec![vec![PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(5u32, 1)],
        }]],
        disequalities: Vec::new(),
        assignments: Vec::new(),
        bitsums: Vec::new(),
        add_field_polys: false,
    }
}

#[test]
fn encode_constraint_side_errors_on_out_of_range_var() {
    // Confirms the fixture actually trips `encode_constraint_side`'s
    // out-of-range check (the precondition for rebuild_base's Err arm).
    let cs = out_of_range_eq_sys();
    assert!(
        encode_constraint_side(&cs).is_err(),
        "out-of-range equality var must fail encode_constraint_side"
    );
}

#[test]
fn rebuild_base_returns_err_on_encode_failure() {
    // rebuild_base's `encode_constraint_side` returns Err → the `Err(_) =>
    // return Err(())` arm fires before any GB work; neither cache nor
    // partial build is populated.
    let mut ctx = IncrementalSolverContext::new();
    let cs = out_of_range_eq_sys();
    let digest = digest_constraint_side(&cs);
    let res = ctx.rebuild_base(&cs, digest, &CancelToken::none());
    assert_eq!(res, Err(()));
    assert!(ctx.cached_base.is_none());
    assert!(ctx.partial_build.is_none());
}

#[test]
fn solve_falls_back_to_stateless_when_rebuild_encode_fails() {
    // Two same-digest calls drive the should_build fast path; the second
    // call's rebuild_base hits the encode failure and solve() falls back to
    // stateless_solve, which itself fails to encode → Unknown.
    let mut ctx = IncrementalSolverContext::new();
    let cs = out_of_range_eq_sys();
    let first = ctx.solve(&cs, &CancelToken::none()); // stateless, sets last_digest
    assert!(matches!(first, SolveOutcome::Unknown));
    let out = ctx.solve(&cs, &CancelToken::none()); // should_build → rebuild Err → stateless
    assert!(
        matches!(out, SolveOutcome::Unknown),
        "encode failure must surface Unknown via stateless fallback, got {:?}",
        out
    );
    assert!(ctx.cached_base.is_none());
    assert!(ctx.partial_build.is_none());
}

#[test]
fn stateless_solve_encode_failure_returns_unknown() {
    // stateless_solve's `encode` returns Err on the out-of-range system, so
    // the `Err(_) => SolveOutcome::Unknown` arm fires directly.
    let cs = out_of_range_eq_sys();
    let out = stateless_solve(&cs, &CancelToken::none());
    assert!(
        matches!(out, SolveOutcome::Unknown),
        "encode error in stateless_solve → Unknown, got {:?}",
        out
    );
}

// ────────── solve_with_cached: split_find_zero UNSAT (non-whole-ring) ──────────

#[test]
fn solve_with_cached_unsat_via_split_find_zero() {
    // `x^2 + 1 = 0` over GF(7) has no root (squares mod 7 are {0,1,2,4}; 6
    // is not among them). Its Groebner basis `{x^2 + 1}` is NOT the whole
    // ring, so the whole-ring short-circuit does not fire; the bounded
    // search over GF(7) is exhaustive and reports `NoZero{exhaustive:true}`,
    // which `solve_with_cached` maps to UNSAT via the `SplitFindZeroOutcome::
    // Unsat` arm (not the earlier whole-ring UNSAT).
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![],
        },
    ]);
    let cs = b.build();

    let mut ctx = IncrementalSolverContext::new();
    let digest = digest_constraint_side(&cs);
    ctx.rebuild_base(&cs, digest, &CancelToken::none())
        .expect("build cache");
    let cached = ctx.cached_base.as_ref().expect("cache");

    // The cached split-GB holds a non-trivial basis (the single nonlinear
    // generator x^2 + 1); a whole-ring basis would instead carry a unit and
    // be handled by the earlier short-circuit rather than split_find_zero.
    assert!(
        cached.split_gb_owned.iter().any(|b| !b.is_empty()),
        "cache holds a non-trivial basis, got {:?}",
        cached.split_gb_owned.iter().map(|b| b.len()).collect::<Vec<_>>()
    );

    let out = solve_with_cached(cached, &cs, &CancelToken::none());
    assert!(
        matches!(out, SolveOutcome::Unsat(_)),
        "x^2+1 over GF(7) is UNSAT via exhaustive search, got {:?}",
        out
    );
}

#[test]
fn solve_unsat_x2_plus_1_through_cache_hit() {
    // End-to-end: the same `x^2 + 1 = 0` over GF(7) routed through the full
    // solve cache lifecycle. Second call builds the cache; the cached path
    // reaches split_find_zero and returns UNSAT.
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    b.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![],
        },
    ]);
    let cs = b.build();
    let mut ctx = IncrementalSolverContext::new();
    let first = ctx.solve(&cs, &CancelToken::none());
    assert!(matches!(first, SolveOutcome::Unsat(_)), "stateless: {:?}", first);
    let second = ctx.solve(&cs, &CancelToken::none()); // builds cache, cached UNSAT
    assert!(
        matches!(second, SolveOutcome::Unsat(_)),
        "cached UNSAT for x^2+1, got {:?}",
        second
    );
    assert!(ctx.cached_base.is_some());
}

// ────────── continue_partial: surviving-empty `run_only` branch ──────────

#[test]
fn continue_partial_all_pending_reduce_to_zero_runs_run_only_branch() {
    // Seed partition 0 with `{x}` (basis = x, hence quiescent), and supply
    // pending 0 = `[x]`. In the first fixpoint iteration, the pending poly
    // reduces by the basis `{x}` to `0` and is filtered out, leaving
    // `surviving` empty while `has_pending` was true. That drives the
    // `else` arm of `if !surviving.is_empty()`, calling `run_only()` on the
    // already-quiescent IGB — the run_only-with-empty-surviving branch.
    //
    // The build then converges: partition 0 holds `{x}`, propagation seeds
    // partition 1 with `x` on iteration 2, and the loop terminates with both
    // bases equal to `{x}`.
    let field = crate::ff::field::PrimeField::new(BigUint::from(7u32));
    let pr = Arc::new(FfPolyRing::new(field, vec!["x".into(), "y".into()]));
    let seed = vec![vec![pr.var(0)], vec![]];
    let pending = vec![vec![pr.var(0)], vec![]];
    let mut partial = hand_partial(pr, seed, pending);
    let out = continue_partial(&mut partial, &CancelToken::none());
    let cached = match out {
        ResumeOutcome::Complete(c) => c,
        _ => panic!("expected Complete"),
    };
    // Partition 0 ends up with `{x}` (the redundant pending copy reduced to
    // zero and was filtered); propagation seeded partition 1 with `x`, which
    // gets accepted there too.
    assert_eq!(cached.split_gb_owned[0].len(), 1, "basis 0 = {{x}}");
    assert!(!cached.split_gb_owned[0][0].is_zero());
    assert_eq!(cached.split_gb_owned[1].len(), 1, "basis 1 propagated to {{x}}");
}

// ────────── solve_with_cached: linear-admit branch (constant query poly) ──────────

/// `x + 3 = 0` over GF(7) plus a self-disequality `x != x`. The disequality
/// is unsatisfiable, encoded as the Rabinowitsch poly `(x - x)·w - 1 = -1`
/// (a constant). A constant has `total_degree = 0 ≤ 1`, so
/// `admit(ring, 0, p)` returns true and the constant lands in the linear
/// partition via the admit branch of `solve_with_cached`.
fn self_diseq_unsat_sys() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    // x + 3 = 0  (constraint-side equality so build_partitions has something
    // to seed the linear basis with — irrelevant to admit dispatch but keeps
    // the cache realistic).
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
    b.add_disequality(x, x); // x != x → -1 query poly (constant).
    b.build()
}

#[test]
fn solve_with_cached_constant_query_poly_admitted_to_linear_partition() {
    // Build the cache for `self_diseq_unsat_sys`, then run `solve_with_cached`
    // directly. `encode_query_disequalities` produces the constant `-1` for
    // the `(x, x)` disequality; in `solve_with_cached` the constant satisfies
    // `admit(ring, 0, p)` → it is added to partition 0 and also to partition
    // 1 (k > 1). The whole-ring check then fires and the verdict is UNSAT
    // (x != x has no model).
    let mut ctx = IncrementalSolverContext::new();
    let cs = self_diseq_unsat_sys();
    let digest = digest_constraint_side(&cs);
    ctx.rebuild_base(&cs, digest, &CancelToken::none())
        .expect("build cache");
    let cached = ctx.cached_base.as_ref().expect("cache");
    // Sanity: the cached ring carries the reserved __w_diseq_0 slot.
    assert!(
        cached.var_map.contains_key("__w_diseq_0"),
        "cached var_map must hold the reserved witness slot"
    );
    // The cached starting bases are non-whole (they encode `x + 3 = 0`); the
    // whole-ring UNSAT comes from the added constant query poly, not from
    // the cache state.
    assert!(
        !cached
            .split_gb_owned
            .iter()
            .any(|b| b.iter().any(|p| !p.is_zero() && p.is_constant())),
        "cache must not already be whole-ring; UNSAT must come from the query"
    );
    let out = solve_with_cached(cached, &cs, &CancelToken::none());
    assert!(
        matches!(out, SolveOutcome::Unsat(_)),
        "constant query poly should drive UNSAT, got {:?}",
        out
    );
}

// ────────── solve_with_cached: k=1 fallback to partition 0 ──────────

#[test]
fn solve_with_cached_k1_fallback_places_query_in_partition_zero() {
    // Hand-build a CachedBase with exactly one (empty) partition and a
    // poly_ring carrying the `__w_diseq_0` slot. The query system has two
    // distinct vars `x`, `y` and the disequality `(x, y)`, so the encoded
    // query poly is `(x - y)·w - 1` with `total_degree = 2`. In
    // `solve_with_cached`:
    //   - `admit(ring, 0, p)` = false (degree > 1).
    //   - `k > 1` = false (k = 1).
    //   - placed stays false → `!placed && k > 0` true → the fallback
    //     pushes the poly to partition 0.
    // The 1-partition split_gb_extend then accepts the Rabinowitsch poly
    // and find_zero discovers a model satisfying `x != y` (e.g. x=1,y=0,w=1).
    let field = crate::ff::field::PrimeField::new(BigUint::from(7u32));
    let pr = Arc::new(FfPolyRing::new(
        field,
        vec!["x".into(), "y".into(), "__w_diseq_0".into()],
    ));
    let var_map = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), 0usize);
        m.insert("y".to_string(), 1usize);
        m.insert("__w_diseq_0".to_string(), 2usize);
        m
    };
    let cached = CachedBase {
        poly_ring: pr.clone(),
        var_map,
        constraint_polys: Vec::new(),
        bitsum_polys: Vec::new(),
        // Exactly one partition (k = 1) — this is what drives the fallback.
        split_gb_owned: vec![vec![]],
        bit_prop_state: BitProp::new(&pr).to_state(),
        digest: 0,
    };
    // Query: vars x, y; disequality (x, y); no equalities.
    let mut qb = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let qx = qb.var("x");
    let qy = qb.var("y");
    qb.add_disequality(qx, qy);
    let q = qb.build();

    let out = solve_with_cached(&cached, &q, &CancelToken::none());
    // The system asserts `x != y` with no other constraints — satisfiable
    // over GF(7), so the fallback path produces SAT.
    assert!(
        matches!(out, SolveOutcome::Sat(_)),
        "k=1 fallback should add the Rabinowitsch poly to partition 0 and \
         find a model for x != y, got {:?}",
        out
    );
}

/// `x − y = 0` (forces x = y) over GF(7) with disequality `(x, y)`: UNSAT.
fn forced_diseq_sys() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x = b.var("x");
    let y = b.var("y");
    // x + 6y = 0  (6 ≡ −1 mod 7), i.e. x − y = 0.
    b.add_equality(vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
        PolyTerm { coeff: BigUint::from(6u32), vars: vec![(y, 1)] },
    ]);
    b.add_disequality(x, y);
    b.build()
}

#[test]
fn membership_fastpath_forced_diseq_unsat_matches_full_path() {
    // `x − y ∈ I`, so the disequality is unsatisfiable. The membership
    // fast-path (flag on) and the full Rabinowitsch path (flag off) must
    // both report UNSAT — the fast-path never changes a verdict.
    let sys = forced_diseq_sys();
    let cancel = CancelToken::none();

    let off = {
        let mut ctx = IncrementalSolverContext::new();
        ctx.solve(&sys, &cancel); // prime the digest (stateless)
        ctx.solve(&sys, &cancel) // cached path
    };
    assert!(matches!(off, SolveOutcome::Unsat(_)), "full path: {:?}", off);

    let on = {
        let _g = crate::config::ConfigGuard::with_override(|c| c.membership_fastpath = true);
        let mut ctx = IncrementalSolverContext::new();
        ctx.solve(&sys, &cancel);
        ctx.solve(&sys, &cancel)
    };
    assert!(matches!(on, SolveOutcome::Unsat(_)), "fast path: {:?}", on);
}

#[test]
fn matrix_elim_order_wiring_is_sound_on_forced_diseq() {
    // `x0 − y0 = 0` (forces x0 = y0) with disequality `(x0, y0)`: UNSAT.
    // Under `matrix_elim_order` the encoder builds the ring with an
    // elimination order on the `y0` alt-copy variable; the order-agnostic
    // split-GB reads that order and must still report UNSAT (whole-ring
    // detection is order-independent). Exercises the elim-ring wiring.
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    let x0 = b.var("x0");
    let y0 = b.var("y0");
    b.add_equality(vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x0, 1)] },
        PolyTerm { coeff: BigUint::from(6u32), vars: vec![(y0, 1)] }, // x0 − y0
    ]);
    b.add_disequality(x0, y0);
    let sys = b.build();
    let cancel = CancelToken::none();
    let _g = crate::config::ConfigGuard::with_override(|c| c.matrix_elim_order = true);
    let r = stateless_solve(&sys, &cancel);
    assert!(
        matches!(r, SolveOutcome::Unsat(_)),
        "elim-order forced diseq must be UNSAT, got {:?}",
        r
    );
}

#[test]
fn membership_fastpath_does_not_falsely_unsat_satisfiable_diseq() {
    // x = 4 (from `x + 3 = 0`), diseq `(x, __zero=0)`: SAT (4 ≠ 0). `x − 0`
    // is not in the ideal, so the fast-path must fall through to the full
    // solve and return SAT — a soundness guard against a false UNSAT.
    let sys = lin_eq_with_diseq();
    let cancel = CancelToken::none();
    let _g = crate::config::ConfigGuard::with_override(|c| c.membership_fastpath = true);
    let mut ctx = IncrementalSolverContext::new();
    ctx.solve(&sys, &cancel);
    let r = ctx.solve(&sys, &cancel);
    assert!(matches!(r, SolveOutcome::Sat(_)), "{:?}", r);
}
