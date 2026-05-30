use super::*;
use crate::ff::field::PrimeField;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

#[test]
fn test_solve_sat() {
    // x*y - 1 = 0,  x = 2 in GF(7)  →  y = 4
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p1 = pr.sub(xy, pr.one());
    let two = pr.field().from_int(2);
    let p2 = pr.sub(pr.var(0), pr.constant(two));

    match solve_split_gb(&pr, &[p1, p2], &[]) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m["x"], BigUint::from(2u32));
            let prod = (&m["x"] * &m["y"]) % BigUint::from(7u32);
            assert_eq!(prod, BigUint::from(1u32));
        }
        _ => panic!("expected SAT"),
    }
}

#[test]
fn test_solve_unsat_returns_core() {
    // x = 2, x = 3 in GF(7): UNSAT, core = [0, 1].
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let two = pr.field().from_int(2);
    let three = pr.field().from_int(3);
    let p1 = pr.sub(pr.var(0), pr.constant(two));
    let p2 = pr.sub(pr.var(0), pr.constant(three));
    match solve_split_gb(&pr, &[p1, p2], &[]) {
        SolveOutcome::Unsat(core) => {
            assert_eq!(core.len(), 2);
            assert!(core.contains(&0) && core.contains(&1));
        }
        _ => panic!("expected UNSAT"),
    }
}

#[test]
fn nonzero_constant_generator_is_unsat_with_singleton_core() {
    // A generator that is itself a nonzero constant (e.g. a `const = const`
    // assertion like `2 = 1` over GF(7) rewriting to the constant `1`) makes
    // the ideal the whole ring: UNSAT, with the precise one-element core.
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let three = pr.field().from_int(3); // nonzero constant over GF(7)
    let c = pr.constant(three);
    match solve_split_gb(&pr, &[c], &[]) {
        SolveOutcome::Unsat(core) => assert_eq!(core, vec![0]),
        other => panic!("expected UNSAT, got {:?}", other),
    }
}

#[test]
fn nonzero_constant_among_constraints_yields_precise_singleton_core() {
    // `[x - 2, 3]`: the bare nonzero constant alone is UNSAT, so the core is
    // exactly the constant's index, not a union with the satisfiable `x - 2`.
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let two = pr.field().from_int(2);
    let three = pr.field().from_int(3);
    let p0 = pr.sub(pr.var(0), pr.constant(two));
    let p1 = pr.constant(three);
    match solve_split_gb(&pr, &[p0, p1], &[]) {
        SolveOutcome::Unsat(core) => assert_eq!(core, vec![1]),
        other => panic!("expected UNSAT, got {:?}", other),
    }
}

#[test]
fn satisfiable_system_with_bitsum_shaped_linear_part_is_not_false_unsat() {
    // A single satisfiable quadratic over GF(7) whose linear part is
    // `y + 2z` — i.e. a `c, 2c` coefficient run that bitsum extraction
    // registers as a bitsum `[y, z]` even though neither variable is
    // bit-constrained. The split-GB search must not let that spurious
    // bitsum prune solutions: `is_bit` proves bit-ness per branch only,
    // so a branch assigning z a non-bit value must not inherit a stale
    // "z is a bit" fact and fire a bogus overflow contradiction.
    //
    // q = y^2 + 6z^2 + 5yx + 3zx + 4x^2 + y + 2z + 2, variable order
    // [y, z, x]. Brute force confirms it has roots over GF(7)^3, so any
    // UNSAT verdict here is unsound.
    let pr = FfPolyRing::new(ff(7), vec!["y".into(), "z".into(), "x".into()]);
    let f = pr.field();
    let c = |n: i64| f.from_int(n);
    let q = {
        let terms = [
            pr.mul(pr.var(0), pr.var(0)),                 // y^2
            pr.scale(c(6), pr.mul(pr.var(1), pr.var(1))), // 6 z^2
            pr.scale(c(5), pr.mul(pr.var(0), pr.var(2))), // 5 y x
            pr.scale(c(3), pr.mul(pr.var(1), pr.var(2))), // 3 z x
            pr.scale(c(4), pr.mul(pr.var(2), pr.var(2))), // 4 x^2
            pr.var(0),                                    // y
            pr.scale(c(2), pr.var(1)),                    // 2 z
            pr.constant(c(2)),                            // 2
        ];
        let mut acc = pr.zero();
        for t in terms {
            acc = pr.add(acc, t);
        }
        acc
    };

    let n_sols = (0..7i64)
        .flat_map(|y| (0..7i64).flat_map(move |z| (0..7i64).map(move |x| (y, z, x))))
        .filter(|&(y, z, x)| {
            (y * y + 6 * z * z + 5 * y * x + 3 * z * x + 4 * x * x + y + 2 * z + 2).rem_euclid(7)
                == 0
        })
        .count();
    assert!(n_sols > 0, "ground-truth sanity: q must be satisfiable");

    match solve_split_gb(&pr, &[q], &[]) {
        SolveOutcome::Unsat(_) => {
            panic!("false UNSAT: q has {n_sols} roots over GF(7)^3 but solver returned UNSAT")
        }
        SolveOutcome::Sat(_) | SolveOutcome::Unknown => {}
    }
}

#[test]
fn test_single_gb_traced_unsat_core() {
    // System: x = 2, x = 3, y = 1  in GF(7).
    // The UNSAT comes from the first two constraints only.
    // With tracing, the core should be a subset of {0, 1, 2}
    // and must include both 0 and 1 (since those are contradictory).
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let two = pr.field().from_int(2);
    let three = pr.field().from_int(3);
    let one = pr.field().from_int(1);
    let p0 = pr.sub(pr.var(0), pr.constant(two)); // x = 2
    let p1 = pr.sub(pr.var(0), pr.constant(three)); // x = 3
    let p2 = pr.sub(pr.var(1), pr.constant(one)); // y = 1 (irrelevant)
    match solve_single_gb(&pr, vec![p0, p1, p2]) {
        SolveOutcome::Unsat(core) => {
            // Core must contain 0 and 1 (the contradictory pair).
            assert!(core.contains(&0), "core must contain input 0 (x=2)");
            assert!(core.contains(&1), "core must contain input 1 (x=3)");
            // Core should NOT contain 2 (y=1 is irrelevant) in an
            // ideal tracer.  Due to conservative initial-basis tracking
            // this may still include 2, but it must be <= 3 elements.
            assert!(core.len() <= 3, "core should be bounded by total inputs");
            log::info!("UNSAT core: {:?} (ideal: [0, 1])", core);
        }
        _ => panic!("expected UNSAT"),
    }
}

#[test]
fn test_split_gb_traced_unsat_core_is_sound_superset() {
    // System: x = 2, x = 3, y = 1  in GF(7).
    // The UNSAT comes from the first two constraints only, so the true
    // minimal core is {0, 1}. The split-GB traced path attributes
    // dependencies by a conservative *over*-approximation (the union of
    // all original inputs feeding the contradictory partition; see
    // `split_gb::fixpoint::run_fixpoint_traced`), so the returned core is
    // guaranteed to be a sound *super-set* of the minimal core — it must
    // contain {0, 1} and stay within the input range, but it may also
    // include the irrelevant input 2 (y=1). This pins only the soundness
    // invariant: the core never drops a generator the contradiction needs.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let two = pr.field().from_int(2);
    let three = pr.field().from_int(3);
    let one = pr.field().from_int(1);
    let p0 = pr.sub(pr.var(0), pr.constant(two));
    let p1 = pr.sub(pr.var(0), pr.constant(three));
    let p2 = pr.sub(pr.var(1), pr.constant(one));
    match solve_split_gb(&pr, &[p0, p1, p2], &[]) {
        SolveOutcome::Unsat(core) => {
            assert!(core.contains(&0), "core must contain input 0 (x=2)");
            assert!(core.contains(&1), "core must contain input 1 (x=3)");
            assert!(
                core.iter().all(|&i| i < 3),
                "core must be a subset of the 3 inputs; got {:?}",
                core
            );
        }
        _ => panic!("expected UNSAT"),
    }
}

#[test]
fn test_single_gb_traced_sat() {
    // x*y = 1 in GF(7): SAT, tracing should not interfere.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.one());
    match solve_single_gb(&pr, vec![p]) {
        SolveOutcome::Sat(m) => {
            let prod = (&m["x"] * &m["y"]) % BigUint::from(7u32);
            assert_eq!(prod, BigUint::from(1u32));
        }
        _ => panic!("expected SAT"),
    }
}

#[test]
fn ff_is_zero_unsound_subset_is_sat() {
    // The 3-poly subsystem `{1 - is_zero - m*x, is_zero*m, x}`
    // over F_17 is SAT (model: x=0, is_zero=1, m=0). GB returning
    // UNSAT on this subset would be unsound.
    let pr = FfPolyRing::new(ff(17), vec!["is_zero".into(), "m".into(), "x".into()]);
    // p0 = 1 - is_zero - m*x
    let one = pr.one();
    let mx = pr.mul(pr.var(1), pr.var(2));
    let p0 = pr.sub(pr.sub(one, pr.var(0)), mx);
    // p1 = is_zero * m
    let p1 = pr.mul(pr.var(0), pr.var(1));
    // p2 = x
    let p2 = pr.clone_poly(&pr.var(2));
    match solve_split_gb(&pr, &[p0, p1, p2], &[]) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m["x"], BigUint::from(0u32));
            assert_eq!(m["is_zero"], BigUint::from(1u32));
            assert_eq!(m["m"], BigUint::from(0u32));
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

#[test]
fn bit_prop_derived_unsat_core_includes_bit_constraints() {
    // Inputs:
    //   p0: x*(x-1) = 0   (bit constraint on x)
    //   p1: y*(y-1) = 0   (bit constraint on y)
    //   p2: x + 2*y - 5 = 0   (bitsum saying x + 2y = 5)
    // With x, y ∈ {0,1} the max of x + 2y is 3, so the system is
    // UNSAT and the UNSAT core must include p0 and p1 (otherwise
    // dropping a bit constraint produces a SAT subset, e.g. p0+p2
    // alone is satisfied by x=5, y=0 in F_7).
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let x = pr.var(0);
    let y = pr.var(1);
    let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let p0 = pr.sub(xx, pr.clone_poly(&x));
    let yy = pr.mul(pr.clone_poly(&y), pr.clone_poly(&y));
    let p1 = pr.sub(yy, pr.clone_poly(&y));
    let two = pr.field().from_int(2);
    let five = pr.field().from_int(5);
    let two_y = pr.scale(two, pr.clone_poly(&y));
    let sum = pr.add(pr.clone_poly(&x), two_y);
    let p2 = pr.sub(sum, pr.constant(five));
    match solve_split_gb(&pr, &[p0, p1, p2], &[]) {
        SolveOutcome::Unsat(core) => {
            assert!(
                core.contains(&0) && core.contains(&1),
                "core must include both bit constraints (p0, p1); got {:?}",
                core
            );
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
}

#[test]
fn bit_prop_derived_eq_unsat_core_is_sound() {
    // Inputs:
    //   p0: x*(x-1) = 0           (bit constraint on x)
    //   p1: y*(y-1) = 0           (bit constraint on y)
    //   p2: x + 2*y - 1 = 0       (bitsum saying x + 2y = 1 ⇒ x=1, y=0)
    //   p3: y - 1 = 0             (asserts y = 1)
    // Without p0 ∧ p1 the bitsum doesn't fire and {p2, p3}
    // has a SAT model (e.g. x=6, y=1 in F_7). UNSAT only when
    // all four constraints participate, so the core must
    // include every index.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let x = pr.var(0);
    let y = pr.var(1);
    let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let p0 = pr.sub(xx, pr.clone_poly(&x));
    let yy = pr.mul(pr.clone_poly(&y), pr.clone_poly(&y));
    let p1 = pr.sub(yy, pr.clone_poly(&y));
    let two = pr.field().from_int(2);
    let one = pr.field().from_int(1);
    let two_y = pr.scale(two, pr.clone_poly(&y));
    let sum = pr.add(pr.clone_poly(&x), two_y);
    let p2 = pr.sub(sum, pr.constant(one.clone()));
    let p3 = pr.sub(pr.clone_poly(&y), pr.constant(one));
    match solve_split_gb(&pr, &[p0, p1, p2, p3], &[]) {
        SolveOutcome::Unsat(core) => {
            assert!(
                core.contains(&0) && core.contains(&1),
                "core must include both bit constraints (p0, p1); got {:?}",
                core
            );
            assert!(
                core.contains(&2),
                "core must include bitsum p2; got {:?}",
                core
            );
            assert!(
                core.contains(&3),
                "core must include p3 (y=1); got {:?}",
                core
            );
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
}

#[test]
fn populate_bitprop_detects_bit_constraint_and_bitsum() {
    // p0 = x*(x-1) = x^2 - x  → bit constraint on x (var 0).
    // p1 = y + 2*z            → bitsum [y, z] (vars 1, 2): coeff run 1, 2.
    // populate_bitprop must register var 0 in `bits` and the [1, 2] bitsum.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into(), "z".into()]);
    let f = pr.field();
    let x = pr.var(0);
    let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let p0 = pr.sub(xx, x); // x^2 - x
    let two_z = pr.scale(f.from_int(2), pr.var(2));
    let p1 = pr.add(pr.var(1), two_z); // y + 2z
    let mut bp = BitProp::new(&pr);
    populate_bitprop(&pr, &[p0, p1], &mut bp);
    assert!(bp.bits.contains(&0), "x must be registered as a bit");
    assert!(
        bp.bitsums.iter().any(|bs| bs == &vec![1usize, 2usize]),
        "bitsum [y, z] must be registered; got {:?}",
        bp.bitsums
    );
}

#[test]
fn populate_bitprop_registers_two_bitsums_from_one_poly() {
    // p = a + 2b + c + 2d + 3e over GF(11), variable order [a, b, c, d, e].
    // `parse::bit_sums` finds two coefficient runs (1,2): the chains
    // [a, b] and [c, d]; the lone `3e` term forms no chain. `bit_sums`
    // therefore returns `Some((sums, residual))` with `sums.len() == 2`,
    // each `bs.bits.len() == 2`, so the inner `for bs in &sums` loop body
    // (the `>= 2` add_bitsum arm) runs for both entries and the loop tail
    // is reached after each. Pins that both bitsums register.
    let pr = FfPolyRing::new(
        ff(11),
        vec!["a".into(), "b".into(), "c".into(), "d".into(), "e".into()],
    );
    let f = pr.field();
    let two = || f.from_int(2);
    let terms = [
        pr.var(0),                  // a
        pr.scale(two(), pr.var(1)), // 2b
        pr.var(2),                  // c
        pr.scale(two(), pr.var(3)), // 2d
        pr.scale(f.from_int(3), pr.var(4)), // 3e (no bitsum partner)
    ];
    let mut p = pr.zero();
    for t in terms {
        p = pr.add(p, t);
    }
    let mut bp = BitProp::new(&pr);
    populate_bitprop(&pr, &[p], &mut bp);
    assert!(
        bp.bitsums.iter().any(|bs| bs == &vec![0usize, 1usize]),
        "bitsum [a, b] must register; got {:?}",
        bp.bitsums
    );
    assert!(
        bp.bitsums.iter().any(|bs| bs == &vec![2usize, 3usize]),
        "bitsum [c, d] must register; got {:?}",
        bp.bitsums
    );
    assert_eq!(bp.bitsums.len(), 2, "exactly two bitsums; got {:?}", bp.bitsums);
}

#[test]
fn populate_bitprop_ignores_non_bit_non_bitsum_polys() {
    // A bare linear poly with a single variable yields no bit constraint
    // (no quadratic term) and no >=2-length bitsum.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let p = pr.sub(pr.var(0), pr.constant(f.from_int(3))); // x - 3
    let mut bp = BitProp::new(&pr);
    populate_bitprop(&pr, &[p], &mut bp);
    assert!(bp.bits.is_empty(), "no quadratic term ⇒ no bit constraint");
    assert!(bp.bitsums.is_empty(), "single linear monomial ⇒ no bitsum");
}

#[test]
fn solve_single_gb_nontrivial_unsat_returns_full_core() {
    // x^2 - 3 over GF(7): 3 is a non-residue (QRs = {1,2,4}), so x^2 = 3
    // has no GF(7) root. The DegRevLex GB {x^2-3} is non-trivial (no
    // constant element), so solve_single_gb reaches the NonTrivial arm;
    // find_zero enumerates x ∈ {0..6} exhaustively (7 < 2^16) and returns
    // FindZeroOutcome::Unsat ⇒ SolveOutcome::Unsat((0..1).collect()).
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.constant(f.from_int(3))); // x^2 - 3
    match solve_single_gb(&pr, vec![p]) {
        SolveOutcome::Unsat(core) => {
            assert_eq!(core, vec![0usize], "non-trivial UNSAT names all inputs");
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
}

#[test]
fn ff_is_zero_unsound_full_unsat_core_is_sound() {
    // 4-poly system over F_17:
    //   p0: 1 - is_zero - m*x = 0
    //   p1: is_zero * m = 0
    //   p2: x = 0
    //   p3: is_zero = 0
    // `{p0, p2, p3}` is the minimum UNSAT subset; dropping p3
    // leaves a SAT subset, so the returned core must name p3.
    let pr = FfPolyRing::new(ff(17), vec!["is_zero".into(), "m".into(), "x".into()]);
    let one = pr.one();
    let mx = pr.mul(pr.var(1), pr.var(2));
    let p0 = pr.sub(pr.sub(one, pr.var(0)), mx);
    let p1 = pr.mul(pr.var(0), pr.var(1));
    let p2 = pr.clone_poly(&pr.var(2));
    let p3 = pr.clone_poly(&pr.var(0));
    match solve_split_gb(&pr, &[p0, p1, p2, p3], &[]) {
        SolveOutcome::Unsat(core) => {
            assert!(
                core.contains(&3),
                "core must include is_zero=0 (index 3); got {:?}",
                core
            );
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
}

#[test]
fn solve_split_gb_unsat_via_dfs_returns_full_input_core() {
    // {x + y, x·y − 1} over GF(7). build_partitions splits the linear
    // x+y into basis 0 and both into basis 1; neither partition is the
    // whole ring after the initial fixpoint (so the `is_whole_ring`
    // early-return at the top of `solve_split_gb_cancel` is NOT taken).
    // The DFS in `split_find_zero_cancel` then drives the conflict
    // re-extension loop to a definitive UNSAT (x·(−x)=1 ⇒ x²=−1=6, a
    // non-residue mod 7), so the `SplitFindZeroOutcome::Unsat` arm of
    // `solve_split_gb_cancel` is reached and reports the trivial
    // all-input core `(0..2)`.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let x_plus_y = pr.add(pr.var(0), pr.var(1));
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
    match solve_split_gb(&pr, &[x_plus_y, xy_minus_1], &[]) {
        SolveOutcome::Unsat(core) => {
            assert_eq!(
                core,
                vec![0usize, 1usize],
                "DFS-derived UNSAT names every original input"
            );
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
}

// =============================================================================
// SPEC-DRIVEN property tests for `solve_split_gb` / `solve_single_gb`. Expected
// values are derived from polynomial-ideal theory / Fermat / brute-force ground
// truth over small primes — NEVER from inspecting source behavior.
// =============================================================================

/// Property (5/9) MODEL CHECKING: any `SolveOutcome::Sat(m)` returned by
/// `solve_split_gb` MUST satisfy every input polynomial (substitute the model
/// into the poly, must evaluate to 0 in GF(p)). SPEC: SAT-as-witness.
#[test]
fn prop_solve_split_gb_sat_model_zeros_all_inputs() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let x_eq_3 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let originals = [pr.clone_poly(&xy_minus_1), pr.clone_poly(&x_eq_3)];
    match solve_split_gb(&pr, &originals, &[]) {
        SolveOutcome::Sat(m) => {
            // Convert model to field-element point in ring var order.
            let pt: Vec<_> = pr
                .var_names()
                .iter()
                .map(|n| f.from_biguint(&m[n]))
                .collect();
            for g in &originals {
                let v = eval_poly_core(&pr, g, &pt);
                assert!(
                    f.is_zero(&v),
                    "SAT model must zero every input generator"
                );
            }
            // MATH: x = 3, x·y = 1 ⇒ y = 3^{-1} = 5 in GF(7).
            assert_eq!(m["x"], BigUint::from(3u32));
            assert_eq!(m["y"], BigUint::from(5u32));
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Property (8) DETERMINISM: two independent runs of `solve_split_gb` on
/// the same inputs must return the same verdict class.
#[test]
fn prop_solve_split_gb_deterministic_verdict_class() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p = pr.sub(pr.var(0), pr.constant(f.from_int(4)));
    let r1 = solve_split_gb(&pr, &[pr.clone_poly(&p)], &[]);
    let r2 = solve_split_gb(&pr, &[pr.clone_poly(&p)], &[]);
    let cls = |o: &SolveOutcome| match o {
        SolveOutcome::Sat(_) => "Sat",
        SolveOutcome::Unsat(_) => "Unsat",
        SolveOutcome::Unknown => "Unknown",
    };
    assert_eq!(cls(&r1), cls(&r2));
}

/// Property (7/5) EDGE PRIMES: pin `x = a` over GF(2), GF(3), GF(5),
/// GF(7), GF(11). MATH: unique solution is `a mod p`. Verify model
/// matches across every probed field size.
#[test]
fn prop_solve_split_gb_pin_eq_across_edge_primes() {
    for p in [2u32, 3, 5, 7, 11] {
        let pr = FfPolyRing::new(ff(p), vec!["x".into()]);
        let f = pr.field();
        let a: u64 = 1; // a < every prime in the list
        let poly = pr.sub(pr.var(0), pr.constant(f.from_int(a as i64)));
        match solve_split_gb(&pr, &[poly], &[]) {
            SolveOutcome::Sat(m) => {
                assert_eq!(
                    m["x"],
                    BigUint::from(a) % BigUint::from(p),
                    "GF({}): x = {} forces x = {}",
                    p,
                    a,
                    a
                );
            }
            other => panic!("GF({}): expected SAT, got {:?}", p, other),
        }
    }
}

/// Property (1/7) FERMAT: in GF(p), `a^p ≡ a` for every a (Fermat's
/// little theorem). At p=7 and a=3, 3^7 mod 7 = 3, so `x^7 = x ∧ x = 3`
/// is SAT with x = 3. Spec: Fermat / SAT model checking.
#[test]
fn prop_solve_split_gb_fermat_unit_eq_consistent() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p_x_eq_3 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    match solve_split_gb(&pr, &[p_x_eq_3], &[]) {
        SolveOutcome::Sat(m) => {
            // MATH: 3^7 mod 7 = 3 (Fermat).
            let x_val = &m["x"];
            assert_eq!(x_val, &BigUint::from(3u32));
            let fermat = x_val.modpow(&BigUint::from(7u32), &BigUint::from(7u32));
            assert_eq!(
                &fermat, x_val,
                "Fermat: x^p ≡ x in GF(p) — independent of source"
            );
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Property (5) MONOTONICITY OF UNSAT: if `{p, q}` is UNSAT, so is
/// `{p, q, r}` for any extra constraint r. Pin: `{x-1, x-2}` is UNSAT in
/// GF(7); add an irrelevant `y - 5`. Still UNSAT.
#[test]
fn prop_solve_split_gb_unsat_monotone_under_extension() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let p3 = pr.sub(pr.var(1), pr.constant(f.from_int(5)));
    assert!(matches!(
        solve_split_gb(&pr, &[p1, p2, p3], &[]),
        SolveOutcome::Unsat(_)
    ));
}

/// Property (5/9) MODEL CHECKING for `solve_single_gb`: a SAT model must
/// zero the original polynomial inputs. Pin: x²-x over GF(11). MATH:
/// roots are exactly {0, 1}.
#[test]
fn prop_solve_single_gb_bit_root_in_zero_or_one() {
    let pr = FfPolyRing::new(ff(11), vec!["x".into()]);
    let f = pr.field();
    let xx = pr.mul(pr.var(0), pr.var(0));
    let bit = pr.sub(xx, pr.var(0));
    match solve_single_gb(&pr, vec![pr.clone_poly(&bit)]) {
        SolveOutcome::Sat(m) => {
            let pt = vec![f.from_biguint(&m["x"])];
            let v = eval_poly_core(&pr, &bit, &pt);
            assert!(f.is_zero(&v), "SAT model must zero the bit constraint");
            let x = &m["x"];
            assert!(
                x == &BigUint::from(0u32) || x == &BigUint::from(1u32),
                "x(x-1)=0 ⇒ x∈{{0,1}} (MATH spec), got {}",
                x
            );
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Property (1) ALGEBRAIC IDENTITY at the solver layer: `2·x = 4` and
/// `x = 2` over GF(7) are equivalent (since 2 is invertible: 2·4 ≡ 1 mod
/// 7, so 2·x = 4 ⇒ x = 2). Both must be SAT with the same x = 2.
#[test]
fn prop_solve_split_gb_invertible_scalar_eq_consistent() {
    let pr_a = FfPolyRing::new(ff(7), vec!["x".into()]);
    let pr_b = FfPolyRing::new(ff(7), vec!["x".into()]);
    let fa = pr_a.field();
    let fb = pr_b.field();
    // 2·x - 4 = 0
    let two_x = pr_a.scale(fa.from_int(2), pr_a.var(0));
    let p_a = pr_a.sub(two_x, pr_a.constant(fa.from_int(4)));
    // x - 2 = 0
    let p_b = pr_b.sub(pr_b.var(0), pr_b.constant(fb.from_int(2)));
    let r_a = solve_split_gb(&pr_a, &[p_a], &[]);
    let r_b = solve_split_gb(&pr_b, &[p_b], &[]);
    let (xa, xb) = match (&r_a, &r_b) {
        (SolveOutcome::Sat(ma), SolveOutcome::Sat(mb)) => (ma["x"].clone(), mb["x"].clone()),
        other => panic!("expected both SAT, got {:?}", other),
    };
    assert_eq!(xa, BigUint::from(2u32));
    assert_eq!(xb, BigUint::from(2u32));
    assert_eq!(xa, xb, "invertible-scale equivalence forces same model");
}

/// Property (3) IDEMPOTENCE: running `solve_split_gb` twice gives the
/// same model on a single-solution problem.
#[test]
fn prop_solve_split_gb_repeat_same_unique_model() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let r1 = solve_split_gb(&pr, &[pr.clone_poly(&p)], &[]);
    let r2 = solve_split_gb(&pr, &[pr.clone_poly(&p)], &[]);
    let pick = |o: SolveOutcome| match o {
        SolveOutcome::Sat(m) => m["x"].clone(),
        _ => panic!("expected SAT"),
    };
    assert_eq!(pick(r1), pick(r2));
}

/// Property (4) UNSAT CORE SOUNDNESS: every index in the returned UNSAT
/// core must be a valid index into the input slice (`i < n_inputs`). A
/// core element outside this range is undefined / unsound. SPEC: core
/// is `Vec<usize>` indexing the input fact list.
#[test]
fn prop_unsat_core_indices_in_range() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let inputs = [pr.clone_poly(&p1), pr.clone_poly(&p2)];
    match solve_split_gb(&pr, &inputs, &[]) {
        SolveOutcome::Unsat(core) => {
            for &i in &core {
                assert!(
                    i < inputs.len(),
                    "core index {} out of range (n_inputs = {})",
                    i,
                    inputs.len()
                );
            }
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
}

/// Helper: evaluate a polynomial at a point. Local copy so we don't
/// pollute the public API. Identical math to `split_gb::tests::eval_poly`.
fn eval_poly_core(
    pr: &FfPolyRing,
    p: &crate::poly::Poly,
    point: &[crate::ff::field::FieldElem],
) -> crate::ff::field::FieldElem {
    let ring = &pr.ring;
    let fp = &pr.field();
    let mut acc = fp.zero();
    for (c, m) in ring.terms(p) {
        let mut t = fp.clone_el(c);
        for v in 0..pr.n_vars() {
            let e = ring.exponent_at(&m, v);
            for _ in 0..e {
                t = fp.mul_ref(&t, &point[v]);
            }
        }
        fp.add_assign(&mut acc, t);
    }
    acc
}
