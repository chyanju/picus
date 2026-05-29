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
fn ff_is_zero_unsound_full_unsat_core_is_sound() {
    // 4-poly system over F_17 that arises during the
    // `cvc5_ff_is_zero_unsound_sat` post_check trail:
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
