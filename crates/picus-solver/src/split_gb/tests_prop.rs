use super::*;
use crate::ff::field::PrimeField;
use crate::frontend::bitprop::BitProp;
use num_bigint::BigUint;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

/// Evaluate `p` at the given point. Local copy mirroring
/// `tests::eval_poly` (helpers stay duplicated rather than shared via
/// `pub(super)` to keep the source mod free of test-only items).
fn eval_poly(pr: &FfPolyRing, p: &Poly, point: &[FieldElem]) -> FieldElem {
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

/// Evaluate a polynomial at a point and return whether it's zero.
fn evals_to_zero(pr: &FfPolyRing, p: &Poly, pt: &[FieldElem]) -> bool {
    pr.field().is_zero(&eval_poly(pr, p, pt))
}

// =============================================================================
// SPEC-DRIVEN property tests for split-GB. Expected values come from FIELD
// MATH / IDEAL THEORY, not from inspecting solver source. A failing test
// here means the spec is violated — either a wrong model, a spurious UNSAT,
// or a missed monotonicity property.
// =============================================================================

/// Property (5/9) MODEL CHECKING: every SAT model returned by
/// `split_find_zero` MUST zero every input generator. This is the
/// SOUNDNESS contract of a SAT verdict. Pin: `x·y - 1 = 0` ∧ `x = 2`
/// over GF(7) ⇒ y = 4 (since 2·4 = 8 ≡ 1 mod 7). MATH-derived.
#[test]
fn prop_split_sat_model_zeros_inputs_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let x_eq_2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let originals = vec![pr.clone_poly(&xy_minus_1), pr.clone_poly(&x_eq_2)];
    let gens: Vec<Vec<Poly>> = vec![vec![pr.clone_poly(&x_eq_2)], vec![xy_minus_1, x_eq_2]];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, gens, &mut bp);
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            for g in &originals {
                assert!(
                    evals_to_zero(&pr, g, &pt),
                    "SAT model must zero every original generator"
                );
            }
            // MATH-derived unique-solution check.
            assert_eq!(
                pr.field().to_biguint(&pt[0]),
                BigUint::from(2u32),
                "x = 2 forces x"
            );
            assert_eq!(
                pr.field().to_biguint(&pt[1]),
                BigUint::from(4u32),
                "x·y = 1, x = 2 ⇒ y = 4 in GF(7)"
            );
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Property (7) EDGE PRIMES: solve `x = a, y = b` over multiple primes.
/// MATH: each system pins one (x, y) point. Verify model values.
#[test]
fn prop_split_sat_two_eqs_pin_solution_across_primes() {
    for p in [2u32, 3, 5, 7, 11, 101] {
        let pr = FfPolyRing::new(ff(p), vec!["x".into(), "y".into()]);
        let f = pr.field();
        let a = 1u64; // a < every test prime
        let b = if p > 2 { 2u64 } else { 0u64 };
        let p_x = pr.sub(pr.var(0), pr.constant(f.from_int(a as i64)));
        let p_y = pr.sub(pr.var(1), pr.constant(f.from_int(b as i64)));
        let originals = vec![pr.clone_poly(&p_x), pr.clone_poly(&p_y)];
        let gens: Vec<Vec<Poly>> = vec![vec![pr.clone_poly(&p_x), pr.clone_poly(&p_y)], vec![p_x, p_y]];
        let mut bp = BitProp::new(&pr);
        let basis = split_gb(&pr, gens, &mut bp);
        match split_find_zero(&pr, basis, &mut bp) {
            SplitFindZeroOutcome::Sat(pt) => {
                for g in &originals {
                    assert!(
                        evals_to_zero(&pr, g, &pt),
                        "GF({}): model must zero generator",
                        p
                    );
                }
                assert_eq!(
                    pr.field().to_biguint(&pt[0]),
                    BigUint::from(a) % BigUint::from(p),
                    "GF({}): x pinned",
                    p
                );
                assert_eq!(
                    pr.field().to_biguint(&pt[1]),
                    BigUint::from(b) % BigUint::from(p),
                    "GF({}): y pinned",
                    p
                );
            }
            other => panic!("GF({}): expected SAT, got {:?}", p, other),
        }
    }
}

/// Property (5) UNSAT BY ELEMENT DISTINCTNESS: `x - a` and `x - b` with
/// `a ≠ b mod p` together generate the unit ideal (their difference is
/// the nonzero constant `b - a`). Spec: distinct points are incompatible.
/// Try across edge primes.
#[test]
fn prop_distinct_constants_force_unsat_across_primes() {
    for p in [3u32, 5, 7, 11, 101] {
        let pr = FfPolyRing::new(ff(p), vec!["x".into()]);
        let f = pr.field();
        let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
        let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
        let originals = vec![pr.clone_poly(&p1), pr.clone_poly(&p2)];
        let mut bp = BitProp::new(&pr);
        let basis = split_gb(
            &pr,
            vec![
                vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
                vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
            ],
            &mut bp,
        );
        // Either the basis becomes the whole ring at fixpoint OR the DFS
        // proves UNSAT. Both routes assert UNSAT.
        let is_whole = basis.iter().any(|b| b.is_whole_ring());
        if !is_whole {
            match split_find_zero(&pr, basis, &mut bp) {
                SplitFindZeroOutcome::Unsat => {}
                other => panic!("GF({}): expected UNSAT, got {:?}", p, other),
            }
        }
        // The (1 - 0) negation property: input `p1` and `p2` cannot
        // coexist with a witness. Confirm: any putative point fails one.
        for v in 0..p {
            let pt = vec![f.from_int(v as i64)];
            assert!(
                !(evals_to_zero(&pr, &originals[0], &pt) && evals_to_zero(&pr, &originals[1], &pt)),
                "GF({}): no element of GF can satisfy both x=1 and x=2",
                p
            );
        }
    }
}

/// Property (8) DETERMINISM: two independent split-GB runs on the same
/// input must return the same outcome class (Sat / Unsat / Unknown).
/// `split_gb` and `split_find_zero` must be pure functions of input.
#[test]
fn prop_split_determinism_two_calls() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p1 = pr.sub(xy, pr.constant(f.from_int(2)));
    let mut bp1 = BitProp::new(&pr);
    let basis1 = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p1)]], &mut bp1);
    let r1 = split_find_zero(&pr, basis1, &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis2 = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p1)]], &mut bp2);
    let r2 = split_find_zero(&pr, basis2, &mut bp2);
    let cls = |o: &SplitFindZeroOutcome| match o {
        SplitFindZeroOutcome::Sat(_) => "Sat",
        SplitFindZeroOutcome::Unsat => "Unsat",
        SplitFindZeroOutcome::Unknown => "Unknown",
    };
    assert_eq!(cls(&r1), cls(&r2), "split-GB verdict must be deterministic");
}

/// Property (3) IDEMPOTENCE: running `split_gb` on a basis already at
/// fixpoint (i.e. the output of a prior `split_gb` run) gives the same
/// "is whole ring" verdict per partition. Spec: a fixpoint is a fixpoint.
#[test]
fn prop_split_gb_idempotent_whole_ring_flag() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let basis1 = split_gb(
        &pr,
        vec![vec![pr.clone_poly(&p1), pr.clone_poly(&p2)], vec![p1, p2]],
        &mut bp,
    );
    let whole1: Vec<bool> = basis1.iter().map(|b| b.is_whole_ring()).collect();
    // Feed each fixpoint basis back as input.
    let gens: Vec<Vec<Poly>> = basis1
        .iter()
        .map(|b| b.basis.iter().map(|p| pr.clone_poly(p)).collect())
        .collect();
    let basis2 = split_gb(&pr, gens, &mut bp);
    let whole2: Vec<bool> = basis2.iter().map(|b| b.is_whole_ring()).collect();
    assert_eq!(whole1, whole2, "fixpoint of fixpoint is fixpoint");
}

/// Property (5) UNSAT BY NON-RESIDUE: `x² - 3 = 0` over GF(7). MATH: the
/// quadratic residues of GF(7) are {0, 1, 2, 4} (squares of 0..6 mod 7),
/// so 3 is NOT a QR ⇒ no solution. Must be UNSAT.
#[test]
fn prop_non_residue_squared_eq_is_unsat_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p)]], &mut bp);
    let is_whole = basis.iter().any(|b| b.is_whole_ring());
    // Either the whole-ring fixpoint catches it, or DFS proves UNSAT.
    let result = if is_whole {
        SplitFindZeroOutcome::Unsat
    } else {
        split_find_zero(&pr, basis, &mut bp)
    };
    assert!(
        matches!(result, SplitFindZeroOutcome::Unsat),
        "x² = 3 over GF(7) is UNSAT (3 is a non-residue), got {:?}",
        result
    );
    // Ground-truth: brute force confirms zero roots.
    let n = (0..7u32)
        .filter(|&v| (v * v) % 7 == 3)
        .count();
    assert_eq!(n, 0, "ground truth: 3 has no square root in GF(7)");
}

/// Property (5) MODEL VALIDITY for x² - 4 = 0 over GF(7): roots are 2 and
/// 5 (MATH: 2² = 4, 5² = 25 ≡ 4 mod 7). A SAT model must return one of
/// them. Pin: the returned x must satisfy x² ≡ 4.
#[test]
fn prop_quadratic_residue_root_is_valid_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.constant(f.from_int(4)));
    let originals = vec![pr.clone_poly(&p)];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p)]], &mut bp);
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert!(evals_to_zero(&pr, &originals[0], &pt));
            let x = pr.field().to_biguint(&pt[0]);
            assert!(
                x == BigUint::from(2u32) || x == BigUint::from(5u32),
                "x² = 4 mod 7 ⇒ x ∈ {{2, 5}}, got {}",
                x
            );
        }
        other => panic!("expected SAT (x ∈ {{2,5}}), got {:?}", other),
    }
}

/// Property (6) BIT-PROP SPEC: `x · (x - 1) = 0` over GF(p) forces
/// x ∈ {0, 1}. Solve and check the returned model. MATH: roots of the
/// polynomial are exactly 0 and 1. Memory says bitprop is a recurring
/// hazard — probe it on multiple primes.
#[test]
fn prop_bit_constraint_forces_zero_or_one() {
    for p in [3u32, 5, 7, 11, 101] {
        let pr = FfPolyRing::new(ff(p), vec!["x".into()]);
        let f = pr.field();
        let xx = pr.mul(pr.var(0), pr.var(0));
        let bit = pr.sub(xx, pr.var(0)); // x² - x = x(x-1)
        let originals = vec![pr.clone_poly(&bit)];
        let mut bp = BitProp::new(&pr);
        let basis = split_gb(
            &pr,
            vec![vec![], vec![pr.clone_poly(&bit)]],
            &mut bp,
        );
        match split_find_zero(&pr, basis, &mut bp) {
            SplitFindZeroOutcome::Sat(pt) => {
                assert!(evals_to_zero(&pr, &originals[0], &pt));
                let x = pr.field().to_biguint(&pt[0]);
                assert!(
                    x == BigUint::from(0u32) || x == BigUint::from(1u32),
                    "GF({}): x(x-1)=0 ⇒ x∈{{0,1}}, got {}",
                    p,
                    x
                );
            }
            other => panic!("GF({}): expected SAT, got {:?}", p, other),
        }
    }
}

/// Property (6) BIT-DECOMPOSITION SPEC: three bit vars `b0, b1, b2` with
/// the bitsum constraint `x = b0 + 2·b1 + 4·b2`. MATH: x ∈ [0, 8). If we
/// also pin `x = 5`, the unique decomposition is b0=1, b1=0, b2=1 (binary
/// representation of 5). Probe the bitprop pipeline on a recurring hazard.
#[test]
fn prop_bitsum_decomposition_matches_binary_repr() {
    let pr = FfPolyRing::new(
        ff(11),
        vec!["b0".into(), "b1".into(), "b2".into(), "x".into()],
    );
    let f = pr.field();
    // Bit constraints: bi · (bi - 1) = 0 for i in 0..3.
    let b0 = pr.var(0);
    let b1 = pr.var(1);
    let b2 = pr.var(2);
    let bit0 = pr.sub(pr.mul(pr.clone_poly(&b0), pr.clone_poly(&b0)), pr.clone_poly(&b0));
    let bit1 = pr.sub(pr.mul(pr.clone_poly(&b1), pr.clone_poly(&b1)), pr.clone_poly(&b1));
    let bit2 = pr.sub(pr.mul(pr.clone_poly(&b2), pr.clone_poly(&b2)), pr.clone_poly(&b2));
    // bitsum: x = b0 + 2 b1 + 4 b2.
    let two_b1 = pr.scale(f.from_int(2), pr.clone_poly(&b1));
    let four_b2 = pr.scale(f.from_int(4), pr.clone_poly(&b2));
    let sum_expr = pr.add(pr.add(pr.clone_poly(&b0), two_b1), four_b2);
    let bitsum_minus_x = pr.sub(sum_expr, pr.var(3));
    // x = 5.
    let x_pin = pr.sub(pr.var(3), pr.constant(f.from_int(5)));

    let originals = vec![
        pr.clone_poly(&bit0),
        pr.clone_poly(&bit1),
        pr.clone_poly(&bit2),
        pr.clone_poly(&bitsum_minus_x),
        pr.clone_poly(&x_pin),
    ];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![
            originals.iter().map(|p| pr.clone_poly(p)).collect(),
            originals.iter().map(|p| pr.clone_poly(p)).collect(),
        ],
        &mut bp,
    );
    if basis.iter().any(|b| b.is_whole_ring()) {
        panic!("decomposition of 5 in 3 bits is SAT (binary 101), not UNSAT");
    }
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            // Every original must zero at the witness.
            for g in &originals {
                assert!(
                    evals_to_zero(&pr, g, &pt),
                    "SAT model must zero every constraint"
                );
            }
            // MATH: 5 = 1·1 + 2·0 + 4·1, so b0=1, b1=0, b2=1.
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(1u32));
            assert_eq!(pr.field().to_biguint(&pt[1]), BigUint::from(0u32));
            assert_eq!(pr.field().to_biguint(&pt[2]), BigUint::from(1u32));
            assert_eq!(pr.field().to_biguint(&pt[3]), BigUint::from(5u32));
        }
        other => panic!("expected SAT (b0=1,b1=0,b2=1,x=5), got {:?}", other),
    }
}

/// Property (6) BIT-DECOMPOSITION RANGE SPEC: n-bit decomposition forces
/// x ∈ [0, 2^n). Pin: 3 bits constraint with x pinned to 8 (i.e. 2^3, out
/// of range). MATH: 8 cannot be written as b0+2b1+4b2 with bi ∈ {0,1} —
/// max is 1+2+4 = 7. Must be UNSAT.
#[test]
fn prop_bit_decomposition_out_of_range_is_unsat() {
    let pr = FfPolyRing::new(
        ff(11),
        vec!["b0".into(), "b1".into(), "b2".into(), "x".into()],
    );
    let f = pr.field();
    let b0 = pr.var(0);
    let b1 = pr.var(1);
    let b2 = pr.var(2);
    let bit0 = pr.sub(pr.mul(pr.clone_poly(&b0), pr.clone_poly(&b0)), pr.clone_poly(&b0));
    let bit1 = pr.sub(pr.mul(pr.clone_poly(&b1), pr.clone_poly(&b1)), pr.clone_poly(&b1));
    let bit2 = pr.sub(pr.mul(pr.clone_poly(&b2), pr.clone_poly(&b2)), pr.clone_poly(&b2));
    let two_b1 = pr.scale(f.from_int(2), pr.clone_poly(&b1));
    let four_b2 = pr.scale(f.from_int(4), pr.clone_poly(&b2));
    let sum_expr = pr.add(pr.add(pr.clone_poly(&b0), two_b1), four_b2);
    let bitsum_minus_x = pr.sub(sum_expr, pr.var(3));
    let x_pin = pr.sub(pr.var(3), pr.constant(f.from_int(8))); // 8 ∉ [0, 8)

    let originals = vec![bit0, bit1, bit2, bitsum_minus_x, x_pin];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![
            originals.iter().map(|p| pr.clone_poly(p)).collect(),
            originals.iter().map(|p| pr.clone_poly(p)).collect(),
        ],
        &mut bp,
    );
    let is_whole = basis.iter().any(|b| b.is_whole_ring());
    let result = if is_whole {
        SplitFindZeroOutcome::Unsat
    } else {
        split_find_zero(&pr, basis, &mut bp)
    };
    assert!(
        matches!(result, SplitFindZeroOutcome::Unsat),
        "x=8 with 3-bit decomp must be UNSAT (max is 7), got {:?}",
        result
    );
}

/// Property (6) BIT-PROP SOUNDNESS PROBE: the GF(7) quadratic from
/// `core_tests.rs::satisfiable_system_with_bitsum_shaped_linear_part_is_not_false_unsat`
/// has a confirmed-positive root count. Same shape, here at the split-GB
/// layer: a single satisfiable polynomial whose linear part has a `1,2`
/// coefficient run is exposed as a bitsum candidate. Spec: a bitsum
/// pattern alone (without bit constraints proving bit-ness) MUST NOT
/// prune SAT models. Memory R5 H1 / R7 J1 both bitprop, hence probe HARD.
#[test]
fn prop_bitsum_shaped_linear_does_not_force_false_unsat_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["y".into(), "z".into(), "x".into()]);
    let f = pr.field();
    let c = |n: i64| f.from_int(n);
    let q = {
        let terms = [
            pr.mul(pr.var(0), pr.var(0)),
            pr.scale(c(6), pr.mul(pr.var(1), pr.var(1))),
            pr.scale(c(5), pr.mul(pr.var(0), pr.var(2))),
            pr.scale(c(3), pr.mul(pr.var(1), pr.var(2))),
            pr.scale(c(4), pr.mul(pr.var(2), pr.var(2))),
            pr.var(0),
            pr.scale(c(2), pr.var(1)),
            pr.constant(c(2)),
        ];
        let mut acc = pr.zero();
        for t in terms {
            acc = pr.add(acc, t);
        }
        acc
    };
    // Brute force confirms SAT (MATH ground truth, not source).
    let n_sols = (0..7i64)
        .flat_map(|y| (0..7i64).flat_map(move |z| (0..7i64).map(move |x| (y, z, x))))
        .filter(|&(y, z, x)| {
            (y * y + 6 * z * z + 5 * y * x + 3 * z * x + 4 * x * x + y + 2 * z + 2).rem_euclid(7)
                == 0
        })
        .count();
    assert!(n_sols > 0, "GF(7) sanity: q is satisfiable");
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&q)]], &mut bp);
    let is_whole = basis.iter().any(|b| b.is_whole_ring());
    if is_whole {
        panic!(
            "false UNSAT at fixpoint: q has {} GF(7)^3 roots but basis went to whole ring",
            n_sols
        );
    }
    // The DFS may legitimately come back Unknown/Sat — never Unsat.
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Unsat => panic!(
            "false UNSAT: q has {} GF(7)^3 roots but split-GB returned Unsat",
            n_sols
        ),
        SplitFindZeroOutcome::Sat(_) | SplitFindZeroOutcome::Unknown => {}
    }
}

/// Property (7) GF(2) edge prime: solve `x = 1` over GF(2). MATH: the
/// unique solution is x = 1. GF(2) is the smallest finite field and is
/// usually a corner case for prime-size assumptions.
#[test]
fn prop_gf2_unit_eq_returns_one() {
    let pr = FfPolyRing::new(ff(2), vec!["x".into()]);
    let f = pr.field();
    let p = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let originals = vec![pr.clone_poly(&p)];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![pr.clone_poly(&p)], vec![p]], &mut bp);
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert!(evals_to_zero(&pr, &originals[0], &pt));
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(1u32));
        }
        other => panic!("GF(2): expected SAT(x=1), got {:?}", other),
    }
}

/// Property (1) ALGEBRAIC IDENTITY at solver scale: `x = a` and `x + 0 = a`
/// must give the same verdict (additive identity). Spec: `+0` is a no-op.
#[test]
fn prop_additive_identity_doesnt_change_verdict() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p_a = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let zero_poly = pr.zero();
    let p_b = pr.add(pr.sub(pr.var(0), pr.constant(f.from_int(3))), zero_poly);
    let mut bp1 = BitProp::new(&pr);
    let basis_a = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p_a)]], &mut bp1);
    let r_a = split_find_zero(&pr, basis_a, &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis_b = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p_b)]], &mut bp2);
    let r_b = split_find_zero(&pr, basis_b, &mut bp2);
    let cls = |o: &SplitFindZeroOutcome| match o {
        SplitFindZeroOutcome::Sat(_) => "Sat",
        SplitFindZeroOutcome::Unsat => "Unsat",
        SplitFindZeroOutcome::Unknown => "Unknown",
    };
    assert_eq!(
        cls(&r_a),
        cls(&r_b),
        "(p) and (p + 0) must give same verdict"
    );
    if let (SplitFindZeroOutcome::Sat(pt_a), SplitFindZeroOutcome::Sat(pt_b)) = (&r_a, &r_b) {
        assert_eq!(
            pr.field().to_biguint(&pt_a[0]),
            pr.field().to_biguint(&pt_b[0]),
            "same SAT model"
        );
    }
}

/// Property (1) ALGEBRAIC IDENTITY: scaling a constraint by 1 is a no-op.
/// `(x - 3) = 0` and `1·(x - 3) = 0` must give identical verdicts.
#[test]
fn prop_scalar_one_does_not_change_verdict() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p_a = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let p_b = pr.scale(f.one(), pr.clone_poly(&p_a));
    let mut bp1 = BitProp::new(&pr);
    let basis_a = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p_a)]], &mut bp1);
    let r_a = split_find_zero(&pr, basis_a, &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis_b = split_gb(&pr, vec![vec![], vec![p_b]], &mut bp2);
    let r_b = split_find_zero(&pr, basis_b, &mut bp2);
    let cls = |o: &SplitFindZeroOutcome| match o {
        SplitFindZeroOutcome::Sat(_) => "Sat",
        SplitFindZeroOutcome::Unsat => "Unsat",
        SplitFindZeroOutcome::Unknown => "Unknown",
    };
    assert_eq!(cls(&r_a), cls(&r_b));
}

/// Property (4) BASIS INVARIANT POST-`split_gb`: every input generator
/// MUST belong to the ideal of its partition's output basis (membership
/// is the SOUNDNESS of a Groebner basis). Pin: simple linear system.
#[test]
fn prop_split_gb_basis_contains_inputs() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let p2 = pr.sub(pr.var(1), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![
            vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
            vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
        ],
        &mut bp,
    );
    // Every input must reduce to zero against each partition's GB.
    for b in &basis {
        assert!(
            b.contains(&p1),
            "partition basis must contain input p1 (x - 2)"
        );
        assert!(
            b.contains(&p2),
            "partition basis must contain input p2 (y - 3)"
        );
    }
}

/// Property (3) IDEMPOTENCE on the model layer: calling `split_find_zero`
/// twice on the same fresh basis (rebuilt from the same input both times)
/// yields the same outcome class. Spec: function purity.
#[test]
fn prop_split_find_zero_idempotent_outcome_class() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let x_eq_2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp1 = BitProp::new(&pr);
    let basis1 = split_gb(
        &pr,
        vec![
            vec![pr.clone_poly(&x_eq_2)],
            vec![pr.clone_poly(&xy_minus_1), pr.clone_poly(&x_eq_2)],
        ],
        &mut bp1,
    );
    let r1 = split_find_zero(&pr, basis1, &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis2 = split_gb(
        &pr,
        vec![
            vec![pr.clone_poly(&x_eq_2)],
            vec![pr.clone_poly(&xy_minus_1), pr.clone_poly(&x_eq_2)],
        ],
        &mut bp2,
    );
    let r2 = split_find_zero(&pr, basis2, &mut bp2);
    let cls = |o: &SplitFindZeroOutcome| match o {
        SplitFindZeroOutcome::Sat(_) => "Sat",
        SplitFindZeroOutcome::Unsat => "Unsat",
        SplitFindZeroOutcome::Unknown => "Unknown",
    };
    assert_eq!(cls(&r1), cls(&r2));
}
