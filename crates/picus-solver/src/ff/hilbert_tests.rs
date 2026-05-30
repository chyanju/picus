use super::*;

fn x(n_vars: usize, var: usize, exp: u16) -> Monomial {
    Monomial::single_var(n_vars, var, exp)
}

fn from_exps(e: Vec<u16>) -> Monomial {
    Monomial::from_exponents(e)
}

#[test]
fn hn_empty_ideal_is_one() {
    let hn = hilbert_numerator(&[]);
    assert_eq!(hn, HilbertNum::one());
}

#[test]
fn hn_single_higher_power() {
    // I = (x^3) in k[x] → N = 1 - t^3
    let hn = hilbert_numerator(&[x(1, 0, 3)]);
    assert_eq!(hn.coeffs(), &[1, 0, 0, -1]);
}

#[test]
fn hn_xx_xy_known_textbook_case() {
    // I = (x^2, x*y) in k[x, y].
    // Std monomials: {1, x, y, y^2, y^3, …}.
    // HS = 1 + 2t + t^2/(1-t) ⇒ HS*(1-t)^2 = 1 - 2t^2 + t^3.
    let hn = hilbert_numerator(&[from_exps(vec![2, 0]), from_exps(vec![1, 1])]);
    assert_eq!(hn.coeffs(), &[1, 0, -2, 1]);
}

#[test]
fn hn_square_of_max_ideal() {
    // I = m^2 = (x^2, x*y, y^2) in k[x, y].
    // S/I has basis {1, x, y} (HF = 1, 2). HN = 1 - 3t^2 + 2t^3.
    let hn = hilbert_numerator(&[
        from_exps(vec![2, 0]),
        from_exps(vec![1, 1]),
        from_exps(vec![0, 2]),
    ]);
    assert_eq!(hn.coeffs(), &[1, 0, -3, 2]);
}

#[test]
fn hn_addition_subtraction_round_trip() {
    let mut a = HilbertNum {
        coeffs: vec![1, -2, 3],
    };
    let b = HilbertNum {
        coeffs: vec![0, 1, 0, -4],
    };
    a.add_assign(&b);
    assert_eq!(a.coeffs(), &[1, -1, 3, -4]);
    a.sub_assign(&b);
    assert_eq!(a.coeffs(), &[1, -2, 3]);
}

#[test]
fn hn_mul_polynomials() {
    // (1 - t) * (1 - t) = 1 - 2t + t^2
    let a = HilbertNum::one_minus_t_pow(1);
    let b = HilbertNum::one_minus_t_pow(1);
    assert_eq!(a.mul(&b).coeffs(), &[1, -2, 1]);
}

#[test]
fn hn_degree_and_trim() {
    let a = HilbertNum {
        coeffs: vec![1, 0, 0, 0],
    };
    assert_eq!(a.degree(), Some(0));
    let z = HilbertNum::zero();
    assert_eq!(z.degree(), None);
}

#[test]
fn hn_saturating_arithmetic_does_not_panic_on_extreme_input() {
    // `i64::MAX`-valued coefficients exercise the saturating
    // arithmetic in `mul` and `add_assign`. Result coefficients
    // clamp to `i64::{MIN, MAX}` rather than wrapping.
    let huge = HilbertNum {
        coeffs: vec![i64::MAX, i64::MAX],
    };
    let other = HilbertNum { coeffs: vec![2, 2] };
    let prod = huge.mul(&other);
    // All coefficients are saturated; no panic.
    for &c in prod.coeffs() {
        assert!(
            c >= 0 || c == i64::MIN,
            "saturated coefficient must be in range"
        );
    }

    let mut acc = HilbertNum {
        coeffs: vec![i64::MAX],
    };
    let plus_one = HilbertNum { coeffs: vec![1] };
    acc.add_assign(&plus_one);
    assert_eq!(acc.coeff(0), i64::MAX, "add_assign saturates at i64::MAX");
}

#[test]
fn binom_basic_and_symmetry() {
    assert_eq!(binom_sat(0, 0), 1);
    assert_eq!(binom_sat(5, 0), 1);
    assert_eq!(binom_sat(5, 5), 1);
    assert_eq!(binom_sat(5, 2), 10);
    assert_eq!(binom_sat(5, 3), 10); // symmetry C(5,3)=C(5,2)
    assert_eq!(binom_sat(10, 4), 210);
    assert_eq!(binom_sat(3, 5), 0); // r > m
    // Large m, small r: choosing min(r, m-r) keeps it exact and cheap.
    assert_eq!(binom_sat(1000, 2), 1000 * 999 / 2);
}

#[test]
fn quotient_dim_positive_dimensional_is_none() {
    // (x) in k[x, y]: y is free ⇒ infinite-dimensional.
    assert_eq!(quotient_dimension(&[x(2, 0, 1)], 2), None);
    // (x*y) in k[x, y]: neither x nor y has a pure power.
    assert_eq!(quotient_dimension(&[from_exps(vec![1, 1])], 2), None);
    // Empty ideal in a non-trivial ring: the whole ring, infinite-dim.
    assert_eq!(quotient_dimension(&[], 2), None);
}

#[test]
fn quotient_dim_edge_unit_and_scalar_ring() {
    // Unit ideal (contains 1): S/I = 0.
    assert_eq!(quotient_dimension(&[Monomial::one(3)], 3), Some(0));
    // S = k (n_vars = 0), I = 0: dim 1.
    assert_eq!(quotient_dimension(&[], 0), Some(1));
}

#[test]
fn one_minus_t_pow_zero_collapses_to_zero() {
    // 1 - t^0 = 1 - 1 = 0.
    let hn = HilbertNum::one_minus_t_pow(0);
    assert!(hn.is_zero());
    assert_eq!(hn, HilbertNum::zero());
    assert_eq!(hn.degree(), None);
}

#[test]
fn sub_assign_resizes_when_other_longer() {
    // self is degree 1, other is degree 3: sub_assign must extend
    // self's coefficient vector before subtracting.
    let mut a = HilbertNum {
        coeffs: vec![5, 7],
    };
    let b = HilbertNum {
        coeffs: vec![1, 2, 3, 4],
    };
    a.sub_assign(&b);
    // [5-1, 7-2, 0-3, 0-4] = [4, 5, -3, -4]
    assert_eq!(a.coeffs(), &[4, 5, -3, -4]);
}

#[test]
fn mul_by_zero_is_zero() {
    let one = HilbertNum::one();
    let zero = HilbertNum::zero();
    assert!(one.mul(&zero).is_zero());
    assert!(zero.mul(&one).is_zero());
    // Non-trivial operand times zero is still zero.
    let p = HilbertNum {
        coeffs: vec![1, -2, 3],
    };
    assert!(p.mul(&HilbertNum::zero()).is_zero());
}

#[test]
fn hf_at_zero_vars_returns_coefficient() {
    // n_vars == 0 means S = k: HF(d) = N_d, the raw coefficient of t^d.
    let hn = HilbertNum {
        coeffs: vec![1, -3, 5],
    };
    assert_eq!(hn.hf_at(0, 0), 1);
    assert_eq!(hn.hf_at(1, 0), -3);
    assert_eq!(hn.hf_at(2, 0), 5);
    // Past the last term the coefficient is 0.
    assert_eq!(hn.hf_at(7, 0), 0);
}

#[test]
fn quotient_dim_declines_past_socle_degree_cap() {
    // Both variables carry pure powers (so the ideal is zero-dimensional
    // and we get past the positive-dimensional `None` check), but the
    // socle-degree bound `Σ(a_v - 1) = 65534 + 65534` exceeds
    // QUOT_DIM_DEGREE_CAP (2^16), so the function declines with `None`
    // rather than summing the Hilbert function.
    let gens = [x(2, 0, 65535), x(2, 1, 65535)];
    assert_eq!(quotient_dimension(&gens, 2), None);
}

#[test]
fn quotient_dim_takes_minimum_pure_power_per_variable() {
    // When two generators are pure powers of the SAME variable, `pure[v]`
    // is first set via `map_or(e, _)` (None → Some(e)) and on the second
    // occurrence the closure `|c| c.min(e)` fires — the smaller exponent
    // wins. Gens = [x0^3, x0^2, x1^2] minimises (as a monomial ideal) to
    // (x0^2, x1^2): standard monomials {1, x0, x1, x0·x1} ⇒ dim = 4.
    let gens = [from_exps(vec![3, 0]), from_exps(vec![2, 0]), from_exps(vec![0, 2])];
    assert_eq!(quotient_dimension(&gens, 2), Some(4));
    // Order-independence: the same closure fires when the smaller pure
    // power is seen first (`pure[0]` set to 2, then `c.min(3)` keeps 2).
    let gens_swapped = [from_exps(vec![2, 0]), from_exps(vec![3, 0]), from_exps(vec![0, 2])];
    assert_eq!(quotient_dimension(&gens_swapped, 2), Some(4));
}

// ─────────────── HARD-PROBE: cross-module bug hunt ───────────────
//
// Spec-driven invariants. Each test asserts something that follows
// directly from the mathematical definition of the Hilbert series or
// dimension, NOT from picus's source code.

/// Brute-force enumeration of standard monomials of the monomial ideal
/// `gens`: any exponent vector with total degree ≤ `max_deg` that is
/// NOT divisible by any generator. Returns the count. Independent
/// reference for `quotient_dimension` on small inputs.
fn enumerate_std_monomials_count(
    gens: &[Monomial],
    n_vars: usize,
    per_var_cap: u16,
) -> usize {
    let bounds: Vec<u16> = vec![per_var_cap; n_vars];
    let total: usize = bounds.iter().map(|&b| (b as usize) + 1).product();
    let mut count = 0usize;
    for i in 0..total {
        let mut idx = i;
        let mut exps: Vec<u16> = Vec::with_capacity(n_vars);
        for v in 0..n_vars {
            let span = (bounds[v] as usize) + 1;
            exps.push((idx % span) as u16);
            idx /= span;
        }
        let m = Monomial::from_exponents(exps);
        let in_ideal = gens.iter().any(|g| g.divides(&m));
        if !in_ideal {
            count += 1;
        }
    }
    count
}

#[test]
fn quotient_dim_matches_brute_force_enumeration_two_vars() {
    // SPEC: dim_k(S/I) = number of standard monomials. Enumerate
    // independently and compare to quotient_dimension on a grid of
    // small Artinian ideals.
    let cases: Vec<(Vec<Monomial>, usize)> = vec![
        // <x^2, y^2>: box {1, x, y, xy} ⇒ 4
        (vec![from_exps(vec![2, 0]), from_exps(vec![0, 2])], 4),
        // <x^3, y^2>: box 3*2 = 6
        (vec![from_exps(vec![3, 0]), from_exps(vec![0, 2])], 6),
        // <x^2, xy, y^2> = m^2: {1, x, y} ⇒ 3
        (vec![from_exps(vec![2, 0]), from_exps(vec![1, 1]), from_exps(vec![0, 2])], 3),
        // <x^4, x^2*y, y^3>: std monomials
        // y=0: x ∈ {0,1,2,3}; y=1: x ∈ {0,1}; y=2: x ∈ {0,1} ⇒ 4+2+2 = 8
        (vec![from_exps(vec![4, 0]), from_exps(vec![2, 1]), from_exps(vec![0, 3])], 8),
    ];
    for (gens, expected) in cases {
        let brute = enumerate_std_monomials_count(&gens, 2, 10);
        assert_eq!(brute, expected, "spec brute-force count mismatch");
        let q = quotient_dimension(&gens, 2);
        assert_eq!(q, Some(expected as u128),
            "quotient_dimension diverges from spec brute-force enumeration");
    }
}

#[test]
fn quotient_dim_matches_brute_force_enumeration_three_vars() {
    // SPEC: same as 2-var case but with 3 variables.
    let cases: Vec<(Vec<Monomial>, usize)> = vec![
        // <x, y, z>: dim 1 ({1})
        (
            vec![from_exps(vec![1, 0, 0]), from_exps(vec![0, 1, 0]), from_exps(vec![0, 0, 1])],
            1,
        ),
        // m^2 in 3 vars: {1, x, y, z} ⇒ 4
        (
            vec![
                from_exps(vec![2, 0, 0]),
                from_exps(vec![1, 1, 0]),
                from_exps(vec![1, 0, 1]),
                from_exps(vec![0, 2, 0]),
                from_exps(vec![0, 1, 1]),
                from_exps(vec![0, 0, 2]),
            ],
            4,
        ),
        // <x^2, y^2, z^2>: box 2*2*2 = 8
        (
            vec![from_exps(vec![2, 0, 0]), from_exps(vec![0, 2, 0]), from_exps(vec![0, 0, 2])],
            8,
        ),
    ];
    for (gens, expected) in cases {
        let brute = enumerate_std_monomials_count(&gens, 3, 8);
        assert_eq!(brute, expected, "spec brute-force count mismatch");
        assert_eq!(quotient_dimension(&gens, 3), Some(expected as u128),
            "quotient_dimension diverges from brute-force enumeration");
    }
}

#[test]
fn hf_sums_to_quotient_dim_across_diverse_shapes() {
    // SPEC: dim_k(S/I) = Σ_d HF(d). Confirm across diverse Artinian
    // shapes that the summed HF equals quotient_dimension's closed form.
    let cases: Vec<Vec<Monomial>> = vec![
        vec![x(2, 0, 1), x(2, 1, 1)],
        vec![x(2, 0, 2), x(2, 1, 2)],
        vec![x(2, 0, 4), x(2, 1, 5)],
        vec![x(3, 0, 2), x(3, 1, 2), x(3, 2, 2)],
        vec![from_exps(vec![3, 0]), from_exps(vec![1, 2]), from_exps(vec![0, 4])],
    ];
    for (i, gens) in cases.iter().enumerate() {
        let n_vars = gens[0].n_vars();
        let q = quotient_dimension(gens, n_vars);
        assert!(q.is_some(), "case {} should be Artinian", i);
        let q = q.unwrap();
        let hn = hilbert_numerator(gens);
        let mut summed: i128 = 0;
        for d in 0..256u32 {
            let hf = hn.hf_at(d, n_vars);
            if hf <= 0 { break; }
            summed += hf;
        }
        assert_eq!(summed as u128, q,
            "case {}: Σ HF(d) ({}) != quotient_dimension ({})", i, summed, q);
    }
}

#[test]
fn hf_at_is_nonnegative_for_artinian_until_socle() {
    // SPEC: for monomial ideals I with R/I Artinian, HF(d) ≥ 0 for all d,
    // and once HF(d) = 0 it stays 0 (HF is eventually-zero monotone for
    // Artinian).
    let gens = [x(2, 0, 3), x(2, 1, 4)];
    let hn = hilbert_numerator(&gens);
    let mut seen_zero = false;
    for d in 0..40u32 {
        let v = hn.hf_at(d, 2);
        assert!(v >= 0, "HF({}) = {} negative", d, v);
        if seen_zero {
            assert_eq!(v, 0, "HF dropped to 0 then came back at d={}: {}", d, v);
        }
        if v == 0 { seen_zero = true; }
    }
    assert!(seen_zero, "spec: Artinian HF must eventually be 0");
}

#[test]
fn hf_at_free_ring_grows_as_binomial() {
    // SPEC: I = 0 in k[x_1, ..., x_n]: HF(d) = C(d + n - 1, n - 1).
    // Independent computation of binomial via the integer recurrence.
    let hn = HilbertNum::one();
    for n_vars in 1usize..=4 {
        for d in 0u32..=6 {
            // Manually compute C(d + n - 1, n - 1).
            let m = (d as u64) + (n_vars as u64) - 1;
            let r = (n_vars as u64) - 1;
            let mut expected: i128 = 1;
            for i in 0..r.min(m - r) {
                expected = expected * ((m - i) as i128) / ((i + 1) as i128);
            }
            assert_eq!(hn.hf_at(d, n_vars), expected,
                "spec: HF(d) of free ring = C(d+n-1, n-1) failed at n_vars={}, d={}",
                n_vars, d);
        }
    }
}

#[test]
fn hilbert_numerator_minimal_gens_invariant() {
    // SPEC: adding generators that are MULTIPLES of existing minimal
    // gens does not change the ideal, so HN is unchanged.
    let minimal = [from_exps(vec![2, 0]), from_exps(vec![1, 1]), from_exps(vec![0, 2])];
    let with_extra = [
        from_exps(vec![2, 0]),
        from_exps(vec![3, 0]),  // multiple of x^2
        from_exps(vec![2, 2]),  // multiple of x^2
        from_exps(vec![1, 1]),
        from_exps(vec![1, 2]),  // multiple of x*y
        from_exps(vec![0, 2]),
        from_exps(vec![0, 4]),  // multiple of y^2
    ];
    let hn_a = hilbert_numerator(&minimal);
    let hn_b = hilbert_numerator(&with_extra);
    assert_eq!(hn_a, hn_b,
        "spec: HN invariant under inclusion of redundant (=multiple-of-minimal) gens");
}

#[test]
fn hilbert_numerator_is_order_independent() {
    // SPEC: HN depends on the IDEAL, not the order of generators.
    let perm_a = [from_exps(vec![2, 0]), from_exps(vec![1, 1]), from_exps(vec![0, 2])];
    let perm_b = [from_exps(vec![0, 2]), from_exps(vec![2, 0]), from_exps(vec![1, 1])];
    let perm_c = [from_exps(vec![1, 1]), from_exps(vec![0, 2]), from_exps(vec![2, 0])];
    let a = hilbert_numerator(&perm_a);
    let b = hilbert_numerator(&perm_b);
    let c = hilbert_numerator(&perm_c);
    assert_eq!(a, b, "spec: HN order-independent (perm a == perm b)");
    assert_eq!(b, c, "spec: HN order-independent (perm b == perm c)");
}

#[test]
fn one_minus_t_pow_basic_invariants() {
    // SPEC checks for the building block.
    let p1 = HilbertNum::one_minus_t_pow(1);
    assert_eq!(p1.coeffs(), &[1, -1], "spec: 1 - t");
    let p3 = HilbertNum::one_minus_t_pow(3);
    assert_eq!(p3.coeffs(), &[1, 0, 0, -1], "spec: 1 - t^3");
    // SPEC: (1 - t^d) at t=1 is 0 for d ≥ 1.
    for d in 1u32..=10 {
        let p = HilbertNum::one_minus_t_pow(d);
        let sum: i64 = p.coeffs().iter().sum();
        assert_eq!(sum, 0, "spec: (1 - t^{})(1) = 0", d);
    }
}

#[test]
fn mul_t_pow_preserves_degree_shift() {
    // SPEC: (t^k * p)(d) = p(d - k); the polynomial degrees shift by exactly k.
    let p = HilbertNum { coeffs: vec![1, -3, 5] }; // deg 2
    for k in 0u32..=5 {
        let mut q = p.clone();
        q.mul_t_pow_assign(k);
        assert_eq!(q.degree(), Some(2 + k),
            "spec: deg(t^{} * p) = deg(p) + {}", k, k);
        for d in 0..k {
            assert_eq!(q.coeff(d), 0, "spec: t^{}*p has 0 below degree {}", k, k);
        }
        for d in 0..=2u32 {
            assert_eq!(q.coeff(d + k), p.coeff(d),
                "spec: (t^{}*p).coeff({}) = p.coeff({})", k, d + k, d);
        }
    }
    // Zero-polynomial early-return: shifting 0 stays 0 at any k.
    let mut z = HilbertNum::zero();
    z.mul_t_pow_assign(5);
    assert_eq!(z, HilbertNum::zero());
}

#[test]
fn quotient_dim_one_var_pure_power_matches_degree() {
    // SPEC: <x^n> in k[x] has dim n. Probe across primes/exponents.
    for n in 1u16..=20 {
        let gens = [x(1, 0, n)];
        assert_eq!(quotient_dimension(&gens, 1), Some(n as u128),
            "spec: dim k[x]/<x^{}> = {}", n, n);
    }
}

#[test]
fn quotient_dim_box_pure_powers_three_vars() {
    // SPEC: <x^a, y^b, z^c> has dim a*b*c.
    for a in 1u16..=3 {
        for b in 1u16..=3 {
            for c in 1u16..=3 {
                let gens = [x(3, 0, a), x(3, 1, b), x(3, 2, c)];
                let expected = (a as u128) * (b as u128) * (c as u128);
                assert_eq!(quotient_dimension(&gens, 3), Some(expected),
                    "spec: dim <x^{}, y^{}, z^{}> = {}", a, b, c, expected);
            }
        }
    }
}

#[test]
fn hilbert_numerator_unit_ideal_is_zero_regardless_of_n_vars() {
    // SPEC: HN(<1>) = 0 (S/<1> = 0).
    for n_vars in 0usize..=4 {
        let unit = Monomial::one(n_vars);
        let hn = hilbert_numerator(&[unit]);
        assert!(hn.is_zero(), "spec: HN(<1>) = 0 for n_vars={}", n_vars);
    }
}

#[test]
fn binom_recurrence_consistency() {
    // SPEC: C(m, r) = C(m-1, r-1) + C(m-1, r) (Pascal's rule).
    for m in 1u64..=20 {
        for r in 1u64..=m {
            let lhs = binom_sat(m, r);
            let rhs = binom_sat(m - 1, r - 1).saturating_add(binom_sat(m - 1, r));
            assert_eq!(lhs, rhs,
                "spec: Pascal's rule C({},{}) = C({},{}) + C({},{})",
                m, r, m - 1, r - 1, m - 1, r);
        }
    }
}

#[test]
fn hf_at_consistency_for_pure_power_single_var() {
    // SPEC: HF(d) of k[x]/<x^n> is 1 for d < n, 0 for d ≥ n.
    for n in 1u16..=8 {
        let hn = hilbert_numerator(&[x(1, 0, n)]);
        for d in 0u32..=(n as u32 + 5) {
            let expected: i128 = if (d as u16) < n { 1 } else { 0 };
            assert_eq!(hn.hf_at(d, 1), expected,
                "spec: HF({}) of k[x]/<x^{}> = {}", d, n, expected);
        }
    }
}

#[test]
fn audit_p3_add_generators_incremental_matches_from_scratch_on_coprime_box() {
    // <x^5, y^5> in 2 vars. Add x*y as a third generator.
    // Incremental: N(<x^5, y^5>) + x*y vs from-scratch N(<x^5, y^5, x*y>).
    let existing = vec![x(2, 0, 5), x(2, 1, 5)];
    let extra = vec![from_exps(vec![1, 1])];
    let hn_existing = hilbert_numerator(&existing);
    let hn_incremental = hn_existing.add_generators_incremental(&existing, &extra);

    let mut full = existing.clone();
    full.extend(extra.iter().cloned());
    let hn_full = hilbert_numerator(&full);

    assert_eq!(hn_incremental, hn_full,
        "incremental BCR update must equal from-scratch hilbert_numerator");
}

#[test]
fn audit_p3_add_generators_incremental_skips_redundant_generator() {
    // <x^2, y^2>; add (x^3, y^3) — both divisible by existing generators.
    // The incremental update must short-circuit (no recursive BCR call)
    // and leave the numerator unchanged.
    let existing = vec![x(2, 0, 2), x(2, 1, 2)];
    let extra = vec![x(2, 0, 3), x(2, 1, 3)];
    let hn_existing = hilbert_numerator(&existing);
    let hn_incremental = hn_existing.add_generators_incremental(&existing, &extra);
    assert_eq!(hn_incremental, hn_existing,
        "adding generators already in I must not change the numerator");
}

#[test]
fn audit_p3_add_generators_incremental_handles_empty_new_gens() {
    let existing = vec![x(2, 0, 2)];
    let hn_existing = hilbert_numerator(&existing);
    let hn_incremental = hn_existing.add_generators_incremental(&existing, &[]);
    assert_eq!(hn_incremental, hn_existing, "empty new_gens is identity");
}

#[test]
fn audit_p3_add_generators_incremental_matches_on_three_vars_mixed() {
    // 3-var diverse case: <x^3, y^3, z^3> + xyz + x^2yz.
    let existing = vec![x(3, 0, 3), x(3, 1, 3), x(3, 2, 3)];
    let extra = vec![
        from_exps(vec![1, 1, 1]),
        from_exps(vec![2, 1, 1]),
    ];
    let hn_existing = hilbert_numerator(&existing);
    let hn_incremental = hn_existing.add_generators_incremental(&existing, &extra);

    let mut full = existing.clone();
    full.extend(extra.iter().cloned());
    let hn_full = hilbert_numerator(&full);
    assert_eq!(hn_incremental, hn_full);
}

#[test]
fn quotient_dim_positive_dim_in_three_vars_diverse() {
    // SPEC: an ideal where any one variable lacks a pure power is
    // positive-dimensional ⇒ dim is None.
    // <x^2, y^2>: z is free.
    assert_eq!(quotient_dimension(&[x(3, 0, 2), x(3, 1, 2)], 3), None);
    // <x*y, x*z, y*z>: no var has a pure power (every gen is bivariate).
    let gens = [
        from_exps(vec![1, 1, 0]),
        from_exps(vec![1, 0, 1]),
        from_exps(vec![0, 1, 1]),
    ];
    assert_eq!(quotient_dimension(&gens, 3), None,
        "spec: pairwise-product gens lack any pure power ⇒ positive-dim");
}
