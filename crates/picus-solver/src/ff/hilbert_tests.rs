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
fn hn_unit_ideal_is_zero() {
    let unit = Monomial::one(3);
    let hn = hilbert_numerator(&[unit]);
    assert_eq!(hn, HilbertNum::zero());
}

#[test]
fn hn_single_variable() {
    // I = (x) in k[x, y] → N = 1 - t
    let hn = hilbert_numerator(&[x(2, 0, 1)]);
    assert_eq!(hn.coeffs(), &[1, -1]);
}

#[test]
fn hn_single_higher_power() {
    // I = (x^3) in k[x] → N = 1 - t^3
    let hn = hilbert_numerator(&[x(1, 0, 3)]);
    assert_eq!(hn.coeffs(), &[1, 0, 0, -1]);
}

#[test]
fn hn_two_coprime_vars() {
    // I = (x, y) coprime → N = (1-t)^2 = 1 - 2t + t^2
    let hn = hilbert_numerator(&[x(2, 0, 1), x(2, 1, 1)]);
    assert_eq!(hn.coeffs(), &[1, -2, 1]);
}

#[test]
fn hn_three_coprime_vars() {
    // I = (x, y, z) → N = (1-t)^3 = 1 - 3t + 3t^2 - t^3
    let hn = hilbert_numerator(&[x(3, 0, 1), x(3, 1, 1), x(3, 2, 1)]);
    assert_eq!(hn.coeffs(), &[1, -3, 3, -1]);
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
fn hn_chain_overlap_xy_yz() {
    // I = (x*y, y*z) in k[x, y, z]. Standard monomials are
    // monomials with `b = 0` (no `y`) plus pure powers `y^k`.
    // HF(0) = 1, HF(d) = d+2 for d ≥ 1; HN = 1 - 2t^2 + t^3.
    let hn = hilbert_numerator(&[from_exps(vec![1, 1, 0]), from_exps(vec![0, 1, 1])]);
    assert_eq!(hn.coeffs(), &[1, 0, -2, 1]);
}

#[test]
fn hn_redundant_generators_are_minimised() {
    // (x, x*y) ⇒ x*y is redundant, so HN = 1 - t (same as `(x)`).
    let hn = hilbert_numerator(&[x(2, 0, 1), from_exps(vec![1, 1])]);
    assert_eq!(hn.coeffs(), &[1, -1]);
}

#[test]
fn hn_artinian_ideal_coeffs_sum_to_zero() {
    // For an artinian ideal I (i.e. `S/I` finite-dimensional),
    // `HN(1) = 0`: `HS(t) = HN(t) / (1-t)^n` is defined at `t=1`
    // only when `(1-t)^n | HN(t)`, which forces `HN(1) = 0`.
    // I = (x^2, x*y, y^2) ⇒ HN = 1 - 3t^2 + 2t^3, sum = 0.
    let hn = hilbert_numerator(&[
        from_exps(vec![2, 0]),
        from_exps(vec![1, 1]),
        from_exps(vec![0, 2]),
    ]);
    let sum: i64 = hn.coeffs().iter().sum();
    assert_eq!(sum, 0);
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
fn hn_mul_t_pow_shifts() {
    let mut a = HilbertNum {
        coeffs: vec![1, -2, 3],
    };
    a.mul_t_pow_assign(2);
    assert_eq!(a.coeffs(), &[0, 0, 1, -2, 3]);
    let mut z = HilbertNum::zero();
    z.mul_t_pow_assign(5);
    assert_eq!(z, HilbertNum::zero());
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
fn hf_at_counts_degree_d_part() {
    // I = (x^2, x*y, y^2) = m^2 in k[x,y]; HF = 1, 2, 0, 0, ...
    let hn = hilbert_numerator(&[
        from_exps(vec![2, 0]),
        from_exps(vec![1, 1]),
        from_exps(vec![0, 2]),
    ]);
    assert_eq!(hn.hf_at(0, 2), 1);
    assert_eq!(hn.hf_at(1, 2), 2);
    assert_eq!(hn.hf_at(2, 2), 0);
    assert_eq!(hn.hf_at(3, 2), 0);
}

#[test]
fn hf_at_single_var_power() {
    // I = (x^3) in k[x]: standard {1, x, x^2}; HF(d) = 1 for d < 3, else 0.
    let hn = hilbert_numerator(&[x(1, 0, 3)]);
    assert_eq!(hn.hf_at(0, 1), 1);
    assert_eq!(hn.hf_at(1, 1), 1);
    assert_eq!(hn.hf_at(2, 1), 1);
    assert_eq!(hn.hf_at(3, 1), 0);
}

#[test]
fn hf_at_free_polynomial_ring() {
    // I = 0 in k[x, y]: HF(d) = C(d+1, 1) = d + 1 (monomials of degree d).
    let hn = HilbertNum::one();
    assert_eq!(hn.hf_at(0, 2), 1);
    assert_eq!(hn.hf_at(1, 2), 2);
    assert_eq!(hn.hf_at(4, 2), 5);
    // k[x,y,z]: HF(d) = C(d+2, 2).
    assert_eq!(hn.hf_at(3, 3), 10);
}

#[test]
fn quotient_dim_zero_dimensional_cases() {
    // (x, y): standard {1} ⇒ dim 1.
    assert_eq!(quotient_dimension(&[x(2, 0, 1), x(2, 1, 1)], 2), Some(1));
    // m^2 = (x^2, x*y, y^2): standard {1, x, y} ⇒ dim 3.
    assert_eq!(
        quotient_dimension(
            &[
                from_exps(vec![2, 0]),
                from_exps(vec![1, 1]),
                from_exps(vec![0, 2])
            ],
            2
        ),
        Some(3)
    );
    // (x^2, y^2): standard {1, x, y, x*y} ⇒ dim 4.
    assert_eq!(
        quotient_dimension(&[from_exps(vec![2, 0]), from_exps(vec![0, 2])], 2),
        Some(4)
    );
    // (x^3) in k[x]: standard {1, x, x^2} ⇒ dim 3.
    assert_eq!(quotient_dimension(&[x(1, 0, 3)], 1), Some(3));
    // (x^a, y^b): box of standard monomials ⇒ a*b.
    assert_eq!(quotient_dimension(&[x(2, 0, 4), x(2, 1, 5)], 2), Some(20));
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
fn quotient_dim_equals_summed_hilbert_function() {
    // Cross-check the closed-form sum against term-by-term HF for an
    // Artinian ideal: I = (x^2, y^3) in k[x, y], dim = 2*3 = 6.
    let gens = [x(2, 0, 2), x(2, 1, 3)];
    let hn = hilbert_numerator(&gens);
    let mut summed: i128 = 0;
    for d in 0..16 {
        summed += hn.hf_at(d, 2);
    }
    assert_eq!(summed, 6);
    assert_eq!(quotient_dimension(&gens, 2), Some(6));
}
