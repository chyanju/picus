use super::*;
use num_bigint::BigUint;

fn small_field() -> PrimeField {
    PrimeField::new(BigUint::from(101u32))
}

fn bn128_field() -> PrimeField {
    let p_str = "21888242871839275222246405745257275088548364400416034343698204186575808495617";
    PrimeField::new(p_str.parse::<BigUint>().unwrap())
}

fn poly_from_ints(coeffs: &[i64], f: &PrimeField) -> UnivariatePoly {
    let cs = coeffs.iter().map(|&c| f.from_i64(c)).collect();
    UnivariatePoly::from_coeffs(cs, f)
}

/// Ground-truth roots: evaluate at every element of GF(p) (small p only).
fn brute_roots(p: &UnivariatePoly, f: &PrimeField) -> Vec<BigUint> {
    let prime = f.prime().clone();
    let mut out = Vec::new();
    let mut c = BigUint::from(0u32);
    while c < prime {
        if f.is_zero(&p.evaluate(&f.from_biguint(&c), f)) {
            out.push(c.clone());
        }
        c += 1u32;
    }
    out
}

#[test]
fn find_roots_checked_matches_brute_force_and_is_complete() {
    let f = small_field();
    let lin = |r: i64| poly_from_ints(&[-r, 1], &f); // x - r

    // (x-3)(x-7)(x-50) — distinct roots.
    let p1 = lin(3).mul(&lin(7), &f).mul(&lin(50), &f);
    // (x-4)^2 (x-9) — repeated root 4 (deduped) plus 9.
    let p2 = lin(4).mul(&lin(4), &f).mul(&lin(9), &f);
    // x^2 - 2 — no root in GF(101) (2 is a non-residue).
    let p3 = poly_from_ints(&[-2, 0, 1], &f);
    // Nonzero constant — no roots.
    let p4 = poly_from_ints(&[5], &f);

    for p in [&p1, &p2, &p3, &p4] {
        let (roots, complete) = find_roots_checked(p, &f);
        assert!(complete, "small-prime root finding must report complete");
        let mut got: Vec<BigUint> = roots.iter().map(|r| r.as_biguint().clone()).collect();
        got.sort();
        let mut want = brute_roots(p, &f);
        want.sort();
        assert_eq!(got, want, "checked roots must match brute force");
        // `find_roots` is exactly the `.0` projection.
        let mut plain: Vec<BigUint> = find_roots(p, &f)
            .iter()
            .map(|r| r.as_biguint().clone())
            .collect();
        plain.sort();
        assert_eq!(plain, got, "find_roots must equal find_roots_checked.0");
    }
}

#[test]
fn add_sub_mul() {
    let f = small_field();
    let a = poly_from_ints(&[1, 2, 3], &f); // 3x^2 + 2x + 1
    let b = poly_from_ints(&[4, 5], &f); // 5x + 4
    let s = a.add(&b, &f);
    // (3x^2 + 2x + 1) + (5x + 4) = 3x^2 + 7x + 5
    assert_eq!(s.coeffs[0].as_biguint(), BigUint::from(5u32));
    assert_eq!(s.coeffs[1].as_biguint(), BigUint::from(7u32));
    assert_eq!(s.coeffs[2].as_biguint(), BigUint::from(3u32));
    let d = a.sub(&b, &f);
    // (3x^2 + 2x + 1) - (5x + 4) = 3x^2 - 3x - 3 = 3x^2 + 98x + 98 mod 101
    assert_eq!(d.coeffs[0].as_biguint(), BigUint::from(98u32));
    assert_eq!(d.coeffs[1].as_biguint(), BigUint::from(98u32));
    assert_eq!(d.coeffs[2].as_biguint(), BigUint::from(3u32));
    let m = a.mul(&b, &f);
    // (3x^2 + 2x + 1) * (5x + 4) = 15x^3 + 12x^2 + 10x^2 + 8x + 5x + 4
    //                           = 15x^3 + 22x^2 + 13x + 4
    assert_eq!(m.coeffs[0].as_biguint(), BigUint::from(4u32));
    assert_eq!(m.coeffs[1].as_biguint(), BigUint::from(13u32));
    assert_eq!(m.coeffs[2].as_biguint(), BigUint::from(22u32));
    assert_eq!(m.coeffs[3].as_biguint(), BigUint::from(15u32));
}

#[test]
fn div_rem_basic() {
    let f = small_field();
    // (x^3 - 1) / (x - 1) = x^2 + x + 1
    let num = poly_from_ints(&[-1, 0, 0, 1], &f);
    let den = poly_from_ints(&[-1, 1], &f);
    let (q, r) = num.div_rem(&den, &f);
    assert!(r.is_zero());
    assert_eq!(q.coeffs.len(), 3);
    assert_eq!(q.coeffs[0].as_biguint(), BigUint::from(1u32));
    assert_eq!(q.coeffs[1].as_biguint(), BigUint::from(1u32));
    assert_eq!(q.coeffs[2].as_biguint(), BigUint::from(1u32));
}

#[test]
fn gcd_works() {
    let f = small_field();
    // gcd(x^2 - 1, x - 1) = x - 1 (monic)
    let a = poly_from_ints(&[-1, 0, 1], &f);
    let b = poly_from_ints(&[-1, 1], &f);
    let g = a.gcd(&b, &f);
    assert_eq!(g.degree(), Some(1));
    assert_eq!(
        g.leading_coefficient().unwrap().as_biguint(),
        BigUint::from(1u32)
    );
    // Should be (x - 1).
    assert_eq!(g.coeffs[0].as_biguint(), BigUint::from(100u32)); // -1 mod 101
}

#[test]
fn pow_mod_works() {
    let f = small_field();
    // x^5 mod (x^2 - 1) over GF(101).
    // x^2 = 1, so x^5 = x.
    let x = UnivariatePoly::x(&f);
    let modulus = poly_from_ints(&[-1, 0, 1], &f);
    let r = x.pow_mod(&BigUint::from(5u32), &modulus, &f);
    assert_eq!(r.degree(), Some(1));
    assert_eq!(r.coeffs[0].as_biguint(), BigUint::from(0u32));
    assert_eq!(r.coeffs[1].as_biguint(), BigUint::from(1u32));
}

#[test]
fn find_roots_linear_and_zero_edges() {
    let f = small_field();
    // Linear poly 3x - 6 → x = 2; exercises the deg==1 fast path.
    let lin = poly_from_ints(&[-6, 3], &f);
    let roots = find_roots(&lin, &f);
    assert_eq!(roots.len(), 1);
    assert_eq!(roots[0].as_biguint(), BigUint::from(2u32));
    // Zero-polynomial early return.
    assert!(find_roots(&UnivariatePoly::zero(), &f).is_empty());
}

#[test]
fn find_roots_bn128() {
    let f = bn128_field();
    // (x - 5)(x - 7) = x^2 - 12x + 35
    let p = poly_from_ints(&[35, -12, 1], &f);
    let mut roots: Vec<BigUint> = find_roots(&p, &f)
        .iter()
        .map(|r| r.as_biguint().clone())
        .collect();
    roots.sort();
    assert_eq!(roots, vec![BigUint::from(5u32), BigUint::from(7u32)]);
}

fn gf2() -> PrimeField {
    PrimeField::new(BigUint::from(2u32))
}

#[test]
fn add_sub_with_shorter_operand_hits_both_arms() {
    let f = small_field();
    let a = poly_from_ints(&[1, 2, 3], &f);
    // add: longer + shorter. (3x^2 + 2x + 1) + 5 = 3x^2 + 2x + 6
    let b5 = poly_from_ints(&[5], &f);
    let s = a.add(&b5, &f);
    assert_eq!(s.degree(), Some(2));
    assert_eq!(s.coeffs()[0].as_biguint(), BigUint::from(6u32));
    assert_eq!(s.coeffs()[1].as_biguint(), BigUint::from(2u32));
    assert_eq!(s.coeffs()[2].as_biguint(), BigUint::from(3u32));
    // add commutes: shorter + longer also hits the (None, Some) arm.
    let s2 = b5.add(&a, &f);
    assert_eq!(s2.coeffs()[0].as_biguint(), BigUint::from(6u32));
    assert_eq!(s2.coeffs()[2].as_biguint(), BigUint::from(3u32));
    // sub: longer - shorter. (3x^2 + 2x + 1) - 1 = 3x^2 + 2x
    let b1 = poly_from_ints(&[1], &f);
    let d = a.sub(&b1, &f);
    assert_eq!(d.degree(), Some(2));
    assert_eq!(d.coeffs()[0].as_biguint(), BigUint::from(0u32));
    assert_eq!(d.coeffs()[1].as_biguint(), BigUint::from(2u32));
    assert_eq!(d.coeffs()[2].as_biguint(), BigUint::from(3u32));
    // sub: shorter - longer hits the (None, Some) negation arm.
    // 1 - (3x^2 + 2x + 1) = -3x^2 - 2x = 98x^2 + 99x mod 101
    let d2 = b1.sub(&a, &f);
    assert_eq!(d2.coeffs()[0].as_biguint(), BigUint::from(0u32));
    assert_eq!(d2.coeffs()[1].as_biguint(), BigUint::from(99u32));
    assert_eq!(d2.coeffs()[2].as_biguint(), BigUint::from(98u32));
}

#[test]
fn neg_negates_each_coefficient() {
    let f = small_field();
    let p = poly_from_ints(&[1, 2, 3], &f);
    let n = p.neg(&f);
    // -1, -2, -3 mod 101 = 100, 99, 98
    assert_eq!(n.coeffs()[0].as_biguint(), BigUint::from(100u32));
    assert_eq!(n.coeffs()[1].as_biguint(), BigUint::from(99u32));
    assert_eq!(n.coeffs()[2].as_biguint(), BigUint::from(98u32));
    // neg of zero poly is zero poly (empty coeffs).
    assert!(UnivariatePoly::zero().neg(&f).is_zero());
}

#[test]
fn scale_by_zero_yields_zero_poly() {
    let f = small_field();
    let p = poly_from_ints(&[1, 2, 3], &f);
    let z = p.scale(&f.zero(), &f);
    assert!(z.is_zero());
    assert!(z.coeffs().is_empty());
    // scaling the zero poly by a nonzero scalar is also zero.
    let z2 = UnivariatePoly::zero().scale(&f.from_u64(7), &f);
    assert!(z2.is_zero());
}

#[test]
fn make_monic_of_zero_is_zero() {
    let f = small_field();
    let m = UnivariatePoly::zero().make_monic(&f);
    assert!(m.is_zero());
    assert!(m.coeffs().is_empty());
}

#[test]
fn derivative_of_constant_and_zero_is_zero() {
    let f = small_field();
    // d/dx (5) = 0
    assert!(poly_from_ints(&[5], &f).derivative(&f).is_zero());
    // d/dx (0) = 0
    assert!(UnivariatePoly::zero().derivative(&f).is_zero());
}

#[test]
fn pow_mod_zero_exponent_is_one_mod_modulus() {
    let f = small_field();
    // base^0 mod (x^2 - 1) = 1 (degree-0 poly with coeff 1).
    let base = poly_from_ints(&[3, 1], &f); // x + 3
    let modulus = poly_from_ints(&[-1, 0, 1], &f); // x^2 - 1
    let r = base.pow_mod(&BigUint::from(0u32), &modulus, &f);
    assert_eq!(r.degree(), Some(0));
    assert_eq!(r.coeffs()[0].as_biguint(), BigUint::from(1u32));
}

#[test]
fn squarefree_derivative_zero_gf2() {
    // Over GF(2), d/dx(x^2) = 2x = 0, so `squarefree` takes the
    // derivative-is-zero branch and returns make_monic(x^2).
    let f = gf2();
    let x2 = poly_from_ints(&[0, 0, 1], &f); // x^2
    let sf = squarefree(&x2, &f);
    // make_monic(x^2) over GF(2) is x^2 itself (leading coeff already 1).
    assert_eq!(sf.degree(), Some(2));
    assert_eq!(sf.coeffs()[0].as_biguint(), BigUint::from(0u32));
    assert_eq!(sf.coeffs()[1].as_biguint(), BigUint::from(0u32));
    assert_eq!(sf.coeffs()[2].as_biguint(), BigUint::from(1u32));
}

#[test]
fn find_roots_gf2_brute_force_split() {
    // x^2 + x = x(x+1) over GF(2): roots {0, 1}. Exercises the GF(2)
    // brute-force root enumeration branch in split_linear_factors.
    let f = gf2();
    let p = poly_from_ints(&[0, 1, 1], &f); // x^2 + x
    let mut roots: Vec<BigUint> = find_roots(&p, &f)
        .iter()
        .map(|r| r.as_biguint())
        .collect();
    roots.sort();
    assert_eq!(roots, vec![BigUint::from(0u32), BigUint::from(1u32)]);
}

#[test]
fn squarefree_of_zero_poly_is_zero() {
    // The `poly.is_zero()` early-return arm of `squarefree`: the zero
    // polynomial has no squarefree part, so the result is zero.
    let f = small_field();
    let sf = squarefree(&UnivariatePoly::zero(), &f);
    assert!(sf.is_zero());
}

#[test]
fn rand_below_zero_bound_returns_zero() {
    // `rand_below` with bound 0 has `bits == 0` and returns 0 without
    // sampling (the degenerate-bound guard). Deterministic regardless of
    // the RNG seed.
    let mut rng = oorandom::Rand64::new(0xDEADBEEF);
    let v = rand_below(&mut rng, &BigUint::from(0u32));
    assert_eq!(v, BigUint::from(0u32));
}

#[test]
fn cantor_zassenhaus_no_linear_part_returns_empty() {
    // x^2 + 2 has no roots in GF(101) (chosen non-residue setup), so its
    // distinct-linear part is degree 0 and cantor_zassenhaus returns [].
    let f = small_field();
    // Find a poly with no GF(101) roots: x^2 - nq for a non-QR nq.
    let mut nonqr = None;
    for cand in 2u64..50 {
        let v = f.from_u64(cand);
        let exp = (BigUint::from(101u32) - BigUint::one()) / BigUint::from(2u32);
        if f.pow(&v, &exp).as_biguint() == BigUint::from(100u32) {
            nonqr = Some(cand);
            break;
        }
    }
    let nq = nonqr.unwrap();
    let p = poly_from_ints(&[nq as i64, 0, 1], &f); // x^2 + nq, no roots
    let factors = cantor_zassenhaus(&p, &f);
    assert!(factors.is_empty());
}

#[test]
fn split_linear_factors_degree_zero_input_yields_no_factors() {
    // `split_linear_factors`' top-of-loop `deg == 0` arm: pop a constant
    // off the stack, `continue` without contributing a linear factor.
    // Calling it on `UnivariatePoly::one(...)` seeds the stack with a
    // single degree-0 element; the loop pops it, hits the deg==0 guard,
    // and the stack drains empty without ever pushing into `out`.
    //
    // `cantor_zassenhaus` itself guards against degree-0 input at its
    // entry (line 384 of univariate.rs), so this branch is exercised by
    // a direct call into the private helper from the sibling test mod.
    let f = small_field();
    let mut rng = oorandom::Rand64::new(0xDEADBEEF);
    let factors = split_linear_factors(&UnivariatePoly::one(&f), &f, &mut rng);
    assert!(factors.is_empty(), "constant seed must produce no linear factors");
}
