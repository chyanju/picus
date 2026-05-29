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
fn evaluate_horner() {
    let f = small_field();
    // p(x) = 2x^2 + 3x + 1
    let p = poly_from_ints(&[1, 3, 2], &f);
    // p(5) = 50 + 15 + 1 = 66
    let v = p.evaluate(&f.from_u64(5), &f);
    assert_eq!(v.as_biguint(), BigUint::from(66u32));
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
fn find_roots_quadratic_small() {
    let f = small_field();
    // (x - 3)(x - 7) = x^2 - 10x + 21
    let p = poly_from_ints(&[21, -10, 1], &f);
    let mut roots: Vec<u64> = find_roots(&p, &f)
        .iter()
        .map(|r| r.as_biguint().iter_u64_digits().next().unwrap_or(0))
        .collect();
    roots.sort();
    assert_eq!(roots, vec![3u64, 7u64]);
}

#[test]
fn find_roots_no_roots() {
    let f = small_field();
    // x^2 + 1 over GF(101): -1 is a QR iff 101 ≡ 1 mod 4. 101 mod 4 = 1, so it has roots.
    // Use x^2 + 2 instead. Check: -2 is QR iff (-2 | 101) = (-1|101)*(2|101) = 1 * 1 = 1. Has roots.
    // Use a polynomial with no roots: pick (x^2 + a) where a is a non-QR.
    // Compute a non-QR by finding b with b^((p-1)/2) = -1.
    let mut nonqr = None;
    for cand in 2u64..50 {
        let v = f.from_u64(cand);
        let exp = (BigUint::from(101u32) - BigUint::one()) / BigUint::from(2u32);
        let pw = f.pow(&v, &exp);
        if pw.as_biguint() == (BigUint::from(101u32) - BigUint::one()) {
            nonqr = Some(cand);
            break;
        }
    }
    let nq = nonqr.expect("non-QR exists in GF(101)");
    // p(x) = x^2 + nq has no roots (since -nq is also a non-QR? actually we need -nq to be a non-QR;
    // sufficient: choose nq so that -nq is a non-QR. With p % 4 == 1, -1 is a QR, so -nq is QR iff
    // nq is QR — so -nq is non-QR. Good.).
    let p = poly_from_ints(&[nq as i64, 0, 1], &f);
    let roots = find_roots(&p, &f);
    assert!(
        roots.is_empty(),
        "expected no roots, got {:?}",
        roots
            .iter()
            .map(|r| r.as_biguint().clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn find_roots_cubic_small() {
    let f = small_field();
    // (x - 1)(x - 2)(x - 3) = x^3 - 6x^2 + 11x - 6
    let p = poly_from_ints(&[-6, 11, -6, 1], &f);
    let mut roots: Vec<u64> = find_roots(&p, &f)
        .iter()
        .map(|r| r.as_biguint().iter_u64_digits().next().unwrap_or(0))
        .collect();
    roots.sort();
    assert_eq!(roots, vec![1, 2, 3]);
}

#[test]
fn find_roots_with_multiplicity() {
    let f = small_field();
    // (x - 5)^2 = x^2 - 10x + 25
    let p = poly_from_ints(&[25, -10, 1], &f);
    let roots: Vec<u64> = find_roots(&p, &f)
        .iter()
        .map(|r| r.as_biguint().iter_u64_digits().next().unwrap_or(0))
        .collect();
    assert_eq!(roots, vec![5]); // dedup'd
}

#[test]
fn find_roots_linear() {
    let f = small_field();
    // 3x - 6 -> x = 2.
    let p = poly_from_ints(&[-6, 3], &f);
    let roots = find_roots(&p, &f);
    assert_eq!(roots.len(), 1);
    assert_eq!(roots[0].as_biguint(), BigUint::from(2u32));
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

#[test]
fn find_roots_zero_poly() {
    let f = small_field();
    let p = UnivariatePoly::zero();
    assert!(find_roots(&p, &f).is_empty());
}

#[test]
fn find_roots_constant_poly() {
    let f = small_field();
    let p = poly_from_ints(&[7], &f);
    assert!(find_roots(&p, &f).is_empty());
}
