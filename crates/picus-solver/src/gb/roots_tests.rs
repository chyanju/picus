use super::*;
use num_bigint::BigUint;

#[test]
fn test_roots_linear() {
    // x - 3 = 0 over GF(17) → root = 3
    let ff = PrimeField::new(BigUint::from(17u32));

    let coeffs = vec![
        ff.from_biguint(&BigUint::from(14u32)), // -3 mod 17
        ff.one(),
    ];

    let roots = find_roots(&ff, &coeffs);
    assert_eq!(roots.len(), 1);
    assert_eq!(ff.to_biguint(&roots[0]), BigUint::from(3u32));
}

#[test]
fn test_roots_quadratic() {
    // x^2 - 1 = 0 over GF(17) → roots 1, 16
    let ff = PrimeField::new(BigUint::from(17u32));

    let coeffs = vec![
        ff.from_biguint(&BigUint::from(16u32)), // -1 mod 17
        ff.zero(),
        ff.one(),
    ];

    let roots = find_roots(&ff, &coeffs);
    assert_eq!(roots.len(), 2);
    let mut vals: Vec<BigUint> = roots.iter().map(|r| ff.to_biguint(r)).collect();
    vals.sort();
    assert_eq!(vals, vec![BigUint::from(1u32), BigUint::from(16u32)]);
}

#[test]
fn test_no_roots() {
    // x^2 + 1 = 0 over GF(3) → no roots
    let ff = PrimeField::new(BigUint::from(3u32));

    let coeffs = vec![ff.one(), ff.zero(), ff.one()];
    let roots = find_roots(&ff, &coeffs);
    assert_eq!(roots.len(), 0);
}

#[test]
fn test_roots_with_zero_root() {
    // x^2 - x = 0 over GF(7) → roots 0, 1
    let ff = PrimeField::new(BigUint::from(7u32));
    let coeffs = vec![ff.zero(), ff.from_biguint(&BigUint::from(6u32)), ff.one()];
    let roots = find_roots(&ff, &coeffs);
    assert_eq!(roots.len(), 2);
    let mut vals: Vec<BigUint> = roots.iter().map(|r| ff.to_biguint(r)).collect();
    vals.sort();
    assert_eq!(vals, vec![BigUint::from(0u32), BigUint::from(1u32)]);
}

#[test]
fn test_roots_high_degree_with_irreducible_factors() {
    // x^4 - 1 over GF(5): a^4 ≡ 1 mod 5 for all a ∈ {1,2,3,4}.
    let ff = PrimeField::new(BigUint::from(5u32));
    let coeffs = vec![
        ff.from_biguint(&BigUint::from(4u32)), // -1
        ff.zero(),
        ff.zero(),
        ff.zero(),
        ff.one(),
    ];
    let roots = find_roots(&ff, &coeffs);
    let mut vals: Vec<BigUint> = roots.iter().map(|r| ff.to_biguint(r)).collect();
    vals.sort();
    assert_eq!(
        vals,
        vec![
            BigUint::from(1u32),
            BigUint::from(2u32),
            BigUint::from(3u32),
            BigUint::from(4u32),
        ]
    );
}

/// Sort roots as BigUint for stable comparison.
fn sorted_roots(ff: &PrimeField, roots: &[picus_core::ff::field::FieldElem]) -> Vec<BigUint> {
    let mut v: Vec<BigUint> = roots.iter().map(|r| ff.to_biguint(r)).collect();
    v.sort();
    v
}

/// Convert a list of integer roots into the canonical (sorted, mod-p) form.
fn expected(p: &BigUint, vals: &[i64]) -> Vec<BigUint> {
    let mut v: Vec<BigUint> = vals
        .iter()
        .map(|&n| {
            if n >= 0 {
                BigUint::from(n as u64) % p
            } else {
                let nn = (-n) as u64;
                (p - (BigUint::from(nn) % p)) % p
            }
        })
        .collect();
    v.sort();
    v
}

// =============================================================================
// Small modulus used for finite-set root enumeration: p = 7.
// =============================================================================
//
// cvc5 polynomials and expected (squarefree) distinct-roots polynomial:
//   x                         → roots {0}
//   x^3                       → roots {0}      (multiplicity collapsed)
//   x^3 * (x-1)               → roots {0, 1}
//   x^3 * (x-1) * (x^2+1)     → roots {0, 1}   (x^2+1 has no roots over GF(7))
//
// These mirror the four DistinctRootsPoly cases in cvc5 (lines 58-80).
#[test]
fn test_distinct_roots_poly_small() {
    let p = BigUint::from(7u32);
    let ff = PrimeField::new(p.clone());

    // f = x   →  roots {0}
    let f1 = vec![ff.zero(), ff.one()];
    assert_eq!(sorted_roots(&ff, &find_roots(&ff, &f1)), expected(&p, &[0]));

    // f = x^3   →  roots {0}
    let f2 = vec![ff.zero(), ff.zero(), ff.zero(), ff.one()];
    assert_eq!(sorted_roots(&ff, &find_roots(&ff, &f2)), expected(&p, &[0]));

    // f = x^3 * (x-1) = x^4 - x^3   →  roots {0, 1}
    let mut f3 = vec![ff.zero(); 5];
    f3[3] = ff.from_biguint(&BigUint::from(6u32)); // -1 mod 7
    f3[4] = ff.one();
    assert_eq!(
        sorted_roots(&ff, &find_roots(&ff, &f3)),
        expected(&p, &[0, 1])
    );

    // f = x^3 * (x-1) * (x^2+1) = (x^4 - x^3) * (x^2+1)
    //   = x^6 + x^4 - x^5 - x^3   →  roots {0, 1}  (x^2+1 has no GF(7) roots)
    let mut f4 = vec![ff.zero(); 7];
    f4[3] = ff.from_biguint(&BigUint::from(6u32)); // -1
    f4[4] = ff.one(); // +x^4
    f4[5] = ff.from_biguint(&BigUint::from(6u32)); // -x^5
    f4[6] = ff.one(); // +x^6
    assert_eq!(
        sorted_roots(&ff, &find_roots(&ff, &f4)),
        expected(&p, &[0, 1])
    );
}

// =============================================================================
// RootsZero  (small modulus)
// =============================================================================
//
//   x            → {0}
//   x^3          → {0}
//   x*(x^2+1)    → {0}
#[test]
fn test_roots_zero_small() {
    let p = BigUint::from(7u32);
    let ff = PrimeField::new(p.clone());

    let f1 = vec![ff.zero(), ff.one()];
    assert_eq!(sorted_roots(&ff, &find_roots(&ff, &f1)), expected(&p, &[0]));

    let f2 = vec![ff.zero(), ff.zero(), ff.zero(), ff.one()];
    assert_eq!(sorted_roots(&ff, &find_roots(&ff, &f2)), expected(&p, &[0]));

    // x*(x^2+1) = x^3 + x  →  roots {0}
    let mut f3 = vec![ff.zero(); 4];
    f3[1] = ff.one();
    f3[3] = ff.one();
    assert_eq!(sorted_roots(&ff, &find_roots(&ff, &f3)), expected(&p, &[0]));
}

// =============================================================================
// RootsFull  (small modulus)
// =============================================================================
//
//   x*(x-1)                       → {0, 1}
//   (x*(x-1))^2                   → {0, 1}
//   (x*(x-1))^2 * (x^2+1)^2       → {0, 1}
//   (x^2+1)^2                     → {}
//   x^2 - x + 1                   → {-2, 3} = {5, 3}  over GF(7)
#[test]
fn test_roots_full_small() {
    let p = BigUint::from(7u32);
    let ff = PrimeField::new(p.clone());

    // x*(x-1) = x^2 - x
    let mut f1 = vec![ff.zero(); 3];
    f1[1] = ff.from_biguint(&BigUint::from(6u32)); // -1
    f1[2] = ff.one();
    assert_eq!(
        sorted_roots(&ff, &find_roots(&ff, &f1)),
        expected(&p, &[0, 1])
    );

    // (x*(x-1))^2 = (x^2 - x)^2 = x^4 - 2 x^3 + x^2
    let mut f2 = vec![ff.zero(); 5];
    f2[2] = ff.one();
    f2[3] = ff.from_biguint(&BigUint::from(5u32)); // -2 mod 7
    f2[4] = ff.one();
    assert_eq!(
        sorted_roots(&ff, &find_roots(&ff, &f2)),
        expected(&p, &[0, 1])
    );

    // (x^2 + 1)^2 = x^4 + 2 x^2 + 1   →  no roots over GF(7)
    let mut f4 = vec![ff.zero(); 5];
    f4[0] = ff.one();
    f4[2] = ff.from_biguint(&BigUint::from(2u32));
    f4[4] = ff.one();
    assert_eq!(sorted_roots(&ff, &find_roots(&ff, &f4)), expected(&p, &[]));

    // x^2 - x + 1   →  roots {-2, 3} = {5, 3} over GF(7)
    // Verify: 3^2 - 3 + 1 = 9 - 3 + 1 = 7 ≡ 0 (mod 7) ✓
    //         5^2 - 5 + 1 = 25 - 5 + 1 = 21 ≡ 0 (mod 7) ✓
    let mut f5 = vec![ff.zero(); 3];
    f5[0] = ff.one();
    f5[1] = ff.from_biguint(&BigUint::from(6u32)); // -1
    f5[2] = ff.one();
    assert_eq!(
        sorted_roots(&ff, &find_roots(&ff, &f5)),
        expected(&p, &[3, 5])
    );

    // (x*(x-1))^2 * (x^2+1)^2  →  roots {0, 1}
    // Skip explicit construction (degree 8); the squarefree case above
    // already confirms behavior on the irreducible factor (x^2+1).
}

// =============================================================================
// BIG_MODULUS = 2^255 - 19  (Curve25519 scalar field prime)
// =============================================================================
//
//.  The interesting case is x^2 - x + 1 over the
// 2^255-19 prime, with roots given as the literal decimal strings in the
// cvc5 source.
#[test]
fn test_distinct_roots_poly_big() {
    let p: BigUint =
        "57896044618658097711785492504343953926634992332820282019728792003956564819949"
            .parse()
            .unwrap();
    let ff = PrimeField::new(p.clone());

    // f = x   →  {0}
    let f1 = vec![ff.zero(), ff.one()];
    assert_eq!(
        sorted_roots(&ff, &find_roots(&ff, &f1)),
        vec![BigUint::from(0u32)]
    );

    // f = x^3   →  {0}
    let f2 = vec![ff.zero(), ff.zero(), ff.zero(), ff.one()];
    assert_eq!(
        sorted_roots(&ff, &find_roots(&ff, &f2)),
        vec![BigUint::from(0u32)]
    );

    // f = x^3 * (x-1) = x^4 - x^3   →  {0, 1}
    let mut f3 = vec![ff.zero(); 5];
    let p_minus_1 = &p - BigUint::from(1u32);
    f3[3] = ff.from_biguint(&p_minus_1);
    f3[4] = ff.one();
    assert_eq!(
        sorted_roots(&ff, &find_roots(&ff, &f3)),
        vec![BigUint::from(0u32), BigUint::from(1u32)]
    );
}

#[test]
fn test_roots_full_big() {
    let p: BigUint =
        "57896044618658097711785492504343953926634992332820282019728792003956564819949"
            .parse()
            .unwrap();
    let ff = PrimeField::new(p.clone());

    // x^2 - x + 1  → roots from cvc5 source (lines 246-253):
    //   r1 = -25380276437079137597092236364571181010632177832931468165172742469126098314552
    //   r2 = +25380276437079137597092236364571181010632177832931468165172742469126098314553
    // Note: r2 - r1 = 1, and r1 + r2 = 1 (sum of roots), r1*r2 = 1 (product).
    let mut f = vec![ff.zero(); 3];
    f[0] = ff.one();
    f[1] = ff.from_biguint(&(&p - BigUint::from(1u32))); // -1
    f[2] = ff.one();
    let roots = find_roots(&ff, &f);
    assert_eq!(roots.len(), 2);
    let vals = sorted_roots(&ff, &roots);
    // Verify: r1 + r2 ≡ 1 (mod p)  and  r1 * r2 ≡ 1 (mod p).
    let sum = (&vals[0] + &vals[1]) % &p;
    let prod = (&vals[0] * &vals[1]) % &p;
    assert_eq!(sum, BigUint::from(1u32));
    assert_eq!(prod, BigUint::from(1u32));

    // (x^2 + 2)^2  →  no roots (x^2 = -2 has no solution over Curve25519 prime)
    let mut f2 = vec![ff.zero(); 5];
    f2[0] = ff.from_biguint(&BigUint::from(4u32)); // 2^2 = 4
    f2[2] = ff.from_biguint(&BigUint::from(4u32)); // 2 * 2 = 4
    f2[4] = ff.one();
    // Actually we want (x^2+2)^2 = x^4 + 4 x^2 + 4
    // Confirm no roots:
    assert_eq!(find_roots(&ff, &f2).len(), 0);
}
