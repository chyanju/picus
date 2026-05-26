use super::*;

fn bn128() -> BigUint {
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse()
        .unwrap()
}

#[test]
fn small_prime_basics() {
    let f = PrimeField::new(BigUint::from(17u32));
    let a = f.from_u64(10);
    let b = f.from_u64(12);
    let c = f.add(&a, &b);
    assert_eq!(f.to_biguint(&c), BigUint::from(5u32));

    let x = f.from_u64(3);
    let y = f.from_u64(6);
    assert_eq!(f.to_biguint(&f.mul(&x, &y)), BigUint::from(1u32));
    assert_eq!(f.inv(&x).unwrap(), y);

    let d = f.div(&f.from_u64(1), &x).unwrap();
    assert_eq!(d, y);
}

#[test]
fn sub_underflow() {
    let f = PrimeField::new(BigUint::from(7u32));
    let a = f.from_u64(2);
    let b = f.from_u64(5);
    let c = f.sub(&a, &b);
    assert_eq!(f.to_biguint(&c), BigUint::from(4u32));

    let mut a2 = f.from_u64(2);
    f.sub_assign(&mut a2, &b);
    assert_eq!(f.to_biguint(&a2), BigUint::from(4u32));
}

#[test]
fn from_i64_negative() {
    let f = PrimeField::new(BigUint::from(7u32));
    assert_eq!(f.to_biguint(&f.from_i64(-1)), BigUint::from(6u32));
    assert_eq!(f.to_biguint(&f.from_i64(-7)), BigUint::from(0u32));
    assert_eq!(f.to_biguint(&f.from_i64(-8)), BigUint::from(6u32));
}

#[test]
fn neg_works() {
    let f = PrimeField::new(BigUint::from(7u32));
    let a = f.from_u64(3);
    let na = f.neg(&a);
    assert_eq!(f.to_biguint(&na), BigUint::from(4u32));
    assert!(f.is_zero(&f.add(&a, &na)));
    assert!(f.is_zero(&f.neg(&f.zero())));
}

#[test]
fn fermat_pow_bn128() {
    let p = bn128();
    let f = PrimeField::new(p.clone());
    let a = f.from_u64(2);
    let exp = &p - BigUint::from(1u32);
    let res = f.pow(&a, &exp);
    assert!(f.is_one(&res));
}

#[test]
fn inverse_bn128() {
    let p = bn128();
    let f = PrimeField::new(p.clone());
    let a = f.from_u64(123456789);
    let ai = f.inv(&a).unwrap();
    assert!(f.is_one(&f.mul(&a, &ai)));
}

#[test]
fn axioms_random() {
    let f = PrimeField::new(BigUint::from(101u32));
    for x in 0u64..101 {
        for y in 0u64..101 {
            let a = f.from_u64(x);
            let b = f.from_u64(y);
            assert_eq!(f.add(&a, &b), f.add(&b, &a));
            assert_eq!(f.mul(&a, &b), f.mul(&b, &a));
            assert!(f.is_zero(&f.add(&a, &f.neg(&a))));
        }
    }
}

/// Cross-check the small-prime path against the GMP path on a
/// prime that fits both. Same operations must produce
/// `to_biguint`-equal outputs.
#[test]
fn small_matches_gmp_axioms() {
    // Both fields are constructed from the same prime; `new`
    // routes the first to Small (bits <= 64). To exercise the
    // Gmp path on the same value, construct a Gmp-only field
    // manually.
    let p_bu = BigUint::from(7919u32);
    let f_small = PrimeField::new(p_bu.clone());
    let f_gmp = {
        let prime_int = biguint_to_integer(&p_bu);
        let result_bits = prime_int.significant_bits() as usize + 1;
        let product_bits = 2 * (prime_int.significant_bits() as usize) + 1;
        PrimeField {
            prime_bu: Arc::new(p_bu.clone()),
            kind: FieldKind::Gmp {
                prime: Arc::new(prime_int),
                result_bits,
                product_bits,
            },
        }
    };
    // Verify the dispatch picked the expected variants.
    assert!(matches!(f_small.kind, FieldKind::Small { .. }));
    assert!(matches!(f_gmp.kind, FieldKind::Gmp { .. }));

    for x in [0u64, 1, 2, 3, 100, 7918, 7917, 4242] {
        for y in [0u64, 1, 5, 99, 7918, 1234] {
            let a_s = f_small.from_u64(x);
            let b_s = f_small.from_u64(y);
            let a_g = f_gmp.from_u64(x);
            let b_g = f_gmp.from_u64(y);
            assert_eq!(
                f_small.to_biguint(&f_small.add(&a_s, &b_s)),
                f_gmp.to_biguint(&f_gmp.add(&a_g, &b_g)),
                "add({}, {})",
                x,
                y
            );
            assert_eq!(
                f_small.to_biguint(&f_small.sub(&a_s, &b_s)),
                f_gmp.to_biguint(&f_gmp.sub(&a_g, &b_g)),
                "sub({}, {})",
                x,
                y
            );
            assert_eq!(
                f_small.to_biguint(&f_small.mul(&a_s, &b_s)),
                f_gmp.to_biguint(&f_gmp.mul(&a_g, &b_g)),
                "mul({}, {})",
                x,
                y
            );
            assert_eq!(
                f_small.to_biguint(&f_small.neg(&a_s)),
                f_gmp.to_biguint(&f_gmp.neg(&a_g)),
                "neg({})",
                x
            );
            if x != 0 {
                assert_eq!(
                    f_small.to_biguint(&f_small.inv(&a_s).unwrap()),
                    f_gmp.to_biguint(&f_gmp.inv(&a_g).unwrap()),
                    "inv({})",
                    x
                );
            }
            assert_eq!(
                f_small.to_biguint(&f_small.pow_u64(&a_s, 13)),
                f_gmp.to_biguint(&f_gmp.pow_u64(&a_g, 13)),
                "pow({}, 13)",
                x
            );
        }
    }
}

/// Same cross-check as [`small_matches_gmp_axioms`], but on a prime
/// **above 2^63** (Goldilocks, `0xFFFFFFFF00000001` = 2^64 - 2^32 + 1).
/// This is the only regime that exercises the Small-arm `small_add`
/// wraparound branch (`s >= p128`) and large-operand `small_mul` /
/// `small_inv` — the path any 64-bit user prime takes, and one that had
/// no differential coverage.
#[test]
fn small_matches_gmp_axioms_above_2_63() {
    const P: u64 = 0xFFFF_FFFF_0000_0001; // 2^64 - 2^32 + 1, prime, > 2^63
    let p_bu = BigUint::from(P);
    let f_small = PrimeField::new(p_bu.clone());
    let f_gmp = {
        let prime_int = biguint_to_integer(&p_bu);
        let result_bits = prime_int.significant_bits() as usize + 1;
        let product_bits = 2 * (prime_int.significant_bits() as usize) + 1;
        PrimeField {
            prime_bu: Arc::new(p_bu.clone()),
            kind: FieldKind::Gmp {
                prime: Arc::new(prime_int),
                result_bits,
                product_bits,
            },
        }
    };
    assert!(matches!(f_small.kind, FieldKind::Small { .. }), "prime must route to Small arm");
    assert!(matches!(f_gmp.kind, FieldKind::Gmp { .. }));

    // Operands chosen to drive add/sub/mul wraparound: values near p,
    // exact 2^63 boundaries, and a midpoint.
    let xs = [0u64, 1, 2, P - 1, P - 2, 1u64 << 63, (1u64 << 63) + 1, P / 2, 12_345_678_901_234_567];
    let ys = [0u64, 1, P - 1, P - 3, 1u64 << 63, 99_999_999_999];
    for &x in &xs {
        for &y in &ys {
            let (a_s, b_s) = (f_small.from_u64(x), f_small.from_u64(y));
            let (a_g, b_g) = (f_gmp.from_u64(x), f_gmp.from_u64(y));
            assert_eq!(
                f_small.to_biguint(&f_small.add(&a_s, &b_s)),
                f_gmp.to_biguint(&f_gmp.add(&a_g, &b_g)), "add({x}, {y})");
            assert_eq!(
                f_small.to_biguint(&f_small.sub(&a_s, &b_s)),
                f_gmp.to_biguint(&f_gmp.sub(&a_g, &b_g)), "sub({x}, {y})");
            assert_eq!(
                f_small.to_biguint(&f_small.mul(&a_s, &b_s)),
                f_gmp.to_biguint(&f_gmp.mul(&a_g, &b_g)), "mul({x}, {y})");
            assert_eq!(
                f_small.to_biguint(&f_small.neg(&a_s)),
                f_gmp.to_biguint(&f_gmp.neg(&a_g)), "neg({x})");
            if x != 0 {
                assert_eq!(
                    f_small.to_biguint(&f_small.inv(&a_s).unwrap()),
                    f_gmp.to_biguint(&f_gmp.inv(&a_g).unwrap()), "inv({x})");
            }
            assert_eq!(
                f_small.to_biguint(&f_small.pow_u64(&a_s, 13)),
                f_gmp.to_biguint(&f_gmp.pow_u64(&a_g, 13)), "pow({x}, 13)");
        }
    }
}

#[test]
fn small_prime_dispatch_is_picked() {
    // Verify auto-selection: primes <= 64 bits route to Small.
    let f_small = PrimeField::new(BigUint::from(7u32));
    assert!(matches!(f_small.kind, FieldKind::Small { .. }));
    let f_small_max = PrimeField::new(BigUint::from(u64::MAX - 58u64)); // largest 64-bit prime
    assert!(matches!(f_small_max.kind, FieldKind::Small { .. }));
    let f_gmp = PrimeField::new(bn128());
    assert!(matches!(f_gmp.kind, FieldKind::Gmp { .. }));
}
