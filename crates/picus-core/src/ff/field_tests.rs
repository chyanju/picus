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
/// `small_inv` — the path any 64-bit user prime (e.g. a Goldilocks-style
/// field) takes.
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

// ──────────────────────────── Spec-driven property tests ────────────────
//
// Expected values are derived from FIELD AXIOMS (additive/multiplicative
// group laws), Fermat's little theorem, distributivity, and identities
// of the square-and-multiply algorithm — NOT from observed source
// behaviour. A failure here is a soundness bug in PrimeField.
//
// Small edge primes (GF(2), GF(3), GF(5), GF(7), GF(13)) exhaustively
// exercise every (a, b) pair. BN128 covers the GMP arm.

/// Build a small set of representative field elements covering 0, 1,
/// the multiplicative generator-region (small ints), and `p - 1`
/// (== -1 mod p). Pure: no calls into the field itself for what to test.
fn small_primes() -> [u64; 5] {
    [2, 3, 5, 7, 13]
}

/// Pick test values for a large prime: 0, 1, several small constants,
/// and `p - 1`. Constants chosen independently of the field's behaviour.
fn bn128_test_values(f: &PrimeField) -> Vec<FieldElem> {
    let p = f.prime().clone();
    vec![
        f.zero(),
        f.one(),
        f.from_u64(2),
        f.from_u64(3),
        f.from_u64(7),
        f.from_u64(123_456_789),
        f.from_u64(u64::MAX),
        f.from_biguint(&(&p - BigUint::from(1u32))),
        f.from_biguint(&(&p - BigUint::from(2u32))),
    ]
}

/// (1) ADDITIVE IDENTITY: a + 0 == a and 0 + a == a, for every a in GF(p).
/// Property: 0 is the neutral element of the additive group.
#[test]
fn prop_additive_identity_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let zero = f.zero();
        for x in 0..p {
            let a = f.from_u64(x);
            assert_eq!(f.add(&a, &zero), a, "GF({p}): {x} + 0 != {x}");
            assert_eq!(f.add(&zero, &a), a, "GF({p}): 0 + {x} != {x}");
        }
    }
}

#[test]
fn prop_additive_identity_bn128() {
    let f = PrimeField::new(bn128());
    let zero = f.zero();
    for a in bn128_test_values(&f) {
        assert_eq!(f.add(&a, &zero), a);
        assert_eq!(f.add(&zero, &a), a);
    }
}

/// (1) MULTIPLICATIVE IDENTITY: a * 1 == a and 1 * a == a, every a in GF(p).
#[test]
fn prop_multiplicative_identity_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let one = f.one();
        for x in 0..p {
            let a = f.from_u64(x);
            assert_eq!(f.mul(&a, &one), a, "GF({p}): {x} * 1 != {x}");
            assert_eq!(f.mul(&one, &a), a, "GF({p}): 1 * {x} != {x}");
        }
    }
}

#[test]
fn prop_multiplicative_identity_bn128() {
    let f = PrimeField::new(bn128());
    let one = f.one();
    for a in bn128_test_values(&f) {
        assert_eq!(f.mul(&a, &one), a);
        assert_eq!(f.mul(&one, &a), a);
    }
}

/// (1) MULTIPLICATIVE ZERO: a * 0 == 0 and 0 * a == 0.
/// Property: absorbing element of the multiplicative monoid.
#[test]
fn prop_multiplicative_zero_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let zero = f.zero();
        for x in 0..p {
            let a = f.from_u64(x);
            assert!(f.is_zero(&f.mul(&a, &zero)), "GF({p}): {x} * 0 != 0");
            assert!(f.is_zero(&f.mul(&zero, &a)), "GF({p}): 0 * {x} != 0");
        }
    }
}

/// (1) ADDITIVE INVERSE: a + (-a) == 0, for every a in GF(p).
#[test]
fn prop_additive_inverse_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let a = f.from_u64(x);
            let na = f.neg(&a);
            assert!(f.is_zero(&f.add(&a, &na)), "GF({p}): {x} + (-{x}) != 0");
            assert!(f.is_zero(&f.add(&na, &a)));
            // Double-negation: -(-a) == a.
            assert_eq!(f.neg(&na), a, "GF({p}): -(-{x}) != {x}");
        }
    }
}

#[test]
fn prop_additive_inverse_bn128() {
    let f = PrimeField::new(bn128());
    for a in bn128_test_values(&f) {
        let na = f.neg(&a);
        assert!(f.is_zero(&f.add(&a, &na)));
        assert_eq!(f.neg(&na), a);
    }
}

/// (1) MULTIPLICATIVE INVERSE: for a != 0, a * a^{-1} == 1.
/// Also: inv(0) is None (0 has no multiplicative inverse in a field).
#[test]
fn prop_multiplicative_inverse_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        assert!(f.inv(&f.zero()).is_none(), "GF({p}): inv(0) must be None");
        for x in 1..p {
            let a = f.from_u64(x);
            let ai = f.inv(&a).expect("nonzero must invert in a field");
            assert!(f.is_one(&f.mul(&a, &ai)), "GF({p}): {x} * inv({x}) != 1");
            assert!(f.is_one(&f.mul(&ai, &a)));
            // Involution: inv(inv(a)) == a.
            assert_eq!(f.inv(&ai).unwrap(), a, "GF({p}): inv(inv({x})) != {x}");
        }
    }
}

#[test]
fn prop_multiplicative_inverse_bn128() {
    let f = PrimeField::new(bn128());
    assert!(f.inv(&f.zero()).is_none());
    for a in bn128_test_values(&f) {
        if f.is_zero(&a) {
            continue;
        }
        let ai = f.inv(&a).expect("nonzero must invert");
        assert!(f.is_one(&f.mul(&a, &ai)));
        assert_eq!(f.inv(&ai).unwrap(), a);
    }
}

/// (1) ADDITIVE COMMUTATIVITY: a + b == b + a.
#[test]
fn prop_add_commutative_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                assert_eq!(f.add(&a, &b), f.add(&b, &a), "GF({p}): {x} + {y} != {y} + {x}");
            }
        }
    }
}

/// (1) MULTIPLICATIVE COMMUTATIVITY: a * b == b * a.
#[test]
fn prop_mul_commutative_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                assert_eq!(f.mul(&a, &b), f.mul(&b, &a), "GF({p}): {x} * {y} != {y} * {x}");
            }
        }
    }
}

/// (1) ADDITIVE ASSOCIATIVITY: (a + b) + c == a + (b + c).
#[test]
fn prop_add_associative_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                for z in 0..p {
                    let a = f.from_u64(x);
                    let b = f.from_u64(y);
                    let c = f.from_u64(z);
                    let lhs = f.add(&f.add(&a, &b), &c);
                    let rhs = f.add(&a, &f.add(&b, &c));
                    assert_eq!(lhs, rhs, "GF({p}): assoc add ({x},{y},{z})");
                }
            }
        }
    }
}

/// (1) MULTIPLICATIVE ASSOCIATIVITY: (a * b) * c == a * (b * c).
#[test]
fn prop_mul_associative_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                for z in 0..p {
                    let a = f.from_u64(x);
                    let b = f.from_u64(y);
                    let c = f.from_u64(z);
                    let lhs = f.mul(&f.mul(&a, &b), &c);
                    let rhs = f.mul(&a, &f.mul(&b, &c));
                    assert_eq!(lhs, rhs, "GF({p}): assoc mul ({x},{y},{z})");
                }
            }
        }
    }
}

/// (1) LEFT DISTRIBUTIVITY: a * (b + c) == a*b + a*c.
/// (1) RIGHT DISTRIBUTIVITY: (a + b) * c == a*c + b*c.
#[test]
fn prop_distributivity_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                for z in 0..p {
                    let a = f.from_u64(x);
                    let b = f.from_u64(y);
                    let c = f.from_u64(z);
                    let left = f.mul(&a, &f.add(&b, &c));
                    let left_expanded = f.add(&f.mul(&a, &b), &f.mul(&a, &c));
                    assert_eq!(left, left_expanded, "GF({p}): left-dist ({x},{y},{z})");
                    let right = f.mul(&f.add(&a, &b), &c);
                    let right_expanded = f.add(&f.mul(&a, &c), &f.mul(&b, &c));
                    assert_eq!(right, right_expanded, "GF({p}): right-dist ({x},{y},{z})");
                }
            }
        }
    }
}

#[test]
fn prop_distributivity_bn128() {
    let f = PrimeField::new(bn128());
    let vals = bn128_test_values(&f);
    for a in &vals {
        for b in &vals {
            for c in &vals {
                let left = f.mul(a, &f.add(b, c));
                let left_expanded = f.add(&f.mul(a, b), &f.mul(a, c));
                assert_eq!(left, left_expanded);
            }
        }
    }
}

/// (1) SUBTRACTION IS ADD-NEG: a - b == a + (-b).
/// Property derives from the definition of the additive group.
#[test]
fn prop_sub_is_add_neg_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let lhs = f.sub(&a, &b);
                let rhs = f.add(&a, &f.neg(&b));
                assert_eq!(lhs, rhs, "GF({p}): {x}-{y} != {x}+(-{y})");
                // And a - a == 0.
                assert!(f.is_zero(&f.sub(&a, &a)));
            }
        }
    }
}

/// (1) DIVISION IS MUL-INV: a / b == a * b^{-1}, for b != 0.
#[test]
fn prop_div_is_mul_inv_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 1..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let lhs = f.div(&a, &b).expect("nonzero divisor");
                let rhs = f.mul(&a, &f.inv(&b).unwrap());
                assert_eq!(lhs, rhs, "GF({p}): {x}/{y} != {x} * inv({y})");
            }
        }
        // Division by zero must yield None.
        assert!(f.div(&f.one(), &f.zero()).is_none());
    }
}

/// (1) FERMAT'S LITTLE THEOREM: a^p == a for every a in GF(p). This is
/// the textbook fact, independent of the implementation of `pow`.
#[test]
fn prop_fermat_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let p_bu = BigUint::from(p);
        for x in 0..p {
            let a = f.from_u64(x);
            let ap = f.pow(&a, &p_bu);
            assert_eq!(ap, a, "GF({p}): {x}^{p} != {x} (Fermat)");
            // Stronger: for a != 0, a^{p-1} == 1.
            if x != 0 {
                let exp = &p_bu - BigUint::from(1u32);
                let ap_minus_1 = f.pow(&a, &exp);
                assert!(f.is_one(&ap_minus_1), "GF({p}): {x}^{p}-1 != 1");
            }
        }
    }
}

/// (1) pow_u64 == pow(BigUint) on the same exponent.
/// The two entry points implement the same algebraic function, so they
/// must agree on every (a, e) pair — independent of which arm runs.
#[test]
fn prop_pow_u64_matches_pow_bigint_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for e in 0u64..(2 * p + 3) {
                let a = f.from_u64(x);
                let lhs = f.pow_u64(&a, e);
                let rhs = f.pow(&a, &BigUint::from(e));
                assert_eq!(lhs, rhs, "GF({p}): pow_u64({x},{e}) != pow({x},{e})");
            }
        }
    }
}

/// (1) pow(a, e) == repeated multiplication: a * a * ... (e times).
/// Spec for square-and-multiply: it must agree with the naive O(e) loop.
#[test]
fn prop_pow_matches_repeated_mul_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let a = f.from_u64(x);
            // Independently compute a^e by left-fold multiplication.
            let mut naive = f.one();
            for e in 0u64..(2 * p + 3) {
                let by_pow = f.pow_u64(&a, e);
                assert_eq!(by_pow, naive, "GF({p}): pow({x},{e}) != naive iterated mul");
                naive = f.mul(&naive, &a);
            }
        }
    }
}

/// (1) pow EXPONENT IDENTITIES:
///   a^0 == 1 (for all a, including a == 0 by the conventional
///   definition that the empty product is 1).
///   a^1 == a.
///   a^(e1 + e2) == a^e1 * a^e2.
#[test]
fn prop_pow_exponent_identities_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let a = f.from_u64(x);
            assert!(f.is_one(&f.pow_u64(&a, 0)), "GF({p}): {x}^0 != 1");
            assert_eq!(f.pow_u64(&a, 1), a, "GF({p}): {x}^1 != {x}");
            for e1 in 0u64..6 {
                for e2 in 0u64..6 {
                    let lhs = f.pow_u64(&a, e1 + e2);
                    let rhs = f.mul(&f.pow_u64(&a, e1), &f.pow_u64(&a, e2));
                    assert_eq!(lhs, rhs, "GF({p}): {x}^({e1}+{e2}) != {x}^{e1} * {x}^{e2}");
                }
            }
        }
    }
}

#[test]
fn prop_pow_exponent_identities_bn128() {
    let f = PrimeField::new(bn128());
    for a in bn128_test_values(&f) {
        assert!(f.is_one(&f.pow_u64(&a, 0)));
        assert_eq!(f.pow_u64(&a, 1), a);
        for e1 in 0u64..5 {
            for e2 in 0u64..5 {
                let lhs = f.pow_u64(&a, e1 + e2);
                let rhs = f.mul(&f.pow_u64(&a, e1), &f.pow_u64(&a, e2));
                assert_eq!(lhs, rhs);
            }
        }
    }
}

/// (1) FROZENKEL: For all a, b in GF(p) with p prime,
/// (a + b)^p == a^p + b^p. This follows from the binomial theorem
/// since every middle coefficient is divisible by p in GF(p).
/// (Also called the "Frobenius endomorphism" property.)
#[test]
fn prop_frobenius_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let p_bu = BigUint::from(p);
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let lhs = f.pow(&f.add(&a, &b), &p_bu);
                let rhs = f.add(&f.pow(&a, &p_bu), &f.pow(&b, &p_bu));
                assert_eq!(lhs, rhs, "GF({p}): ({x}+{y})^{p} != {x}^{p} + {y}^{p}");
            }
        }
    }
}

/// (1) NEG VIA p-1: -a == (p-1) * a, since p ≡ 0 in GF(p) so
/// (p-1)*a ≡ -a (mod p). Independent algebraic check on `neg`.
#[test]
fn prop_neg_equals_p_minus_one_times_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let p_minus_1 = f.from_u64(p - 1);
        for x in 0..p {
            let a = f.from_u64(x);
            assert_eq!(f.neg(&a), f.mul(&p_minus_1, &a), "GF({p}): -{x} != (p-1)*{x}");
        }
    }
}

/// (2) ROUND-TRIP through from_biguint / to_biguint.
/// For a value v already reduced in [0, p), from_biguint then
/// to_biguint must return v unchanged.
#[test]
fn prop_biguint_roundtrip_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let bu = BigUint::from(x);
            let a = f.from_biguint(&bu);
            assert_eq!(f.to_biguint(&a), bu, "GF({p}): roundtrip {x}");
        }
    }
}

#[test]
fn prop_biguint_roundtrip_bn128() {
    let f = PrimeField::new(bn128());
    let candidates = [
        BigUint::from(0u32),
        BigUint::from(1u32),
        BigUint::from(2u32),
        BigUint::from(123_456_789u64),
        BigUint::from(u64::MAX),
        &bn128() - BigUint::from(1u32),
        &bn128() - BigUint::from(2u32),
    ];
    for bu in &candidates {
        let a = f.from_biguint(bu);
        assert_eq!(f.to_biguint(&a), *bu, "BN128 roundtrip {bu}");
    }
}

/// (2) from_u64 REDUCTION: from_u64(v) reduces v mod p.
/// Spec: the result is congruent to v mod p, and is in [0, p).
#[test]
fn prop_from_u64_reduces_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        // Take a span well beyond p to force reduction.
        for v in 0u64..(5 * p + 7) {
            let a = f.from_u64(v);
            let bu = f.to_biguint(&a);
            // Expected from MATH: v mod p.
            assert_eq!(bu, BigUint::from(v % p), "GF({p}): from_u64({v}) != {v} mod {p}");
            // Canonical form: result in [0, p).
            assert!(bu < *f.prime());
        }
    }
}

/// (2) from_i64 REDUCTION: from_i64(v) reduces v mod p with the
/// least-non-negative representative.
/// Spec: ((v mod p) + p) mod p, always in [0, p).
#[test]
fn prop_from_i64_reduces_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let pi = p as i64;
        for v in -(3 * pi + 5)..(3 * pi + 5) {
            let a = f.from_i64(v);
            let bu = f.to_biguint(&a);
            let expected = ((v % pi) + pi) % pi;
            assert_eq!(
                bu,
                BigUint::from(expected as u64),
                "GF({p}): from_i64({v}) != ((v mod p)+p) mod p"
            );
            assert!(bu < *f.prime());
        }
    }
}

/// (3) IDEMPOTENCE / DETERMINISM: same input → same output across two
/// calls. The field is a pure mathematical object; no hidden state.
#[test]
fn prop_deterministic_ops_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                assert_eq!(f.add(&a, &b), f.add(&a, &b));
                assert_eq!(f.sub(&a, &b), f.sub(&a, &b));
                assert_eq!(f.mul(&a, &b), f.mul(&a, &b));
                assert_eq!(f.neg(&a), f.neg(&a));
                if x != 0 {
                    assert_eq!(f.inv(&a).unwrap(), f.inv(&a).unwrap());
                }
                assert_eq!(f.pow_u64(&a, 11), f.pow_u64(&a, 11));
            }
        }
    }
}

/// (4) CANONICAL FORM INVARIANT: every result lies in [0, p).
/// Property: the field stores canonical representatives. Tests every
/// arithmetic op against the public prime.
#[test]
fn prop_canonical_form_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let bp = f.prime().clone();
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                assert!(f.to_biguint(&f.add(&a, &b)) < bp);
                assert!(f.to_biguint(&f.sub(&a, &b)) < bp);
                assert!(f.to_biguint(&f.mul(&a, &b)) < bp);
                assert!(f.to_biguint(&f.neg(&a)) < bp);
                if x != 0 {
                    assert!(f.to_biguint(&f.inv(&a).unwrap()) < bp);
                }
                assert!(f.to_biguint(&f.pow_u64(&a, 7)) < bp);
            }
        }
    }
}

/// (4) is_zero / is_one MATCH CANONICAL VALUE: by the canonical-form
/// invariant, is_zero(x) iff x == 0 and is_one(x) iff x == 1.
#[test]
fn prop_is_zero_is_one_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let a = f.from_u64(x);
            assert_eq!(f.is_zero(&a), x == 0, "GF({p}): is_zero({x}) wrong");
            assert_eq!(f.is_one(&a), x == 1, "GF({p}): is_one({x}) wrong");
        }
    }
}

/// (8) DETERMINISM ACROSS INDEPENDENT FIELD INSTANCES: two fields
/// constructed independently from the same prime must agree on
/// every op. Property: the field semantics depends only on the prime.
#[test]
fn prop_independent_instances_agree_small_primes() {
    for &p in &small_primes() {
        let f1 = PrimeField::new(BigUint::from(p));
        let f2 = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a1 = f1.from_u64(x);
                let b1 = f1.from_u64(y);
                let a2 = f2.from_u64(x);
                let b2 = f2.from_u64(y);
                assert_eq!(f1.to_biguint(&f1.add(&a1, &b1)), f2.to_biguint(&f2.add(&a2, &b2)));
                assert_eq!(f1.to_biguint(&f1.mul(&a1, &b1)), f2.to_biguint(&f2.mul(&a2, &b2)));
            }
        }
    }
}

/// (7) GF(2) EDGE PRIME: the smallest prime. Spec: -1 == 1, every
/// nonzero element is its own inverse, and (a + b)^2 = a^2 + b^2
/// (Frobenius at p=2).
#[test]
fn prop_gf2_edge_cases() {
    let f = PrimeField::new(BigUint::from(2u32));
    let zero = f.zero();
    let one = f.one();
    // In GF(2): -1 == 1.
    assert_eq!(f.neg(&one), one);
    // The only nonzero element is 1; its inverse is itself.
    assert_eq!(f.inv(&one).unwrap(), one);
    // 1 + 1 == 0 in characteristic 2.
    assert!(f.is_zero(&f.add(&one, &one)));
    // 1 - 1 == 0.
    assert!(f.is_zero(&f.sub(&one, &one)));
    // Frobenius: x^2 == x.
    assert_eq!(f.pow_u64(&zero, 2), zero);
    assert_eq!(f.pow_u64(&one, 2), one);
}

/// (1) for the additive-inverse-is-neg-equiv: a + b == 0 iff b == -a.
/// Property follows from uniqueness of inverses in an abelian group.
#[test]
fn prop_unique_additive_inverse_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let sum_zero = f.is_zero(&f.add(&a, &b));
                let b_is_neg_a = b == f.neg(&a);
                assert_eq!(sum_zero, b_is_neg_a, "GF({p}): {x}+{y}==0 iff {y}==-{x}");
            }
        }
    }
}

/// (1) UNIQUE MULTIPLICATIVE INVERSE: for a != 0, a * b == 1 iff
/// b == a^{-1}. Property: uniqueness of inverses in a group.
#[test]
fn prop_unique_multiplicative_inverse_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 1..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let prod_one = f.is_one(&f.mul(&a, &b));
                let b_is_inv_a = b == f.inv(&a).unwrap();
                assert_eq!(prod_one, b_is_inv_a, "GF({p}): {x}*{y}==1 iff {y}==inv({x})");
            }
        }
    }
}

/// (4) NO ZERO DIVISORS: for a, b in GF(p) with p prime,
/// a * b == 0 iff a == 0 or b == 0. This is the integral-domain
/// property of a field.
#[test]
fn prop_no_zero_divisors_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let prod_zero = f.is_zero(&f.mul(&a, &b));
                let either_zero = x == 0 || y == 0;
                assert_eq!(prod_zero, either_zero, "GF({p}): {x}*{y}==0 iff {x}==0||{y}==0");
            }
        }
    }
}

/// (1) FERMAT ON BN128: a^p == a for the BN128 prime, where p is the
/// large field characteristic. Independent algebraic check on `pow`.
/// (Compared to the existing `fermat_pow_bn128`, this hits multiple a.)
#[test]
fn prop_fermat_bn128() {
    let p = bn128();
    let f = PrimeField::new(p.clone());
    for a in bn128_test_values(&f) {
        let ap = f.pow(&a, &p);
        assert_eq!(ap, a, "BN128: a^p != a (Fermat)");
    }
}

/// (1) FERMAT VIA EULER: a^{p-1} == 1 for a != 0 in GF(p).
#[test]
fn prop_euler_fermat_bn128() {
    let p = bn128();
    let f = PrimeField::new(p.clone());
    let p_minus_1 = &p - BigUint::from(1u32);
    for a in bn128_test_values(&f) {
        if f.is_zero(&a) {
            continue;
        }
        let r = f.pow(&a, &p_minus_1);
        assert!(f.is_one(&r), "BN128: a^(p-1) != 1");
    }
}

/// (1) INVERSE VIA FERMAT: for a != 0, a^{p-2} == a^{-1}. Spec
/// identity; an independent way to compute the inverse.
#[test]
fn prop_inverse_via_fermat_small_primes() {
    for &p in &small_primes() {
        if p < 2 {
            continue;
        }
        let f = PrimeField::new(BigUint::from(p));
        let p_minus_2 = BigUint::from(p - 2);
        for x in 1..p {
            let a = f.from_u64(x);
            let by_fermat = f.pow(&a, &p_minus_2);
            let by_inv = f.inv(&a).unwrap();
            assert_eq!(by_fermat, by_inv, "GF({p}): {x}^(p-2) != inv({x})");
        }
    }
}

#[test]
fn prop_inverse_via_fermat_bn128() {
    let p = bn128();
    let f = PrimeField::new(p.clone());
    let p_minus_2 = &p - BigUint::from(2u32);
    for a in bn128_test_values(&f) {
        if f.is_zero(&a) {
            continue;
        }
        let by_fermat = f.pow(&a, &p_minus_2);
        let by_inv = f.inv(&a).unwrap();
        assert_eq!(by_fermat, by_inv);
    }
}

/// (7) ZERO POW: 0^e == 0 for e >= 1, and 0^0 == 1 (empty-product convention).
#[test]
fn prop_zero_pow_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let z = f.zero();
        assert!(f.is_one(&f.pow_u64(&z, 0)), "GF({p}): 0^0 != 1");
        for e in 1u64..15 {
            assert!(f.is_zero(&f.pow_u64(&z, e)), "GF({p}): 0^{e} != 0");
        }
    }
}

/// (7) ONE POW: 1^e == 1 for every e.
#[test]
fn prop_one_pow_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let one = f.one();
        for e in 0u64..15 {
            assert!(f.is_one(&f.pow_u64(&one, e)), "GF({p}): 1^{e} != 1");
        }
    }
}

/// (8) DETERMINISM OF pow: two calls with the same (a, e) agree, both
/// on pow and pow_u64.
#[test]
fn prop_pow_deterministic_bn128() {
    let f = PrimeField::new(bn128());
    let exp = BigUint::from(31415926535u64);
    for a in bn128_test_values(&f) {
        let r1 = f.pow(&a, &exp);
        let r2 = f.pow(&a, &exp);
        assert_eq!(r1, r2);
        let r3 = f.pow_u64(&a, 31415926535u64);
        let r4 = f.pow_u64(&a, 31415926535u64);
        assert_eq!(r3, r4);
        assert_eq!(r1, r3, "pow vs pow_u64 must agree");
    }
}

/// (1) NEG-MUL EQUIVALENCES: -(a*b) == (-a)*b == a*(-b).
#[test]
fn prop_neg_mul_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let neg_ab = f.neg(&f.mul(&a, &b));
                let neg_a_b = f.mul(&f.neg(&a), &b);
                let a_neg_b = f.mul(&a, &f.neg(&b));
                assert_eq!(neg_ab, neg_a_b, "GF({p}): -({x}*{y}) != (-{x})*{y}");
                assert_eq!(neg_ab, a_neg_b, "GF({p}): -({x}*{y}) != {x}*(-{y})");
            }
        }
    }
}
