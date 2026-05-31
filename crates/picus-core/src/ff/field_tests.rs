use super::*;

fn bn128() -> BigUint {
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse()
        .unwrap()
}

/// Cross-check the small-prime path against the GMP path on a
/// prime that fits both. Same operations must produce
/// `to_biguint`-equal outputs.
#[test]
fn small_matches_gmp_axioms() {
    // `new` routes a 64-bit-fitting prime to Small; construct a Gmp-only
    // field manually to exercise the Gmp path on the same value.
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

// Expected values come from FIELD AXIOMS (additive/multiplicative
// group laws), Fermat's little theorem, distributivity, and identities
// of the square-and-multiply algorithm. A failure is a soundness bug
// in PrimeField. Small edge primes (GF(2), GF(3), GF(5), GF(7), GF(13))
// exhaustively exercise every (a, b) pair; BN128 covers the GMP arm.

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

/// ADDITIVE IDENTITY: a + 0 == a and 0 + a == a, for every a in GF(p).
/// Property: 0 is the neutral element of the additive group.
#[test]
fn prop_additive_identity() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let zero = f.zero();
        for x in 0..p {
            let a = f.from_u64(x);
            assert_eq!(f.add(&a, &zero), a, "GF({p}): {x} + 0 != {x}");
            assert_eq!(f.add(&zero, &a), a, "GF({p}): 0 + {x} != {x}");
        }
    }
    let f = PrimeField::new(bn128());
    let zero = f.zero();
    for a in bn128_test_values(&f) {
        assert_eq!(f.add(&a, &zero), a);
        assert_eq!(f.add(&zero, &a), a);
    }
}

/// MULTIPLICATIVE IDENTITY: a * 1 == a and 1 * a == a, every a in GF(p).
#[test]
fn prop_multiplicative_identity() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let one = f.one();
        for x in 0..p {
            let a = f.from_u64(x);
            assert_eq!(f.mul(&a, &one), a, "GF({p}): {x} * 1 != {x}");
            assert_eq!(f.mul(&one, &a), a, "GF({p}): 1 * {x} != {x}");
        }
    }
    let f = PrimeField::new(bn128());
    let one = f.one();
    for a in bn128_test_values(&f) {
        assert_eq!(f.mul(&a, &one), a);
        assert_eq!(f.mul(&one, &a), a);
    }
}

/// MULTIPLICATIVE ZERO: a * 0 == 0 and 0 * a == 0.
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

/// ADDITIVE INVERSE: a + (-a) == 0, for every a in GF(p).
#[test]
fn prop_additive_inverse() {
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
    let f = PrimeField::new(bn128());
    for a in bn128_test_values(&f) {
        let na = f.neg(&a);
        assert!(f.is_zero(&f.add(&a, &na)));
        assert_eq!(f.neg(&na), a);
    }
}

/// MULTIPLICATIVE INVERSE: for a != 0, a * a^{-1} == 1.
/// Also: inv(0) is None (0 has no multiplicative inverse in a field).
#[test]
fn prop_multiplicative_inverse() {
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

/// LEFT DISTRIBUTIVITY: a * (b + c) == a*b + a*c.
/// RIGHT DISTRIBUTIVITY: (a + b) * c == a*c + b*c.
#[test]
fn prop_distributivity() {
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

/// SUBTRACTION IS ADD-NEG: a - b == a + (-b).
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

/// DIVISION IS MUL-INV: a / b == a * b^{-1}, for b != 0.
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

/// FERMAT'S LITTLE THEOREM: a^p == a for every a in GF(p). This is
/// the textbook fact, independent of the implementation of `pow`.
/// Also tests the Euler form a^{p-1} == 1 for a != 0.
#[test]
fn prop_fermat() {
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
    // BN128 arm: a^p == a and a^{p-1} == 1 for nonzero a.
    let p = bn128();
    let f = PrimeField::new(p.clone());
    let p_minus_1 = &p - BigUint::from(1u32);
    for a in bn128_test_values(&f) {
        let ap = f.pow(&a, &p);
        assert_eq!(ap, a, "BN128: a^p != a (Fermat)");
        if !f.is_zero(&a) {
            let r = f.pow(&a, &p_minus_1);
            assert!(f.is_one(&r), "BN128: a^(p-1) != 1");
        }
    }
}

/// pow(a, e) == repeated multiplication: a * a * ... (e times).
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

/// pow EXPONENT IDENTITIES:
///   a^0 == 1 (for all a, including a == 0 by the conventional
///   definition that the empty product is 1).
///   a^1 == a.
///   a^(e1 + e2) == a^e1 * a^e2.
#[test]
fn prop_pow_exponent_identities() {
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

/// FROBENIUS ENDOMORPHISM: For all a, b in GF(p) with p prime,
/// (a + b)^p == a^p + b^p. This follows from the binomial theorem
/// since every middle coefficient is divisible by p in GF(p).
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

/// ROUND-TRIP through from_biguint / to_biguint.
/// For a value v already reduced in [0, p), from_biguint then
/// to_biguint must return v unchanged.
#[test]
fn prop_biguint_roundtrip() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let bu = BigUint::from(x);
            let a = f.from_biguint(&bu);
            assert_eq!(f.to_biguint(&a), bu, "GF({p}): roundtrip {x}");
        }
    }
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

/// from_u64 REDUCTION: from_u64(v) reduces v mod p.
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

/// from_i64 REDUCTION: from_i64(v) reduces v mod p with the
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

/// CANONICAL FORM INVARIANT: every result lies in [0, p).
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

/// DETERMINISM ACROSS INDEPENDENT FIELD INSTANCES: two fields
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

/// NO ZERO DIVISORS: for a, b in GF(p) with p prime,
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

/// INVERSE VIA FERMAT: for a != 0, a^{p-2} == a^{-1}. Spec
/// identity; an independent way to compute the inverse.
#[test]
fn prop_inverse_via_fermat() {
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

/// NEG-MUL EQUIVALENCES: -(a*b) == (-a)*b == a*(-b).
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

// ──────────────────────────── in-place / by-value variant agreement ─────
//
// The *_assign and *_owned API points must yield the identical canonical
// element as the by-reference counterparts. These are the hot paths the
// geobucket reducer uses to recycle GMP allocations; a divergence would
// silently corrupt downstream computation.

#[test]
fn prop_add_assign_matches_add_small_primes() {
    // add_assign(a, b) result == add(a, b).
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let expected = f.add(&a, &b);
                let mut a_mut = a.clone();
                f.add_assign(&mut a_mut, &b);
                assert_eq!(a_mut, expected, "GF({p}) add_assign({x},{y})");
            }
        }
    }
    // GMP arm.
    let f = PrimeField::new(bn128());
    let vals = bn128_test_values(&f);
    for a in &vals {
        for b in &vals {
            let expected = f.add(a, b);
            let mut a_mut = a.clone();
            f.add_assign(&mut a_mut, b);
            assert_eq!(a_mut, expected);
        }
    }
}

#[test]
fn prop_sub_assign_matches_sub_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let expected = f.sub(&a, &b);
                let mut a_mut = a.clone();
                f.sub_assign(&mut a_mut, &b);
                assert_eq!(a_mut, expected, "GF({p}) sub_assign({x},{y})");
            }
        }
    }
    let f = PrimeField::new(bn128());
    let vals = bn128_test_values(&f);
    for a in &vals {
        for b in &vals {
            let expected = f.sub(a, b);
            let mut a_mut = a.clone();
            f.sub_assign(&mut a_mut, b);
            assert_eq!(a_mut, expected);
        }
    }
}

#[test]
fn prop_mul_assign_matches_mul_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let expected = f.mul(&a, &b);
                let mut a_mut = a.clone();
                f.mul_assign(&mut a_mut, &b);
                assert_eq!(a_mut, expected, "GF({p}) mul_assign({x},{y})");
            }
        }
    }
    let f = PrimeField::new(bn128());
    let vals = bn128_test_values(&f);
    for a in &vals {
        for b in &vals {
            let expected = f.mul(a, b);
            let mut a_mut = a.clone();
            f.mul_assign(&mut a_mut, b);
            assert_eq!(a_mut, expected);
        }
    }
}

#[test]
fn prop_add_owned_matches_add_small_primes() {
    // add_owned(a, b) recycles GMP buffers but must equal add(a, b).
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let expected = f.add(&a, &b);
                let actual = f.add_owned(a, b);
                assert_eq!(actual, expected, "GF({p}) add_owned({x},{y})");
            }
        }
    }
    let f = PrimeField::new(bn128());
    let vals = bn128_test_values(&f);
    for a in &vals {
        for b in &vals {
            let expected = f.add(a, b);
            let actual = f.add_owned(a.clone(), b.clone());
            assert_eq!(actual, expected);
        }
    }
}

#[test]
fn prop_sub_owned_matches_sub_small_primes() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let expected = f.sub(&a, &b);
                let actual = f.sub_owned(a, b);
                assert_eq!(actual, expected, "GF({p}) sub_owned({x},{y})");
            }
        }
    }
    let f = PrimeField::new(bn128());
    let vals = bn128_test_values(&f);
    for a in &vals {
        for b in &vals {
            let expected = f.sub(a, b);
            let actual = f.sub_owned(a.clone(), b.clone());
            assert_eq!(actual, expected);
        }
    }
}

#[test]
fn prop_neg_owned_matches_neg_small_primes() {
    // neg_owned consumes; must equal neg(&).
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let a = f.from_u64(x);
            let expected = f.neg(&a);
            let actual = f.neg_owned(a);
            assert_eq!(actual, expected, "GF({p}) neg_owned({x})");
        }
    }
    let f = PrimeField::new(bn128());
    for a in bn128_test_values(&f) {
        let expected = f.neg(&a);
        let actual = f.neg_owned(a.clone());
        assert_eq!(actual, expected);
    }
}

#[test]
fn prop_add_assign_owned_matches_add_small_primes() {
    // add_assign_owned forwards to add_assign — same semantic.
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                let expected = f.add(&a, &b);
                let mut a_mut = a.clone();
                f.add_assign_owned(&mut a_mut, b);
                assert_eq!(a_mut, expected, "GF({p}) add_assign_owned({x},{y})");
            }
        }
    }
}

// ──────────────────────────── feanor-style aliases ─────────────────────

#[test]
fn prop_feanor_aliases_forward() {
    // The feanor-named methods are pure forwards to the canonical ones.
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            for y in 0..p {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                assert_eq!(f.eq_el(&a, &b), a == b, "eq_el forwards");
                assert_eq!(f.add_ref(&a, &b), f.add(&a, &b));
                assert_eq!(f.sub_ref(&a, &b), f.sub(&a, &b));
                assert_eq!(f.mul_ref(&a, &b), f.mul(&a, &b));
                // by-value negate
                assert_eq!(f.negate(a.clone()), f.neg(&a));
                // clone_el
                let c = f.clone_el(&a);
                assert_eq!(c, a);
            }
        }
    }
}

#[test]
fn prop_from_int_matches_from_i64() {
    // from_int(n) is alias for from_i64(n).
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let pi = p as i64;
        for v in -(2 * pi)..(2 * pi) {
            assert_eq!(f.from_int(v), f.from_i64(v));
        }
    }
}

#[test]
fn prop_int_hom_maps_match_from_i64() {
    // int_hom().map(n) == from_i64(n).
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let hom = f.int_hom();
        for v in -10i64..10 {
            assert_eq!(hom.map(v), f.from_i64(v));
        }
    }
}

// ──────────────────────────── PrimeField PartialEq ─────────────────────

#[test]
fn prop_primefield_eq_by_prime() {
    // Two PrimeFields are equal iff they have the same prime
    // (independent of Arc identity).
    let f1 = PrimeField::new(BigUint::from(7u32));
    let f2 = PrimeField::new(BigUint::from(7u32));
    let f3 = PrimeField::new(BigUint::from(11u32));
    assert!(f1 == f2, "same prime => fields equal");
    assert!(!(f1 == f3), "different prime => fields unequal");
    // Cloning preserves Arc identity → fast path.
    let f1c = f1.clone();
    assert!(f1 == f1c);
}

// ──────────────────────────── characteristic == prime ──────────────────

#[test]
fn prop_characteristic_equals_prime() {
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        assert_eq!(f.characteristic(), f.prime());
        assert_eq!(*f.characteristic(), BigUint::from(p));
    }
}

// ──────────────────────────── is_zero / is_one semantics ───────────────

#[test]
fn prop_is_zero_is_one_consistent() {
    // Definitions: is_zero(zero())=true, is_one(one())=true,
    // is_zero(one())=false unless p==1 (impossible by assert);
    // is_one(zero())=false.
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        assert!(f.is_zero(&f.zero()));
        assert!(f.is_one(&f.one()));
        assert!(!f.is_one(&f.zero()));
        assert!(!f.is_zero(&f.one()));
        // for_u64(0) is zero, for_u64(1) is one.
        assert!(f.is_zero(&f.from_u64(0)));
        assert!(f.is_one(&f.from_u64(1)));
        assert!(f.is_zero(&f.from_u64(p)), "p mod p == 0");
    }
}

// ──────────────────────────── construction guards ─────────────────────

#[test]
#[should_panic(expected = "prime must be > 1")]
fn prop_new_panics_on_prime_one() {
    let _ = PrimeField::new(BigUint::from(1u32));
}

#[test]
#[should_panic(expected = "prime must be > 1")]
fn prop_new_panics_on_prime_zero() {
    let _ = PrimeField::new(BigUint::from(0u32));
}

// ──────────────────────────── Hash + Eq consistency ────────────────────

#[test]
fn prop_fieldelem_hash_eq_consistency_small() {
    // Equal field elements must hash equally.
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let a = f.from_u64(x);
            let b = f.from_u64(x);
            assert_eq!(a, b);
            let mut ha = DefaultHasher::new();
            let mut hb = DefaultHasher::new();
            a.hash(&mut ha);
            b.hash(&mut hb);
            assert_eq!(ha.finish(), hb.finish(), "Eq => Hash GF({p}) {x}");
        }
    }
}

// ──────────────────────────── pow with BigUint exponent ────────────────

#[test]
fn prop_pow_zero_exponent_is_one_even_for_zero_base() {
    // Convention: a^0 == 1 for ALL a, including a == 0.
    // Docstring on prop_pow_exponent_identities confirms this.
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let zero_exp = BigUint::from(0u32);
        assert!(f.is_one(&f.pow(&f.zero(), &zero_exp)));
        assert!(f.is_one(&f.pow(&f.one(), &zero_exp)));
        assert!(f.is_one(&f.pow_u64(&f.zero(), 0)));
    }
}

#[test]
fn prop_pow_biguint_matches_pow_u64() {
    // pow(a, BigUint::from(e)) == pow_u64(a, e) for small e.
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let a = f.from_u64(x);
            for e in 0u64..7 {
                let by_bu = f.pow(&a, &BigUint::from(e));
                let by_u64 = f.pow_u64(&a, e);
                assert_eq!(by_bu, by_u64, "GF({p}) pow({x},{e}) variant mismatch");
            }
        }
    }
}

// ──────────────────────────── Repeated assigns preserve invariants ─────

#[test]
fn prop_chained_assigns_preserve_canonical_form() {
    // Many chained add_assigns must stay in [0, p).
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        let mut acc = f.zero();
        for v in 0..(3 * p) {
            f.add_assign(&mut acc, &f.from_u64(v));
            // canonical-form invariant must hold after each op.
            assert!(f.to_biguint(&acc) < BigUint::from(p));
        }
        // Multiplication chain
        let mut acc = f.one();
        for v in 1..(2 * p) {
            f.mul_assign(&mut acc, &f.from_u64(v % p));
            assert!(f.to_biguint(&acc) < BigUint::from(p));
        }
    }
}

// ──────────────────────────── div(0/0) returns None ────────────────────

#[test]
fn prop_div_by_zero_returns_none() {
    // Division by zero must return None (per `inv(zero) = None`).
    for &p in &small_primes() {
        let f = PrimeField::new(BigUint::from(p));
        for x in 0..p {
            let a = f.from_u64(x);
            assert!(f.div(&a, &f.zero()).is_none(), "GF({p}) {x}/0 must be None");
        }
    }
}

// ──────────────────────────── Zech-log small-prime backend ───────────────

/// Deterministic LCG (no `rand` dependency; reproducible across runs).
fn lcg(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state >> 16
}

#[test]
fn primitive_root_is_a_generator() {
    // The smallest primitive root must have full multiplicative order p-1:
    // g^k != 1 for 0 < k < p-1, and g^(p-1) == 1.
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 101, 251, 65521] {
        let g = primitive_root(p);
        if p == 2 {
            assert_eq!(g, 1);
            continue;
        }
        let mut seen = std::collections::HashSet::new();
        let mut cur = 1u64;
        for _ in 0..(p - 1) {
            assert!(seen.insert(cur), "GF({p}): g={g} repeats before order p-1");
            cur = small_mul(cur, g, p);
        }
        assert_eq!(cur, 1, "GF({p}): g={g} must return to 1 after p-1 steps");
    }
}

#[test]
fn zech_tables_match_direct_small_primes_exhaustively() {
    // For tiny primes, every mul / inv / pow pair must agree with the direct
    // `small_*` arithmetic.
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 101, 251] {
        let t = ZechTables::build(p);
        for a in 0..p {
            for b in 0..p {
                assert_eq!(t.mul(a, b), small_mul(a, b, p), "GF({p}): {a}*{b}");
            }
            assert_eq!(t.inv(a), small_inv(a, p), "GF({p}): inv({a})");
            for e in 0..p {
                assert_eq!(t.pow(a, e), small_pow(a, e, p), "GF({p}): {a}^{e}");
            }
        }
    }
}

#[test]
fn zech_tables_match_direct_large_prime_random() {
    // GF(65521): too large for the exhaustive sweep — sample randomly.
    let p = 65521u64;
    let t = ZechTables::build(p);
    let mut s = 0x1234_5678u64;
    for _ in 0..200_000 {
        let a = lcg(&mut s) % p;
        let b = lcg(&mut s) % p;
        assert_eq!(t.mul(a, b), small_mul(a, b, p), "{a}*{b}");
        assert_eq!(t.inv(a), small_inv(a, p), "inv({a})");
        let e = lcg(&mut s); // full u64 exponent — exercises the mod (p-1) reduction
        assert_eq!(t.pow(a, e), small_pow(a, e, p), "{a}^{e}");
    }
}

#[test]
fn zech_field_matches_direct_field() {
    // The `zech_log_small_fp` flag must be result-identical to the direct
    // backend across mul / inv / div / pow on the field API.
    for &p in &[7u64, 101, 251, 65521] {
        let direct = {
            let _g = crate::config::ConfigGuard::with_override(|c| c.zech_log_small_fp = false);
            PrimeField::new(BigUint::from(p))
        };
        let zech = {
            let _g = crate::config::ConfigGuard::with_override(|c| c.zech_log_small_fp = true);
            PrimeField::new(BigUint::from(p))
        };
        let mut s = 0xC0FFEEu64;
        for _ in 0..20_000 {
            let a = direct.from_u64(lcg(&mut s) % p);
            let b = direct.from_u64(lcg(&mut s) % p);
            assert_eq!(direct.mul(&a, &b), zech.mul(&a, &b), "GF({p}) mul");
            assert_eq!(direct.inv(&a), zech.inv(&a), "GF({p}) inv");
            assert_eq!(direct.div(&a, &b), zech.div(&a, &b), "GF({p}) div");
            let e = BigUint::from(lcg(&mut s));
            assert_eq!(direct.pow(&a, &e), zech.pow(&a, &e), "GF({p}) pow");
        }
    }
}

#[test]
fn zech_log_off_by_default_keeps_direct_backend() {
    // Default config (flag off): a small prime must not build the tables.
    let f = PrimeField::new(BigUint::from(101u64));
    // Indirect check: arithmetic is still correct (the selection itself is
    // private; the flag-on path is covered by `zech_field_matches_direct_field`).
    let a = f.from_u64(7);
    let b = f.from_u64(9);
    assert_eq!(f.mul(&a, &b), f.from_u64(63));
}
