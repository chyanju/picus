use super::*;

#[test]
fn field_inverse_of_zero_is_none() {
    assert_eq!(
        field_inverse(&BigUint::from(0u32), &BigUint::from(7u32)),
        None
    );
}

#[test]
fn field_inverse_of_one_short_circuits_regardless_of_prime() {
    // The `coeff == 1` short-circuit means the `prime <= 2` guard never fires.
    assert_eq!(
        field_inverse(&BigUint::from(1u32), &BigUint::from(2u32)),
        Some(BigUint::from(1u32))
    );
    assert_eq!(
        field_inverse(&BigUint::from(1u32), &BigUint::from(7u32)),
        Some(BigUint::from(1u32))
    );
}

#[test]
fn field_inverse_with_prime_le_2_is_none_for_non_unit() {
    // No invertible non-unit element in GF(p) for p <= 2.
    assert_eq!(
        field_inverse(&BigUint::from(3u32), &BigUint::from(2u32)),
        None
    );
}

#[test]
fn field_inverse_of_three_in_gf7_is_five() {
    // 3 · 5 = 15 ≡ 1 (mod 7).
    assert_eq!(
        field_inverse(&BigUint::from(3u32), &BigUint::from(7u32)),
        Some(BigUint::from(5u32))
    );
}

#[test]
fn field_inverse_round_trip_in_gf11() {
    let p = BigUint::from(11u32);
    for c in 1u32..11 {
        let inv = field_inverse(&BigUint::from(c), &p).expect("invertible");
        assert_eq!(
            (BigUint::from(c) * inv) % &p,
            BigUint::from(1u32),
            "c={} inverse should give 1 mod 11",
            c
        );
    }
}
