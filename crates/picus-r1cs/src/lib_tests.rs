use super::*;

// ---- bn128_prime() ----

#[test]
fn prop_bn128_prime_matches_literal() {
    // The BN128 scalar-field prime is a well-known constant.
    let expected: BigUint =
        "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            .parse()
            .unwrap();
    assert_eq!(bn128_prime(), &expected);
}

#[test]
fn prop_bn128_prime_is_idempotent() {
    // Reference returned by LazyLock must be stable across calls.
    assert!(std::ptr::eq(bn128_prime(), bn128_prime()));
}

// ---- field_reduce() ----

#[test]
fn prop_field_reduce_small_primes() {
    for &p in &[2u32, 7, 101] {
        let prime = BigUint::from(p);
        // 0 mod p = 0
        assert_eq!(field_reduce(&BigUint::from(0u32), &prime), BigUint::from(0u32));
        // p mod p = 0
        assert_eq!(field_reduce(&prime, &prime), BigUint::from(0u32));
        // (p - 1) mod p = p - 1 (since p >= 2)
        let pm1 = &prime - 1u32;
        assert_eq!(field_reduce(&pm1, &prime), pm1.clone());
    }
}

#[test]
fn prop_field_reduce_idempotent() {
    // (x mod p) mod p = x mod p.
    let p = BigUint::from(7u32);
    let x = BigUint::from(123u32);
    let once = field_reduce(&x, &p);
    let twice = field_reduce(&once, &p);
    assert_eq!(once, twice);
}

#[test]
fn prop_field_reduce_bound() {
    // Result is strictly less than p for any non-trivial prime.
    let p = BigUint::from(7u32);
    for v in 0u32..50 {
        let r = field_reduce(&BigUint::from(v), &p);
        assert!(r < p);
    }
}

#[test]
fn prop_field_reduce_bn128_passthrough() {
    // BN128 prime divides itself; a value less than p stays itself.
    let p = bn128_prime();
    let small = BigUint::from(42u32);
    assert_eq!(&field_reduce(&small, p), &small);
}

// ---- parse_var_index() ----

#[test]
fn prop_parse_var_index_x_prefix() {
    assert_eq!(parse_var_index("x0"), Some(0));
    assert_eq!(parse_var_index("x3"), Some(3));
    assert_eq!(parse_var_index("x12"), Some(12));
}

#[test]
fn prop_parse_var_index_y_prefix() {
    assert_eq!(parse_var_index("y0"), Some(0));
    assert_eq!(parse_var_index("y42"), Some(42));
}

#[test]
fn prop_parse_var_index_no_digits_after_prefix() {
    // "x" or "y" alone has no digits — must return None.
    assert_eq!(parse_var_index("x"), None);
    assert_eq!(parse_var_index("y"), None);
}

#[test]
fn prop_parse_var_index_empty_returns_none() {
    assert_eq!(parse_var_index(""), None);
}

#[test]
fn prop_parse_var_index_wrong_prefix_returns_none() {
    // Any letter other than 'x' or 'y' is not a recognised variable name.
    assert_eq!(parse_var_index("z3"), None);
    assert_eq!(parse_var_index("a0"), None);
    assert_eq!(parse_var_index("X3"), None); // case-sensitive
    assert_eq!(parse_var_index("Y3"), None);
}

#[test]
fn prop_parse_var_index_non_numeric_suffix_returns_none() {
    // The suffix must parse as `usize`. Non-numeric tails → None,
    // not panic.
    assert_eq!(parse_var_index("xabc"), None);
    assert_eq!(parse_var_index("x3a"), None);
    assert_eq!(parse_var_index("x-1"), None);
}

#[test]
fn prop_parse_var_index_large_value() {
    // usize-sized numeric tail must parse correctly.
    assert_eq!(parse_var_index("x1000000"), Some(1_000_000));
}

#[test]
fn audit_parse_var_index_no_panic_on_unicode() {
    // Non-ASCII first byte must not be mistakenly treated as 'x'/'y'.
    // The first byte of multi-byte UTF-8 sequences has the high bit set
    // and can't be 'x' (0x78) or 'y' (0x79), so the function should
    // return None without panicking.
    assert_eq!(parse_var_index("αβ"), None);
    assert_eq!(parse_var_index("中"), None);
}
