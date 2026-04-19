pub mod grammar;
pub mod parser;
pub mod sym;

use num_bigint::BigUint;
use std::sync::LazyLock;

/// The BN128 prime field constant.
/// p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
static BN128_PRIME: LazyLock<BigUint> = LazyLock::new(|| {
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse()
        .unwrap()
});

/// Return a reference to the BN128 prime field constant.
#[must_use]
pub fn bn128_prime() -> &'static BigUint {
    &BN128_PRIME
}

/// Reduce a BigUint modulo the BN128 prime.
#[must_use]
pub fn field_reduce(x: &BigUint) -> BigUint {
    x % bn128_prime()
}

/// Parse a variable name like "x3" or "y12" into its numeric index.
/// Returns `None` if the name doesn't match the expected pattern.
#[must_use]
pub fn parse_var_index(name: &str) -> Option<usize> {
    let first = name.as_bytes().first()?;
    if (*first == b'x' || *first == b'y') && name.len() > 1 {
        name[1..].parse().ok()
    } else {
        None
    }
}
