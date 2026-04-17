pub mod grammar;
pub mod parser;
pub mod sym;
pub mod precondition;

/// The BN128 prime field used by Circom circuits.
/// p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
pub fn bn128_prime() -> num_bigint::BigUint {
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse()
        .unwrap()
}

/// Reduce a BigUint modulo the BN128 prime (field reduction).
pub fn field_reduce(x: &num_bigint::BigUint) -> num_bigint::BigUint {
    x % bn128_prime()
}
