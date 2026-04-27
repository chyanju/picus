pub mod linear;
pub mod binary01;
pub mod basis2;
pub mod aboz;
pub mod bim;

pub use binary01::RangeValue;

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::bn128_prime;

/// Resolve named constants introduced by the SubP optimizer.
/// Shared by binary01 and basis2 lemmas.
///
/// NOTE: hardcoded to BN128 prime. If Picus is extended to other curves
/// (BLS12-381, Goldilocks, etc.), this must accept the prime as a parameter.
pub fn resolve_named_constant(name: &str) -> Option<BigUint> {
    let p = bn128_prime();
    match name {
        "p" => Some(p.clone()),
        "ps1" => Some(p - BigUint::one()),
        "ps2" => Some(p - BigUint::from(2u32)),
        "ps3" => Some(p - BigUint::from(3u32)),
        "ps4" => Some(p - BigUint::from(4u32)),
        "ps5" => Some(p - BigUint::from(5u32)),
        "zero" => Some(BigUint::zero()),
        "one" => Some(BigUint::one()),
        _ => None,
    }
}
