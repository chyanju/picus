//! Finite-field algebra over GF(p).
//!
//! GF(p) arithmetic with a dual backend (u64/u128 buffer for primes
//! `<= 2^64`, `rug::Integer` GMP for larger), dense and sparse
//! multivariate polynomials, divisibility masks, and geobucket reduction.
//! The Gröbner-basis and root-finding engines that operate on these types
//! live in `picus-solver`.

pub mod field;
pub mod monomial;
pub mod divmask;
pub mod polynomial;
pub mod geobucket;
pub mod linalg;
pub mod repr;
pub mod sparse_monomial;
pub mod sparse_polynomial;
pub mod sparse_geobucket;

/// Geobucket cascade tuning, shared by the dense [`geobucket`] and sparse
/// [`sparse_geobucket`] implementations so the two stay in lockstep.
pub(crate) mod geobucket_params {
    /// Smallest bucket capacity (in terms). A larger first bucket means
    /// fewer cascade events per accumulation call.
    pub(crate) const BASE_CAPACITY: usize = 128;
    /// Geometric growth factor between consecutive buckets.
    pub(crate) const RATIO: usize = 4;
    /// Hard cap on the number of buckets. `128 * 4^19 ≈ 10^13` terms.
    pub(crate) const MAX_BUCKETS: usize = 20;
}

pub use divmask::{DivMask, DivMaskScheme};
pub use field::{FieldElem, PrimeField};
pub use monomial::{Monomial, MonomialOrder};
pub use polynomial::{DensePoly, PolyRing, Polynomial, TermRef};
