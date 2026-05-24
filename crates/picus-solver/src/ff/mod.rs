//! Inlined finite-field algebra engine.
//!
//! Provides:
//! * `GF(p)` arithmetic with a dual backend: u64 + u128 buffer for
//!   primes `<= 2^64`, `rug::Integer` (GMP) for larger primes
//!   (BN128-size ~254 bits and above). Selected by [`field::PrimeField::new`]
//!   at ring construction.
//! * Multivariate polynomials over `GF(p)` (explicit exponent vectors).
//! * Buchberger's algorithm + F4-lite matrix path.
//! * Univariate root finding via Cantor-Zassenhaus.
//!
//! Designed to replace the dependency on `feanor-math` for the
//! picus-solver crate.

pub mod field;
pub mod monomial;
pub mod divmask;
pub mod polynomial;
pub mod geobucket;
pub mod spair;
pub mod buchberger;
pub mod f4;
pub mod hilbert;
pub mod univariate;
pub mod repr;
pub mod sparse_monomial;
pub mod sparse_polynomial;
pub mod sparse_geobucket;
pub mod sparse_gb;

#[cfg(test)]
mod repr_oracle;

pub use field::{PrimeField, FieldElem};
pub use monomial::{Monomial, MonomialOrder};
pub use divmask::{DivMask, DivMaskScheme};
pub use polynomial::{DensePoly, PolyRing, Polynomial, TermRef};
pub use spair::SPair;
pub use buchberger::{
    BuchbergerConfig, BuchbergerObserver, GBasis, IncrementalGB, NoObserver,
    groebner_basis, groebner_basis_observed, groebner_basis_incremental, interreduce,
};
pub use univariate::{UnivariatePoly, find_roots};
