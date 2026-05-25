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
pub mod repr;
pub mod sparse_monomial;
pub mod sparse_polynomial;
pub mod sparse_geobucket;

pub use divmask::{DivMask, DivMaskScheme};
pub use field::{FieldElem, PrimeField};
pub use monomial::{Monomial, MonomialOrder};
pub use polynomial::{DensePoly, PolyRing, Polynomial, TermRef};
