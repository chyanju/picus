//! Schreyer module signatures for the GVW signature-based Gröbner basis.
//!
//! A signature `(idx, monom)` denotes the module monomial `monom · e_idx`,
//! where `e_idx` is the unit vector of the `idx`-th original generator (the
//! Schreyer module index — keyed to the *original* generator, not the
//! basis position). Signatures are compared index-major, then by the ring's
//! monomial order; a J-pair carries the larger of its two parents'
//! propagated cofactor signatures. GVW (in `gvw`) processes J-pairs in
//! increasing signature order, reduces signature-safely, and skips a J-pair
//! a recorded syzygy or a rewrite/singular criterion proves redundant.

use crate::ff::monomial::{Monomial, MonomialOrder};
use std::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Signature {
    /// Original-generator (Schreyer module) index.
    pub idx: u32,
    /// Monomial multiplier on the unit vector `e_idx`.
    pub monom: Monomial,
}

impl Signature {
    /// Signature of the `idx`-th input generator: `1 · e_idx`.
    pub fn input(idx: u32, n_vars: usize) -> Self {
        Signature { idx, monom: Monomial::one(n_vars) }
    }

    /// Multiply the signature's monomial by `m` (the S-poly cofactor).
    pub fn mul(&self, m: &Monomial) -> Signature {
        Signature { idx: self.idx, monom: self.monom.mul(m) }
    }

    /// Compare under the ring order: index-major (a higher module index
    /// dominates), then the monomial order on the multiplier.
    pub fn cmp(&self, other: &Signature, order: MonomialOrder) -> Ordering {
        self.idx
            .cmp(&other.idx)
            .then_with(|| self.monom.cmp_with_order(&other.monom, order))
    }

    /// Whether `self` divides `other` in the module — same index and
    /// `self.monom` divides `other.monom`. Used to test whether `other` is
    /// a multiple of a recorded syzygy `self`.
    pub fn divides(&self, other: &Signature) -> bool {
        self.idx == other.idx && self.monom.divides(&other.monom)
    }
}

#[cfg(test)]
#[path = "signature_tests.rs"]
mod tests;
