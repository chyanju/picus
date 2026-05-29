//! 128-bit DivMask for fast monomial divisibility rejection.
//!
//! A DivMask maps a monomial's exponent vector to a 128-bit bitmask
//! where each bit indicates whether the corresponding exponent meets a
//! precomputed threshold. Divisibility `a | b` requires
//! `mask(a) & mask(b) == mask(a)`, so any bit set in `mask(a)` but not
//! in `mask(b)` immediately rules out divisibility without touching the
//! exponent vector. At 128 bits per mask, the filter covers up to 128
//! distinct variables before bucketing reduces resolution.

use super::monomial::Monomial;

const DIVMASK_BITS: usize = 128;

/// 128-bit divisibility mask.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DivMask(pub u128);

impl DivMask {
    pub const fn empty() -> Self {
        DivMask(0)
    }

    /// Necessary condition for `a | b`: every bit set in `mask(a)` must be set in `mask(b)`.
    #[inline]
    pub fn divides_consistent_with(self, other: DivMask) -> bool {
        (self.0 & !other.0) == 0
    }
}

/// Per-variable thresholds for the DivMask encoding.
///
/// `thresholds.len() == actual_vars * bits_per_var` where
/// `actual_vars = min(n_vars * bits_per_var, 128) / bits_per_var`. Variables beyond
/// `actual_vars` get no DivMask bits. Bit `(v * bits_per_var + k)` is
/// set in a monomial's mask iff `monomial.exponent(v) > thresholds[v * bits_per_var + k]`.
#[derive(Clone, Debug)]
pub struct DivMaskScheme {
    pub n_vars: usize,
    pub bits_per_var: usize,
    pub thresholds: Vec<u16>, // length n_vars * bits_per_var
}

impl DivMaskScheme {
    /// Build a scheme for `n_vars` variables targeting up to `max_deg` per
    /// variable (used to space thresholds). `bits_per_var` is chosen so the
    /// total stays within 32 bits.
    pub fn build(n_vars: usize, max_deg_per_var: u16) -> Self {
        if n_vars == 0 {
            return DivMaskScheme { n_vars: 0, bits_per_var: 0, thresholds: Vec::new() };
        }
        let bits_per_var = (DIVMASK_BITS / n_vars).max(1);
        let n_used = (n_vars * bits_per_var).min(DIVMASK_BITS);
        // Generate thresholds for the first `n_used / bits_per_var` variables
        // (extra variables share the leftover bits — we cap at n_used).
        let actual_vars = n_used / bits_per_var;
        let mut thresholds = Vec::with_capacity(actual_vars * bits_per_var);
        let max = max_deg_per_var.max(1);
        for _v in 0..actual_vars {
            for k in 0..bits_per_var {
                // Threshold k = (k+1) * max / bits_per_var (floored); bit
                // (v, k) is set iff exponent(v) exceeds it.
                let t = ((k as u32 + 1) * max as u32 / bits_per_var as u32)
                    .min(u16::MAX as u32) as u16;
                thresholds.push(t);
            }
        }
        DivMaskScheme { n_vars, bits_per_var, thresholds }
    }

    pub fn compute(&self, mon: &Monomial) -> DivMask {
        self.compute_from_slice(mon.exponents())
    }

    #[inline]
    pub fn compute_from_slice(&self, exps: &[u16]) -> DivMask {
        let mut mask: u128 = 0;
        let actual_vars = self.thresholds.len() / self.bits_per_var.max(1);
        for v in 0..actual_vars {
            let exp = if v < exps.len() { exps[v] } else { 0 };
            for k in 0..self.bits_per_var {
                let t = self.thresholds[v * self.bits_per_var + k];
                if exp > t {
                    mask |= 1u128 << (v * self.bits_per_var + k);
                }
            }
        }
        DivMask(mask)
    }
}

#[cfg(test)]
#[path = "divmask_tests.rs"]
mod tests;
