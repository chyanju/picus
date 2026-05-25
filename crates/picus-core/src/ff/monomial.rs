//! Monomials with explicit exponent vectors and monomial orderings.
//!
//! Unlike `feanor-math`'s compressed `(deg, order)` encoding, we store the
//! exponent vector explicitly. This trades a small amount of memory for
//! O(1) per-variable exponent access — the right tradeoff for Buchberger
//! where divisibility, LCM, and exponent extraction dominate.

use std::cmp::Ordering;

/// Monomial orderings supported by the inlined polynomial engine.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MonomialOrder {
    /// Degree-reverse lexicographic ordering.
    DegRevLex,
    /// Pure lexicographic ordering.
    Lex,
}

/// A monomial `x_0^{e_0} * x_1^{e_1} * ... * x_{n-1}^{e_{n-1}}`.
///
/// Exponents stored as a single boxed slice to avoid the `Vec` capacity field;
/// the total degree is cached because Buchberger checks it on every operation.
#[derive(Clone, Debug)]
pub struct Monomial {
    exponents: Box<[u16]>,
    total_deg: u32,
}

impl Monomial {
    /// Create a monomial of all-zero exponents (i.e. the constant 1).
    pub fn one(n_vars: usize) -> Self {
        Monomial { exponents: vec![0u16; n_vars].into_boxed_slice(), total_deg: 0 }
    }

    /// Create from a raw exponent vector; total degree is computed.
    pub fn from_exponents(exponents: Vec<u16>) -> Self {
        let total_deg: u32 = exponents.iter().map(|&e| e as u32).sum();
        Monomial { exponents: exponents.into_boxed_slice(), total_deg }
    }

    /// Single variable to the given power.
    pub fn single_var(n_vars: usize, var: usize, exp: u16) -> Self {
        let mut v = vec![0u16; n_vars];
        v[var] = exp;
        Monomial::from_exponents(v)
    }

    #[inline]
    pub fn n_vars(&self) -> usize {
        self.exponents.len()
    }

    #[inline]
    pub fn exponents(&self) -> &[u16] {
        &self.exponents
    }

    #[inline]
    pub fn exponent(&self, var: usize) -> u16 {
        self.exponents[var]
    }

    #[inline]
    pub fn total_degree(&self) -> u32 {
        self.total_deg
    }

    #[inline]
    pub fn is_one(&self) -> bool {
        self.total_deg == 0
    }

    /// Component-wise sum: `self * other`.
    pub fn mul(&self, other: &Monomial) -> Monomial {
        debug_assert_eq!(self.exponents.len(), other.exponents.len());
        let exps: Vec<u16> = self
            .exponents
            .iter()
            .zip(other.exponents.iter())
            .map(|(&a, &b)| a.checked_add(b)
                .expect("exponent overflow: u16 too small for this monomial degree"))
            .collect();
        Monomial {
            exponents: exps.into_boxed_slice(),
            total_deg: self.total_deg + other.total_deg,
        }
    }

    /// Multiply in place by `other`.
    pub fn mul_assign(&mut self, other: &Monomial) {
        debug_assert_eq!(self.exponents.len(), other.exponents.len());
        for (a, &b) in self.exponents.iter_mut().zip(other.exponents.iter()) {
            *a = a.checked_add(b)
                .expect("exponent overflow: u16 too small for this monomial degree");
        }
        self.total_deg += other.total_deg;
    }

    /// Returns true iff `self` divides `other` (i.e. `self_i <= other_i` for all i).
    pub fn divides(&self, other: &Monomial) -> bool {
        debug_assert_eq!(self.exponents.len(), other.exponents.len());
        if self.total_deg > other.total_deg {
            return false;
        }
        self.exponents.iter().zip(other.exponents.iter()).all(|(&a, &b)| a <= b)
    }

    /// Component-wise difference `other / self`. Caller must ensure divisibility.
    pub fn div(&self, divisor: &Monomial) -> Monomial {
        debug_assert!(divisor.divides(self));
        let exps: Vec<u16> = self
            .exponents
            .iter()
            .zip(divisor.exponents.iter())
            .map(|(&a, &b)| a - b)
            .collect();
        Monomial {
            exponents: exps.into_boxed_slice(),
            total_deg: self.total_deg - divisor.total_deg,
        }
    }

    /// Component-wise maximum: the LCM in monomial-land.
    pub fn lcm(&self, other: &Monomial) -> Monomial {
        debug_assert_eq!(self.exponents.len(), other.exponents.len());
        let exps: Vec<u16> = self
            .exponents
            .iter()
            .zip(other.exponents.iter())
            .map(|(&a, &b)| a.max(b))
            .collect();
        let total: u32 = exps.iter().map(|&e| e as u32).sum();
        Monomial { exponents: exps.into_boxed_slice(), total_deg: total }
    }

    /// Component-wise minimum: the GCD in monomial-land.
    pub fn gcd(&self, other: &Monomial) -> Monomial {
        debug_assert_eq!(self.exponents.len(), other.exponents.len());
        let exps: Vec<u16> = self
            .exponents
            .iter()
            .zip(other.exponents.iter())
            .map(|(&a, &b)| a.min(b))
            .collect();
        let total: u32 = exps.iter().map(|&e| e as u32).sum();
        Monomial { exponents: exps.into_boxed_slice(), total_deg: total }
    }

    /// Two monomials are coprime iff they share no variable in common.
    pub fn is_coprime(&self, other: &Monomial) -> bool {
        debug_assert_eq!(self.exponents.len(), other.exponents.len());
        self.exponents
            .iter()
            .zip(other.exponents.iter())
            .all(|(&a, &b)| a == 0 || b == 0)
    }

    /// Compare under the given ordering.
    pub fn cmp_with_order(&self, other: &Monomial, order: MonomialOrder) -> Ordering {
        match order {
            MonomialOrder::Lex => cmp_lex(&self.exponents, &other.exponents),
            MonomialOrder::DegRevLex => {
                match self.total_deg.cmp(&other.total_deg) {
                    Ordering::Equal => cmp_revlex(&self.exponents, &other.exponents),
                    o => o,
                }
            }
        }
    }
}

impl super::repr::MonomialRepr for Monomial {
    fn one(n_vars: usize) -> Self {
        Monomial::one(n_vars)
    }
    fn from_exponents(exps: Vec<u16>) -> Self {
        Monomial::from_exponents(exps)
    }
    fn single_var(n_vars: usize, var: usize, exp: u16) -> Self {
        Monomial::single_var(n_vars, var, exp)
    }
    fn n_vars(&self) -> usize {
        Monomial::n_vars(self)
    }
    fn total_degree(&self) -> u32 {
        Monomial::total_degree(self)
    }
    fn is_one(&self) -> bool {
        Monomial::is_one(self)
    }
    fn exponent(&self, var: usize) -> u16 {
        Monomial::exponent(self, var)
    }
    fn to_dense(&self) -> Vec<u16> {
        self.exponents().to_vec()
    }
    fn for_each_nonzero(&self, mut f: impl FnMut(usize, u16)) {
        for (i, &e) in self.exponents().iter().enumerate() {
            if e > 0 {
                f(i, e);
            }
        }
    }
    fn mul(&self, other: &Self) -> Self {
        Monomial::mul(self, other)
    }
    fn mul_assign(&mut self, other: &Self) {
        Monomial::mul_assign(self, other)
    }
    fn divides(&self, other: &Self) -> bool {
        Monomial::divides(self, other)
    }
    fn div(&self, divisor: &Self) -> Self {
        Monomial::div(self, divisor)
    }
    fn lcm(&self, other: &Self) -> Self {
        Monomial::lcm(self, other)
    }
    fn gcd(&self, other: &Self) -> Self {
        Monomial::gcd(self, other)
    }
    fn is_coprime(&self, other: &Self) -> bool {
        Monomial::is_coprime(self, other)
    }
    fn cmp_with_order(&self, other: &Self, order: MonomialOrder) -> Ordering {
        Monomial::cmp_with_order(self, other, order)
    }
}

impl PartialEq for Monomial {
    fn eq(&self, other: &Self) -> bool {
        self.total_deg == other.total_deg && self.exponents == other.exponents
    }
}
impl Eq for Monomial {}

impl std::hash::Hash for Monomial {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.exponents.hash(state);
    }
}

#[inline]
fn cmp_lex(a: &[u16], b: &[u16]) -> Ordering {
    debug_assert_eq!(a.len(), b.len());
    // Standard lex: compare from variable 0 upward; first differing exponent decides.
    for (x, y) in a.iter().zip(b.iter()) {
        match x.cmp(y) {
            Ordering::Equal => continue,
            o => return o,
        }
    }
    Ordering::Equal
}

#[inline]
fn cmp_revlex(a: &[u16], b: &[u16]) -> Ordering {
    debug_assert_eq!(a.len(), b.len());
    // Reverse lex tiebreaker for DegRevLex: scan from highest variable down;
    // the monomial with the SMALLER trailing exponent is the LARGER under degrevlex.
    for (x, y) in a.iter().rev().zip(b.iter().rev()) {
        match x.cmp(y) {
            Ordering::Equal => continue,
            // smaller right-most exponent => larger monomial
            Ordering::Less => return Ordering::Greater,
            Ordering::Greater => return Ordering::Less,
        }
    }
    Ordering::Equal
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mono(exps: &[u16]) -> Monomial {
        Monomial::from_exponents(exps.to_vec())
    }

    #[test]
    fn basic_ops() {
        let a = mono(&[2, 1, 0]);
        let b = mono(&[1, 2, 1]);
        assert_eq!(a.total_degree(), 3);
        assert_eq!(b.total_degree(), 4);
        let prod = a.mul(&b);
        assert_eq!(prod.exponents(), &[3, 3, 1]);
        assert_eq!(prod.total_degree(), 7);
        let lcm = a.lcm(&b);
        assert_eq!(lcm.exponents(), &[2, 2, 1]);
        let gcd = a.gcd(&b);
        assert_eq!(gcd.exponents(), &[1, 1, 0]);
    }

    #[test]
    fn divides_and_div() {
        let a = mono(&[1, 1, 0]);
        let b = mono(&[2, 1, 1]);
        assert!(a.divides(&b));
        assert!(!b.divides(&a));
        let q = b.div(&a);
        assert_eq!(q.exponents(), &[1, 0, 1]);
        assert_eq!(q.total_degree(), 2);
    }

    #[test]
    fn coprime() {
        assert!(mono(&[1, 0, 0]).is_coprime(&mono(&[0, 2, 1])));
        assert!(!mono(&[1, 1, 0]).is_coprime(&mono(&[0, 1, 0])));
    }

    #[test]
    fn lex_ordering() {
        // x_0^2 > x_0 x_1 (because of the first index)
        let a = mono(&[2, 0, 0]);
        let b = mono(&[1, 1, 0]);
        assert_eq!(a.cmp_with_order(&b, MonomialOrder::Lex), Ordering::Greater);
    }

    #[test]
    fn degrevlex_ordering() {
        // Same total degree (3): x0^2 x1 vs x1^2 x2.
        // In DegRevLex, x0^2 x1 > x1^2 x2 because the rightmost-nonzero
        // exponent in x1^2 x2 is x2 (var 2, exp 1) vs x1 (var 1, exp 1) —
        // i.e. x1^2 x2 has a nonzero exponent further to the right, so it ranks LOWER.
        let a = mono(&[2, 1, 0]);
        let b = mono(&[0, 2, 1]);
        assert_eq!(a.total_degree(), b.total_degree());
        assert_eq!(a.cmp_with_order(&b, MonomialOrder::DegRevLex), Ordering::Greater);

        // Different degrees: x0^3 vs x0 x1
        let c = mono(&[3, 0, 0]);
        let d = mono(&[1, 1, 0]);
        assert_eq!(c.cmp_with_order(&d, MonomialOrder::DegRevLex), Ordering::Greater);
    }
}
