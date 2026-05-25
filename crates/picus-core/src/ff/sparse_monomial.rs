//! Sparse monomial representation: only the nonzero `(var, exp)` pairs.
//!
//! Every operation is O(nnz) instead of the dense `Monomial`'s
//! O(n_vars), so a polynomial ring over thousands of variables stays
//! cheap (the dense per-monomial `n_vars`-wide exponent vector is
//! prohibitive there). Validated bit-for-bit against the dense
//! `Monomial` by `repr_oracle`.

use std::cmp::Ordering;

use super::monomial::MonomialOrder;
use super::repr::MonomialRepr;

/// `x_0^{e_0} ... x_{n-1}^{e_{n-1}}` as the sorted list of `(var, exp)`
/// pairs with `exp > 0`. Canonical (ascending `var`, no zero exponents),
/// so the derived `PartialEq`/`Eq`/`Hash` are sound.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SparseMonomial {
    n_vars: usize,
    vars: Vec<(u32, u16)>,
    total_deg: u32,
}

impl SparseMonomial {
    /// Presence-based 128-bit divisibility mask for fast rejection: for
    /// every variable `v` with nonzero exponent, set bit `h(v)` where `h`
    /// is a multiplicative hash into `0..128`. If a bit is set in `a`'s
    /// mask but not `b`'s, some variable of `a` is absent from `b`, so
    /// `a ∤ b` — checked via [`DivMask::divides_consistent_with`].
    ///
    /// Unlike the dense [`DivMaskScheme`](super::divmask::DivMaskScheme)
    /// (thresholds over the first 128 variables only — useless on the wide
    /// rings the sparse representation targets), this hashes *every*
    /// variable into the 128 bits; collisions only yield false positives,
    /// resolved by the full [`MonomialRepr::divides`] check. Exponent
    /// magnitude is not encoded — the `divides` total-degree guard and the
    /// full check cover that.
    #[inline]
    pub fn divmask(&self) -> super::divmask::DivMask {
        let mut m: u128 = 0;
        for &(v, _) in &self.vars {
            let h = (v as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 57;
            m |= 1u128 << (h & 127);
        }
        super::divmask::DivMask(m)
    }

    /// Lex: lowest variable where the exponents differ decides; higher
    /// exponent there is the larger monomial.
    #[inline]
    fn cmp_lex(&self, other: &Self) -> Ordering {
        let (mut i, mut j) = (0usize, 0usize);
        while i < self.vars.len() && j < other.vars.len() {
            let (va, ea) = self.vars[i];
            let (vb, eb) = other.vars[j];
            match va.cmp(&vb) {
                // self has exponent at the lower variable va, other has 0.
                Ordering::Less => return Ordering::Greater,
                Ordering::Greater => return Ordering::Less,
                Ordering::Equal => match ea.cmp(&eb) {
                    Ordering::Equal => {
                        i += 1;
                        j += 1;
                    }
                    o => return o,
                },
            }
        }
        // Whoever has a remaining (higher-index) variable is the larger.
        if i < self.vars.len() {
            Ordering::Greater
        } else if j < other.vars.len() {
            Ordering::Less
        } else {
            Ordering::Equal
        }
    }

    /// Reverse-lex tiebreak (used by DegRevLex at equal total degree):
    /// the highest variable where the exponents differ decides; the
    /// SMALLER exponent there is the larger monomial.
    #[inline]
    fn cmp_revlex(&self, other: &Self) -> Ordering {
        let mut i = self.vars.len();
        let mut j = other.vars.len();
        loop {
            let va = if i > 0 { Some(self.vars[i - 1]) } else { None };
            let vb = if j > 0 { Some(other.vars[j - 1]) } else { None };
            match (va, vb) {
                (None, None) => return Ordering::Equal,
                // self has a nonzero exponent at the highest differing var.
                (Some(_), None) => return Ordering::Less,
                (None, Some(_)) => return Ordering::Greater,
                (Some((va_, ea)), Some((vb_, eb))) => {
                    if va_ > vb_ {
                        return Ordering::Less;
                    } else if vb_ > va_ {
                        return Ordering::Greater;
                    } else {
                        match ea.cmp(&eb) {
                            Ordering::Equal => {
                                i -= 1;
                                j -= 1;
                            }
                            // smaller exponent at the highest differing var = larger
                            Ordering::Less => return Ordering::Greater,
                            Ordering::Greater => return Ordering::Less,
                        }
                    }
                }
            }
        }
    }
}

impl MonomialRepr for SparseMonomial {
    #[inline]
    fn one(n_vars: usize) -> Self {
        SparseMonomial { n_vars, vars: Vec::new(), total_deg: 0 }
    }

    #[inline]
    fn from_exponents(exps: Vec<u16>) -> Self {
        let n_vars = exps.len();
        let mut vars = Vec::new();
        let mut total = 0u32;
        for (i, &e) in exps.iter().enumerate() {
            if e > 0 {
                vars.push((i as u32, e));
                total += e as u32;
            }
        }
        SparseMonomial { n_vars, vars, total_deg: total }
    }

    #[inline]
    fn single_var(n_vars: usize, var: usize, exp: u16) -> Self {
        let (vars, total) = if exp > 0 {
            (vec![(var as u32, exp)], exp as u32)
        } else {
            (Vec::new(), 0)
        };
        SparseMonomial { n_vars, vars, total_deg: total }
    }

    #[inline]
    fn n_vars(&self) -> usize {
        self.n_vars
    }
    #[inline]
    fn total_degree(&self) -> u32 {
        self.total_deg
    }
    #[inline]
    fn is_one(&self) -> bool {
        self.vars.is_empty()
    }

    #[inline]
    fn exponent(&self, var: usize) -> u16 {
        let v = var as u32;
        match self.vars.binary_search_by_key(&v, |&(vv, _)| vv) {
            Ok(i) => self.vars[i].1,
            Err(_) => 0,
        }
    }

    #[inline]
    fn to_dense(&self) -> Vec<u16> {
        let mut d = vec![0u16; self.n_vars];
        for &(v, e) in &self.vars {
            d[v as usize] = e;
        }
        d
    }

    #[inline]
    fn for_each_nonzero(&self, mut f: impl FnMut(usize, u16)) {
        for &(v, e) in &self.vars {
            f(v as usize, e);
        }
    }

    #[inline]
    fn mul(&self, other: &Self) -> Self {
        let mut out = Vec::with_capacity(self.vars.len() + other.vars.len());
        let (mut i, mut j) = (0usize, 0usize);
        while i < self.vars.len() && j < other.vars.len() {
            let (va, ea) = self.vars[i];
            let (vb, eb) = other.vars[j];
            match va.cmp(&vb) {
                Ordering::Less => {
                    out.push((va, ea));
                    i += 1;
                }
                Ordering::Greater => {
                    out.push((vb, eb));
                    j += 1;
                }
                Ordering::Equal => {
                    let e = ea
                        .checked_add(eb)
                        .expect("exponent overflow: u16 too small for this monomial degree");
                    out.push((va, e));
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&self.vars[i..]);
        out.extend_from_slice(&other.vars[j..]);
        SparseMonomial {
            n_vars: self.n_vars,
            total_deg: self.total_deg + other.total_deg,
            vars: out,
        }
    }

    #[inline]
    fn mul_assign(&mut self, other: &Self) {
        *self = MonomialRepr::mul(self, other);
    }

    #[inline]
    fn divides(&self, other: &Self) -> bool {
        if self.total_deg > other.total_deg {
            return false;
        }
        let mut j = 0usize;
        for &(v, e) in &self.vars {
            while j < other.vars.len() && other.vars[j].0 < v {
                j += 1;
            }
            if j >= other.vars.len() || other.vars[j].0 != v || other.vars[j].1 < e {
                return false;
            }
        }
        true
    }

    #[inline]
    fn div(&self, divisor: &Self) -> Self {
        debug_assert!(MonomialRepr::divides(divisor, self));
        let mut out = Vec::with_capacity(self.vars.len());
        for &(v, e) in &self.vars {
            let d = divisor.exponent(v as usize);
            if e > d {
                out.push((v, e - d));
            }
        }
        SparseMonomial {
            n_vars: self.n_vars,
            total_deg: self.total_deg - divisor.total_deg,
            vars: out,
        }
    }

    #[inline]
    fn lcm(&self, other: &Self) -> Self {
        let mut out = Vec::with_capacity(self.vars.len() + other.vars.len());
        let (mut i, mut j) = (0usize, 0usize);
        while i < self.vars.len() && j < other.vars.len() {
            let (va, ea) = self.vars[i];
            let (vb, eb) = other.vars[j];
            match va.cmp(&vb) {
                Ordering::Less => {
                    out.push((va, ea));
                    i += 1;
                }
                Ordering::Greater => {
                    out.push((vb, eb));
                    j += 1;
                }
                Ordering::Equal => {
                    out.push((va, ea.max(eb)));
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&self.vars[i..]);
        out.extend_from_slice(&other.vars[j..]);
        let total = out.iter().map(|&(_, e)| e as u32).sum();
        SparseMonomial { n_vars: self.n_vars, total_deg: total, vars: out }
    }

    #[inline]
    fn gcd(&self, other: &Self) -> Self {
        let mut out = Vec::new();
        let (mut i, mut j) = (0usize, 0usize);
        while i < self.vars.len() && j < other.vars.len() {
            let (va, ea) = self.vars[i];
            let (vb, eb) = other.vars[j];
            match va.cmp(&vb) {
                Ordering::Less => i += 1,
                Ordering::Greater => j += 1,
                Ordering::Equal => {
                    out.push((va, ea.min(eb)));
                    i += 1;
                    j += 1;
                }
            }
        }
        let total = out.iter().map(|&(_, e)| e as u32).sum();
        SparseMonomial { n_vars: self.n_vars, total_deg: total, vars: out }
    }

    #[inline]
    fn is_coprime(&self, other: &Self) -> bool {
        let (mut i, mut j) = (0usize, 0usize);
        while i < self.vars.len() && j < other.vars.len() {
            match self.vars[i].0.cmp(&other.vars[j].0) {
                Ordering::Less => i += 1,
                Ordering::Greater => j += 1,
                Ordering::Equal => return false,
            }
        }
        true
    }

    #[inline]
    fn cmp_with_order(&self, other: &Self, order: MonomialOrder) -> Ordering {
        match order {
            MonomialOrder::Lex => self.cmp_lex(other),
            MonomialOrder::DegRevLex => match self.total_deg.cmp(&other.total_deg) {
                Ordering::Equal => self.cmp_revlex(other),
                o => o,
            },
        }
    }
}
