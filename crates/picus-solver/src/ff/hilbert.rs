//! Hilbert numerator for monomial ideals.
//!
//! For a monomial ideal `I = (m_1, …, m_s)` in `S = k[x_1, …, x_n]`,
//! the Hilbert series of `S/I` factors as
//!
//! ```text
//!     HS(S/I; t) = N(t) / (1 - t)^n
//! ```
//!
//! where `N(t) ∈ Z[t]` is the **Hilbert numerator**. The recursion
//! used here (Bigatti–Caboara–Robbiano) follows from the exact
//! sequence
//!
//! ```text
//!     0 → S/(I:p)  --·p-->  S/I  →  S/(I + (p))  → 0
//! ```
//!
//! and gives
//!
//! ```text
//!     N(I) = N(I + (p)) + t^deg(p) · N(I : p).
//! ```
//!
//! [`hilbert_numerator`] picks `p = x_k^e` where `k` maximises the
//! number of minimal generators containing `x_k` and `e` is the
//! smallest nonzero `x_k`-exponent across those generators; both
//! subproblems are strictly smaller, ensuring termination.
//!
//! [`quotient_dimension`] reads the `k`-vector-space dimension of
//! `S/I` (= the number of standard monomials = the solution count of a
//! zero-dimensional ideal with multiplicity over the algebraic
//! closure) off the leading monomials of a *finished* Gröbner basis,
//! via the graded Hilbert function [`HilbertNum::hf_at`]. This is a
//! sound, verdict-neutral oracle — pure combinatorics on exponent
//! vectors — used by [`crate::gb::ideal::Ideal::quotient_dimension`]
//! and as an FGLM staircase cross-check.

use super::monomial::Monomial;

/// Sparse univariate polynomial in `Z[t]` indexed by degree:
/// `coeffs[d]` is the coefficient of `t^d`. Trailing zeros are
/// trimmed by [`HilbertNum::trim`] after every mutating operation so
/// `degree` and equality match the mathematical polynomial.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HilbertNum {
    coeffs: Vec<i64>,
}

impl HilbertNum {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// The constant polynomial `1`.
    pub fn one() -> Self {
        Self { coeffs: vec![1] }
    }

    /// The polynomial `1 - t^d`. `d = 0` collapses to `0` (since
    /// `1 - t^0 = 0`); the rest are the building blocks of the
    /// coprime-product path in [`hilbert_numerator`].
    pub fn one_minus_t_pow(d: u32) -> Self {
        if d == 0 {
            return Self::zero();
        }
        let mut coeffs = vec![0i64; d as usize + 1];
        coeffs[0] = 1;
        coeffs[d as usize] = -1;
        Self { coeffs }
    }

    pub fn is_zero(&self) -> bool {
        self.coeffs.iter().all(|&c| c == 0)
    }

    /// Degree of the leading nonzero coefficient; `None` for the zero
    /// polynomial.
    pub fn degree(&self) -> Option<u32> {
        self.coeffs
            .iter()
            .rposition(|&c| c != 0)
            .map(|d| d as u32)
    }

    /// Coefficient of `t^d`. Returns `0` for any `d` past the trailing
    /// nonzero term.
    pub fn coeff(&self, d: u32) -> i64 {
        self.coeffs.get(d as usize).copied().unwrap_or(0)
    }

    /// Add `other` into `self` in place. Per-coefficient
    /// `i64::saturating_add` clamps to `i64::{MIN, MAX}` on overflow.
    pub fn add_assign(&mut self, other: &Self) {
        if other.coeffs.len() > self.coeffs.len() {
            self.coeffs.resize(other.coeffs.len(), 0);
        }
        for (i, &c) in other.coeffs.iter().enumerate() {
            self.coeffs[i] = self.coeffs[i].saturating_add(c);
        }
        self.trim();
    }

    /// Subtract `other` from `self` in place. Per-coefficient
    /// `i64::saturating_sub`.
    pub fn sub_assign(&mut self, other: &Self) {
        if other.coeffs.len() > self.coeffs.len() {
            self.coeffs.resize(other.coeffs.len(), 0);
        }
        for (i, &c) in other.coeffs.iter().enumerate() {
            self.coeffs[i] = self.coeffs[i].saturating_sub(c);
        }
        self.trim();
    }

    /// Multiply in place by `t^d` (shift coefficients up by `d`).
    pub fn mul_t_pow_assign(&mut self, d: u32) {
        if d == 0 || self.is_zero() {
            return;
        }
        let d = d as usize;
        let mut new_coeffs = vec![0i64; self.coeffs.len() + d];
        for (i, &c) in self.coeffs.iter().enumerate() {
            new_coeffs[i + d] = c;
        }
        self.coeffs = new_coeffs;
    }

    /// Polynomial multiplication: returns `self * other`. Per-pair
    /// `i64::saturating_mul` followed by per-cell
    /// `i64::saturating_add`.
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let n = self.coeffs.len() + other.coeffs.len() - 1;
        let mut coeffs = vec![0i64; n];
        for (i, &a) in self.coeffs.iter().enumerate() {
            if a == 0 {
                continue;
            }
            for (j, &b) in other.coeffs.iter().enumerate() {
                let prod = a.saturating_mul(b);
                coeffs[i + j] = coeffs[i + j].saturating_add(prod);
            }
        }
        let mut result = Self { coeffs };
        result.trim();
        result
    }

    /// Slice view of the coefficient vector after trimming. Exposed for
    /// tests and diagnostic comparisons.
    pub fn coeffs(&self) -> &[i64] {
        &self.coeffs
    }

    /// Value of the graded Hilbert function `HF(S/I)(d)` in `n_vars`
    /// variables, where `self = N(t)` is the Hilbert numerator: the
    /// coefficient of `t^d` in `N(t) / (1 - t)^{n_vars}`, i.e.
    /// `HF(d) = Σ_k N_k · C(d − k + n_vars − 1, n_vars − 1)`
    /// (using `1/(1−t)^n = Σ_m C(m+n−1, n−1) t^m`). `i128` saturating
    /// arithmetic; `n_vars == 0` gives `S = k`, so `HF(d) = N_d`.
    ///
    /// For a genuine monomial ideal this is a non-negative integer; the
    /// saturating arithmetic only guards a pathological (overflowing)
    /// input from panicking.
    pub fn hf_at(&self, d: u32, n_vars: usize) -> i128 {
        if n_vars == 0 {
            return self.coeff(d) as i128;
        }
        let r = (n_vars - 1) as u64;
        let dmax = self.degree().unwrap_or(0).min(d);
        let mut sum: i128 = 0;
        for k in 0..=dmax {
            let nk = self.coeff(k) as i128;
            if nk == 0 {
                continue;
            }
            // C((d-k) + r, r) = C((d-k)+r, d-k): choose the smaller index.
            let binom = binom_sat((d - k) as u64 + r, r);
            sum = sum.saturating_add(nk.saturating_mul(binom));
        }
        sum
    }

    fn trim(&mut self) {
        while let Some(&c) = self.coeffs.last() {
            if c == 0 {
                self.coeffs.pop();
            } else {
                break;
            }
        }
    }
}

/// Compute the Hilbert numerator of the monomial ideal generated by
/// `gens`.
///
/// Returns `1` when `gens` is empty (the zero ideal, so `S/I = S`),
/// and `0` if any generator is the unit monomial (the ideal is the
/// whole ring, so `S/I = 0`). Otherwise removes redundant generators
/// (the minimal monomial generating set is unique) and recurses on
/// `N(I) = N(I + (p)) + t^deg(p) * N(I : p)` for `p = x_k^e`, with
/// `k` chosen as the variable appearing in the most minimal
/// generators and `e` as the smallest nonzero `x_k`-exponent across
/// the minimal generators (which guarantees both subproblems shrink).
pub fn hilbert_numerator(gens: &[Monomial]) -> HilbertNum {
    if gens.is_empty() {
        return HilbertNum::one();
    }
    if gens.iter().any(|m| m.is_one()) {
        return HilbertNum::zero();
    }

    // Minimal generating set: a monomial `m_j` is redundant iff some
    // other `m_i` divides it. Build the minimal set in one O(s^2) pass
    // by sweeping generators and dropping each one already dominated
    // (or any earlier-kept one dominated by the newcomer).
    let mut minimal: Vec<Monomial> = Vec::new();
    'outer: for m in gens.iter() {
        for k in &minimal {
            if k.divides(m) {
                continue 'outer;
            }
        }
        minimal.retain(|k| !m.divides(k));
        minimal.push(m.clone());
    }

    if minimal.len() == 1 {
        return HilbertNum::one_minus_t_pow(minimal[0].total_degree());
    }

    // Pairwise-coprime shortcut: `N(I) = ∏ (1 - t^deg(m_i))`. This is
    // the only case where the numerator has the "regular sequence"
    // shape; everything else needs the recursive splitting below.
    let coprime = (0..minimal.len()).all(|i| {
        ((i + 1)..minimal.len()).all(|j| minimal[i].is_coprime(&minimal[j]))
    });
    if coprime {
        let mut result = HilbertNum::one();
        for g in &minimal {
            result = result.mul(&HilbertNum::one_minus_t_pow(g.total_degree()));
        }
        return result;
    }

    // Choose pivot: variable `k` appearing in the most minimal
    // generators (ties: smallest index), exponent `e` = the minimum
    // nonzero exponent of `x_k` across the minimal generators.
    let n_vars = minimal[0].n_vars();
    let mut occurrence = vec![0usize; n_vars];
    for m in &minimal {
        for (v, &e) in m.exponents().iter().enumerate() {
            if e > 0 {
                occurrence[v] += 1;
            }
        }
    }
    let (pivot_var, _) = occurrence
        .iter()
        .enumerate()
        .max_by_key(|&(_, &c)| c)
        .expect("at least one variable present (non-coprime branch)");
    let pivot_exp = minimal
        .iter()
        .map(|m| m.exponent(pivot_var))
        .filter(|&e| e > 0)
        .min()
        .expect("at least one gen has x_{pivot_var} > 0");

    let pivot = Monomial::single_var(n_vars, pivot_var, pivot_exp);
    let pivot_deg = pivot.total_degree();

    // I + (pivot): drop minimal gens divisible by pivot (newly
    // redundant), then add pivot itself.
    let mut i_plus: Vec<Monomial> = minimal
        .iter()
        .filter(|m| !pivot.divides(m))
        .cloned()
        .collect();
    i_plus.push(pivot.clone());

    // I : pivot = (m_i / gcd(m_i, pivot) : i). For gens not involving
    // `pivot_var` this leaves them unchanged; for gens with
    // `x_pivot_var^e_i`, the resulting exponent is `e_i - min(e_i, pivot_exp)`.
    let i_quot: Vec<Monomial> = minimal
        .iter()
        .map(|m| {
            let g = m.gcd(&pivot);
            m.div(&g)
        })
        .collect();

    let mut result = hilbert_numerator(&i_plus);
    let mut t_quot = hilbert_numerator(&i_quot);
    t_quot.mul_t_pow_assign(pivot_deg);
    result.add_assign(&t_quot);
    result
}

/// Binomial coefficient `C(m, r)` as `i128`, saturating on overflow.
/// Iterates over `min(r, m − r)` terms via the integer recurrence
/// `C(m, i+1) = C(m, i) · (m − i) / (i + 1)` (each partial product is a
/// binomial, so the division is exact). Picking the smaller index keeps
/// the loop short even when `m ≈ n_vars` is large.
fn binom_sat(m: u64, r: u64) -> i128 {
    if r > m {
        return 0;
    }
    let r = r.min(m - r);
    let mut res: i128 = 1;
    for i in 0..r {
        res = res.saturating_mul((m - i) as i128) / ((i + 1) as i128);
    }
    res
}

/// Socle-degree bound past which [`quotient_dimension`] declines
/// (returns `None`) instead of summing the Hilbert function term by
/// term. Reduced-GB leading terms of real circuit ideals carry small
/// pure powers (bit constraints give `x^2`), so this is never reached in
/// practice; it bounds a pathological input (e.g. a large explicit
/// field equation) to a quick, sound `None`.
const QUOT_DIM_DEGREE_CAP: u32 = 1 << 16;

/// `dim_k(S/I)` for the monomial ideal generated by `gens` — the number
/// of standard monomials, i.e. the `k`-vector-space dimension of `S/I`.
/// For `gens = LT(J)` (the leading monomials of a Gröbner basis of `J`)
/// this equals `dim_k(R/J)`, the number of solutions of `J` with
/// multiplicity over the algebraic closure (Macaulay: the standard
/// monomials are a `k`-basis of `R/J`).
///
/// Returns `None` when `S/I` is **not** finite-dimensional — some
/// variable lacks a pure power in `gens`, so the ideal is positive-
/// dimensional — or when the socle-degree bound exceeds
/// [`QUOT_DIM_DEGREE_CAP`] (declined; never returns a wrong value).
///
/// Sound and verdict-neutral by construction: pure combinatorics on the
/// exponent vectors of an already-computed basis, no field arithmetic.
pub fn quotient_dimension(gens: &[Monomial], n_vars: usize) -> Option<u128> {
    // Unit ideal `I = (1)`: `S/I = 0`.
    if gens.iter().any(|m| m.is_one()) {
        return Some(0);
    }
    // `S = k` with `I = 0` (no unit generator above): `dim_k k = 1`.
    if n_vars == 0 {
        return Some(1);
    }
    // Zero-dimensionality test and socle-degree bound: each variable
    // needs a pure power `x_v^{a_v}` among the generators. `a_v` is the
    // minimal such exponent; every standard monomial has `x_v`-degree
    // `< a_v`, so the top standard-monomial degree is at most
    // `Σ (a_v − 1)`. (Matches `Ideal::is_zero_dim`'s pure-power test.)
    let mut pure: Vec<Option<u32>> = vec![None; n_vars];
    for m in gens {
        let exps = m.exponents();
        let mut nz: Option<usize> = None;
        let mut multi = false;
        for v in 0..n_vars {
            if exps[v] > 0 {
                if nz.is_some() {
                    multi = true;
                    break;
                }
                nz = Some(v);
            }
        }
        if !multi {
            if let Some(v) = nz {
                let e = exps[v] as u32;
                pure[v] = Some(pure[v].map_or(e, |c| c.min(e)));
            }
        }
    }
    let mut d_max: u64 = 0;
    for slot in &pure {
        match slot {
            Some(a) => d_max += a.saturating_sub(1) as u64,
            None => return None, // positive-dimensional
        }
    }
    if d_max > QUOT_DIM_DEGREE_CAP as u64 {
        return None; // declined: pathologically large, never wrong
    }

    let num = hilbert_numerator(gens);
    let mut dim: u128 = 0;
    for d in 0..=(d_max as u32) {
        let hf = num.hf_at(d, n_vars);
        if hf <= 0 {
            break; // Artinian: HF(d)=0 ⇒ HF(e)=0 for all e ≥ d
        }
        dim = dim.saturating_add(hf as u128);
    }
    Some(dim)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x(n_vars: usize, var: usize, exp: u16) -> Monomial {
        Monomial::single_var(n_vars, var, exp)
    }

    fn from_exps(e: Vec<u16>) -> Monomial {
        Monomial::from_exponents(e)
    }

    #[test]
    fn hn_empty_ideal_is_one() {
        let hn = hilbert_numerator(&[]);
        assert_eq!(hn, HilbertNum::one());
    }

    #[test]
    fn hn_unit_ideal_is_zero() {
        let unit = Monomial::one(3);
        let hn = hilbert_numerator(&[unit]);
        assert_eq!(hn, HilbertNum::zero());
    }

    #[test]
    fn hn_single_variable() {
        // I = (x) in k[x, y] → N = 1 - t
        let hn = hilbert_numerator(&[x(2, 0, 1)]);
        assert_eq!(hn.coeffs(), &[1, -1]);
    }

    #[test]
    fn hn_single_higher_power() {
        // I = (x^3) in k[x] → N = 1 - t^3
        let hn = hilbert_numerator(&[x(1, 0, 3)]);
        assert_eq!(hn.coeffs(), &[1, 0, 0, -1]);
    }

    #[test]
    fn hn_two_coprime_vars() {
        // I = (x, y) coprime → N = (1-t)^2 = 1 - 2t + t^2
        let hn = hilbert_numerator(&[x(2, 0, 1), x(2, 1, 1)]);
        assert_eq!(hn.coeffs(), &[1, -2, 1]);
    }

    #[test]
    fn hn_three_coprime_vars() {
        // I = (x, y, z) → N = (1-t)^3 = 1 - 3t + 3t^2 - t^3
        let hn = hilbert_numerator(&[x(3, 0, 1), x(3, 1, 1), x(3, 2, 1)]);
        assert_eq!(hn.coeffs(), &[1, -3, 3, -1]);
    }

    #[test]
    fn hn_xx_xy_known_textbook_case() {
        // I = (x^2, x*y) in k[x, y].
        // Std monomials: {1, x, y, y^2, y^3, …}.
        // HS = 1 + 2t + t^2/(1-t) ⇒ HS*(1-t)^2 = 1 - 2t^2 + t^3.
        let hn = hilbert_numerator(&[from_exps(vec![2, 0]), from_exps(vec![1, 1])]);
        assert_eq!(hn.coeffs(), &[1, 0, -2, 1]);
    }

    #[test]
    fn hn_square_of_max_ideal() {
        // I = m^2 = (x^2, x*y, y^2) in k[x, y].
        // S/I has basis {1, x, y} (HF = 1, 2). HN = 1 - 3t^2 + 2t^3.
        let hn = hilbert_numerator(&[
            from_exps(vec![2, 0]),
            from_exps(vec![1, 1]),
            from_exps(vec![0, 2]),
        ]);
        assert_eq!(hn.coeffs(), &[1, 0, -3, 2]);
    }

    #[test]
    fn hn_chain_overlap_xy_yz() {
        // I = (x*y, y*z) in k[x, y, z]. Standard monomials are
        // monomials with `b = 0` (no `y`) plus pure powers `y^k`.
        // HF(0) = 1, HF(d) = d+2 for d ≥ 1; HN = 1 - 2t^2 + t^3.
        let hn = hilbert_numerator(&[from_exps(vec![1, 1, 0]), from_exps(vec![0, 1, 1])]);
        assert_eq!(hn.coeffs(), &[1, 0, -2, 1]);
    }

    #[test]
    fn hn_redundant_generators_are_minimised() {
        // (x, x*y) ⇒ x*y is redundant, so HN = 1 - t (same as `(x)`).
        let hn = hilbert_numerator(&[x(2, 0, 1), from_exps(vec![1, 1])]);
        assert_eq!(hn.coeffs(), &[1, -1]);
    }

    #[test]
    fn hn_artinian_ideal_coeffs_sum_to_zero() {
        // For an artinian ideal I (i.e. `S/I` finite-dimensional),
        // `HN(1) = 0`: `HS(t) = HN(t) / (1-t)^n` is defined at `t=1`
        // only when `(1-t)^n | HN(t)`, which forces `HN(1) = 0`.
        // I = (x^2, x*y, y^2) ⇒ HN = 1 - 3t^2 + 2t^3, sum = 0.
        let hn = hilbert_numerator(&[
            from_exps(vec![2, 0]),
            from_exps(vec![1, 1]),
            from_exps(vec![0, 2]),
        ]);
        let sum: i64 = hn.coeffs().iter().sum();
        assert_eq!(sum, 0);
    }

    #[test]
    fn hn_addition_subtraction_round_trip() {
        let mut a = HilbertNum { coeffs: vec![1, -2, 3] };
        let b = HilbertNum { coeffs: vec![0, 1, 0, -4] };
        a.add_assign(&b);
        assert_eq!(a.coeffs(), &[1, -1, 3, -4]);
        a.sub_assign(&b);
        assert_eq!(a.coeffs(), &[1, -2, 3]);
    }

    #[test]
    fn hn_mul_t_pow_shifts() {
        let mut a = HilbertNum { coeffs: vec![1, -2, 3] };
        a.mul_t_pow_assign(2);
        assert_eq!(a.coeffs(), &[0, 0, 1, -2, 3]);
        let mut z = HilbertNum::zero();
        z.mul_t_pow_assign(5);
        assert_eq!(z, HilbertNum::zero());
    }

    #[test]
    fn hn_mul_polynomials() {
        // (1 - t) * (1 - t) = 1 - 2t + t^2
        let a = HilbertNum::one_minus_t_pow(1);
        let b = HilbertNum::one_minus_t_pow(1);
        assert_eq!(a.mul(&b).coeffs(), &[1, -2, 1]);
    }

    #[test]
    fn hn_degree_and_trim() {
        let a = HilbertNum { coeffs: vec![1, 0, 0, 0] };
        assert_eq!(a.degree(), Some(0));
        let z = HilbertNum::zero();
        assert_eq!(z.degree(), None);
    }

    #[test]
    fn hn_saturating_arithmetic_does_not_panic_on_extreme_input() {
        // `i64::MAX`-valued coefficients exercise the saturating
        // arithmetic in `mul` and `add_assign`. Result coefficients
        // clamp to `i64::{MIN, MAX}` rather than wrapping.
        let huge = HilbertNum { coeffs: vec![i64::MAX, i64::MAX] };
        let other = HilbertNum { coeffs: vec![2, 2] };
        let prod = huge.mul(&other);
        // All coefficients are saturated; no panic.
        for &c in prod.coeffs() {
            assert!(c >= 0 || c == i64::MIN, "saturated coefficient must be in range");
        }

        let mut acc = HilbertNum { coeffs: vec![i64::MAX] };
        let plus_one = HilbertNum { coeffs: vec![1] };
        acc.add_assign(&plus_one);
        assert_eq!(acc.coeff(0), i64::MAX, "add_assign saturates at i64::MAX");
    }

    #[test]
    fn binom_basic_and_symmetry() {
        assert_eq!(binom_sat(0, 0), 1);
        assert_eq!(binom_sat(5, 0), 1);
        assert_eq!(binom_sat(5, 5), 1);
        assert_eq!(binom_sat(5, 2), 10);
        assert_eq!(binom_sat(5, 3), 10); // symmetry C(5,3)=C(5,2)
        assert_eq!(binom_sat(10, 4), 210);
        assert_eq!(binom_sat(3, 5), 0); // r > m
        // Large m, small r: choosing min(r, m-r) keeps it exact and cheap.
        assert_eq!(binom_sat(1000, 2), 1000 * 999 / 2);
    }

    #[test]
    fn hf_at_counts_degree_d_part() {
        // I = (x^2, x*y, y^2) = m^2 in k[x,y]; HF = 1, 2, 0, 0, ...
        let hn = hilbert_numerator(&[
            from_exps(vec![2, 0]),
            from_exps(vec![1, 1]),
            from_exps(vec![0, 2]),
        ]);
        assert_eq!(hn.hf_at(0, 2), 1);
        assert_eq!(hn.hf_at(1, 2), 2);
        assert_eq!(hn.hf_at(2, 2), 0);
        assert_eq!(hn.hf_at(3, 2), 0);
    }

    #[test]
    fn hf_at_single_var_power() {
        // I = (x^3) in k[x]: standard {1, x, x^2}; HF(d) = 1 for d < 3, else 0.
        let hn = hilbert_numerator(&[x(1, 0, 3)]);
        assert_eq!(hn.hf_at(0, 1), 1);
        assert_eq!(hn.hf_at(1, 1), 1);
        assert_eq!(hn.hf_at(2, 1), 1);
        assert_eq!(hn.hf_at(3, 1), 0);
    }

    #[test]
    fn hf_at_free_polynomial_ring() {
        // I = 0 in k[x, y]: HF(d) = C(d+1, 1) = d + 1 (monomials of degree d).
        let hn = HilbertNum::one();
        assert_eq!(hn.hf_at(0, 2), 1);
        assert_eq!(hn.hf_at(1, 2), 2);
        assert_eq!(hn.hf_at(4, 2), 5);
        // k[x,y,z]: HF(d) = C(d+2, 2).
        assert_eq!(hn.hf_at(3, 3), 10);
    }

    #[test]
    fn quotient_dim_zero_dimensional_cases() {
        // (x, y): standard {1} ⇒ dim 1.
        assert_eq!(quotient_dimension(&[x(2, 0, 1), x(2, 1, 1)], 2), Some(1));
        // m^2 = (x^2, x*y, y^2): standard {1, x, y} ⇒ dim 3.
        assert_eq!(
            quotient_dimension(
                &[from_exps(vec![2, 0]), from_exps(vec![1, 1]), from_exps(vec![0, 2])],
                2
            ),
            Some(3)
        );
        // (x^2, y^2): standard {1, x, y, x*y} ⇒ dim 4.
        assert_eq!(
            quotient_dimension(&[from_exps(vec![2, 0]), from_exps(vec![0, 2])], 2),
            Some(4)
        );
        // (x^3) in k[x]: standard {1, x, x^2} ⇒ dim 3.
        assert_eq!(quotient_dimension(&[x(1, 0, 3)], 1), Some(3));
        // (x^a, y^b): box of standard monomials ⇒ a*b.
        assert_eq!(
            quotient_dimension(&[x(2, 0, 4), x(2, 1, 5)], 2),
            Some(20)
        );
    }

    #[test]
    fn quotient_dim_positive_dimensional_is_none() {
        // (x) in k[x, y]: y is free ⇒ infinite-dimensional.
        assert_eq!(quotient_dimension(&[x(2, 0, 1)], 2), None);
        // (x*y) in k[x, y]: neither x nor y has a pure power.
        assert_eq!(quotient_dimension(&[from_exps(vec![1, 1])], 2), None);
        // Empty ideal in a non-trivial ring: the whole ring, infinite-dim.
        assert_eq!(quotient_dimension(&[], 2), None);
    }

    #[test]
    fn quotient_dim_edge_unit_and_scalar_ring() {
        // Unit ideal (contains 1): S/I = 0.
        assert_eq!(quotient_dimension(&[Monomial::one(3)], 3), Some(0));
        // S = k (n_vars = 0), I = 0: dim 1.
        assert_eq!(quotient_dimension(&[], 0), Some(1));
    }

    #[test]
    fn quotient_dim_equals_summed_hilbert_function() {
        // Cross-check the closed-form sum against term-by-term HF for an
        // Artinian ideal: I = (x^2, y^3) in k[x, y], dim = 2*3 = 6.
        let gens = [x(2, 0, 2), x(2, 1, 3)];
        let hn = hilbert_numerator(&gens);
        let mut summed: i128 = 0;
        for d in 0..16 {
            summed += hn.hf_at(d, 2);
        }
        assert_eq!(summed, 6);
        assert_eq!(quotient_dimension(&gens, 2), Some(6));
    }
}
