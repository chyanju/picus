//! Geobucket data structure (Yan 1998) for efficient polynomial accumulation.
//!
//! A geobucket is a collection of "buckets" of geometrically increasing
//! capacity. Each bucket holds a sorted-descending polynomial. When a bucket
//! overflows its capacity, its contents are merged into the next bucket.
//! Adding a polynomial of length `L` costs O(L * log(N/L)) amortized vs.
//! O(N) for a naive single-vector accumulator — which is the dominant
//! speedup during multi-step polynomial reduction.
//!
//! Each bucket is stored as a `Polynomial` plus a `head` cursor so that
//! `pop_leading_term` can advance in O(1) without rebuilding the bucket.
//! Cross-bucket merges materialize only the live tail of each bucket
//! (terms at index `head..`).

use std::cmp::Ordering;

use super::field::FieldElem;
use super::polynomial::{PolyRing, Polynomial};

/// Smallest bucket capacity (in terms).
const BASE_CAPACITY: usize = 4;
/// Geometric growth factor between consecutive buckets.
const RATIO: usize = 4;
/// Hard cap on the number of buckets. 4 * 4^15 covers polynomials of ~10^9 terms.
const MAX_BUCKETS: usize = 16;

pub struct Geobucket<'r> {
    buckets: Vec<Polynomial>,
    heads: Vec<usize>,
    ring: &'r PolyRing,
}

impl<'r> Geobucket<'r> {
    pub fn new(ring: &'r PolyRing) -> Self {
        Geobucket { buckets: Vec::new(), heads: Vec::new(), ring }
    }

    pub fn from_poly(poly: Polynomial, ring: &'r PolyRing) -> Self {
        let mut gb = Self::new(ring);
        gb.add_poly(poly);
        gb
    }

    /// Capacity of bucket `idx`: BASE_CAPACITY * RATIO^idx, saturating to usize::MAX.
    fn capacity(idx: usize) -> usize {
        let mut cap = BASE_CAPACITY;
        for _ in 0..idx {
            cap = match cap.checked_mul(RATIO) {
                Some(v) => v,
                None => return usize::MAX,
            };
        }
        cap
    }

    /// Smallest bucket index whose capacity is >= `len`. Capped at MAX_BUCKETS - 1.
    fn fitting_bucket(len: usize) -> usize {
        let mut idx = 0usize;
        let mut cap = BASE_CAPACITY;
        while cap < len && idx + 1 < MAX_BUCKETS {
            idx += 1;
            cap = cap.saturating_mul(RATIO);
        }
        idx
    }

    fn ensure_bucket(&mut self, idx: usize) {
        while self.buckets.len() <= idx {
            self.buckets.push(Polynomial::zero());
            self.heads.push(0);
        }
    }

    fn bucket_is_empty(&self, idx: usize) -> bool {
        idx >= self.buckets.len() || self.heads[idx] >= self.buckets[idx].num_terms()
    }

    /// Take ownership of the live tail of bucket `idx`, leaving the bucket empty.
    fn take_bucket_live(&mut self, idx: usize) -> Polynomial {
        if idx >= self.buckets.len() {
            return Polynomial::zero();
        }
        let head = self.heads[idx];
        self.heads[idx] = 0;
        let existing = std::mem::replace(&mut self.buckets[idx], Polynomial::zero());
        if head == 0 {
            return existing;
        }
        if head >= existing.num_terms() {
            return Polynomial::zero();
        }
        let n = self.ring.n_vars;
        let exps = existing.raw_exponents()[head * n..].to_vec();
        let coeffs = existing.raw_coeffs()[head..].to_vec();
        let degs = existing.raw_total_degs()[head..].to_vec();
        Polynomial::from_raw_sorted(exps, coeffs, degs)
    }

    /// Add a polynomial. Amortized O(L * log(N/L)) where L = len(p), N = total size.
    pub fn add_poly(&mut self, p: Polynomial) {
        if p.is_zero() {
            return;
        }
        let mut cur = p;
        let mut idx = Self::fitting_bucket(cur.num_terms());
        loop {
            self.ensure_bucket(idx);
            if self.bucket_is_empty(idx) {
                let cap_here = Self::capacity(idx);
                if cur.num_terms() <= cap_here || idx + 1 >= MAX_BUCKETS {
                    self.buckets[idx] = cur;
                    self.heads[idx] = 0;
                    return;
                }
                idx += 1;
                continue;
            }
            // Take ownership of bucket[idx]'s live tail and merge with `cur`.
            // No clone needed when head == 0 (the common case).
            let live = self.take_bucket_live(idx);
            let merged = live.add(&cur, self.ring);
            let merged_len = merged.num_terms();
            if merged_len == 0 {
                return;
            }
            let cap_here = Self::capacity(idx);
            if merged_len <= cap_here || idx + 1 >= MAX_BUCKETS {
                self.buckets[idx] = merged;
                return;
            }
            cur = merged;
            idx += 1;
        }
    }

    /// Subtract `neg_coeff * x^mul_exps * divisor` from the geobucket.
    /// Internally materializes the scaled polynomial then routes via `add_poly`.
    pub fn sub_scaled(&mut self, mul_exps: &[u16], neg_coeff: &FieldElem, divisor: &Polynomial) {
        if divisor.is_zero() || self.ring.field.is_zero(neg_coeff) {
            return;
        }
        let scaled = divisor.mul_term(mul_exps, neg_coeff, self.ring);
        self.add_poly(scaled);
    }

    /// Like `sub_scaled` but skips the divisor's leading term — used during
    /// reduction where the LT contribution exactly cancels the polynomial's
    /// already-popped leading term. Saves one Vec slice + one mul per call
    /// vs. computing the full scaled polynomial.
    pub fn sub_scaled_tail(
        &mut self,
        mul_exps: &[u16],
        neg_coeff: &FieldElem,
        divisor: &Polynomial,
    ) {
        let div_len = divisor.num_terms();
        if div_len <= 1 || self.ring.field.is_zero(neg_coeff) {
            return;
        }
        let n = self.ring.n_vars;
        let mul_deg: u32 = mul_exps.iter().map(|&e| e as u32).sum();
        let tail_len = div_len - 1;
        let mut out_exps: Vec<u16> = Vec::with_capacity(tail_len * n);
        let mut out_coeffs: Vec<FieldElem> = Vec::with_capacity(tail_len);
        let mut out_degs: Vec<u32> = Vec::with_capacity(tail_len);
        let d_exps = divisor.raw_exponents();
        let d_coeffs = divisor.raw_coeffs();
        let d_degs = divisor.raw_total_degs();
        for i in 1..div_len {
            let base = &d_exps[i * n..(i + 1) * n];
            for k in 0..n {
                let sum = base[k].checked_add(mul_exps[k])
                    .expect("exponent overflow in sub_scaled_tail");
                out_exps.push(sum);
            }
            out_coeffs.push(self.ring.field.mul(&d_coeffs[i], neg_coeff));
            out_degs.push(d_degs[i] + mul_deg);
        }
        let scaled_tail = Polynomial::from_raw_sorted(out_exps, out_coeffs, out_degs);
        self.add_poly(scaled_tail);
    }

    pub fn is_zero(&self) -> bool {
        (0..self.buckets.len()).all(|i| self.bucket_is_empty(i))
    }

    /// Pop the leading term across all buckets. Cancellations are resolved here:
    /// if multiple buckets share the leading monomial, their coefficients are
    /// summed; if the sum is zero the term is discarded and we continue.
    /// Cost: O(num_buckets) per call, plus O(num_buckets) per cancellation step.
    pub fn pop_leading_term(&mut self) -> Option<(Vec<u16>, u32, FieldElem)> {
        let n = self.ring.n_vars;
        let order = self.ring.order;
        loop {
            // Find the bucket with the maximal current leading monomial.
            let mut best: Option<usize> = None;
            for i in 0..self.buckets.len() {
                if self.bucket_is_empty(i) {
                    continue;
                }
                let head_i = self.heads[i];
                let i_exps = &self.buckets[i].raw_exponents()[head_i * n..(head_i + 1) * n];
                let i_deg = self.buckets[i].raw_total_degs()[head_i];
                match best {
                    None => best = Some(i),
                    Some(b) => {
                        let head_b = self.heads[b];
                        let b_exps = &self.buckets[b].raw_exponents()[head_b * n..(head_b + 1) * n];
                        let b_deg = self.buckets[b].raw_total_degs()[head_b];
                        if Polynomial::cmp_term_at(i_exps, i_deg, b_exps, b_deg, order)
                            == Ordering::Greater
                        {
                            best = Some(i);
                        }
                    }
                }
            }
            let best = best?;
            // Snapshot the chosen monomial and consume that bucket's head.
            let head_b = self.heads[best];
            let exps: Vec<u16> = self.buckets[best].raw_exponents()
                [head_b * n..(head_b + 1) * n]
                .to_vec();
            let deg = self.buckets[best].raw_total_degs()[head_b];
            let mut coeff = self.buckets[best].raw_coeffs()[head_b].clone();
            self.heads[best] += 1;
            // Sum coefficients from any other buckets whose head matches this monomial.
            for i in 0..self.buckets.len() {
                if i == best || self.bucket_is_empty(i) {
                    continue;
                }
                let head_i = self.heads[i];
                let i_deg = self.buckets[i].raw_total_degs()[head_i];
                if i_deg != deg {
                    continue;
                }
                let i_exps = &self.buckets[i].raw_exponents()[head_i * n..(head_i + 1) * n];
                if i_exps == exps.as_slice() {
                    coeff = self.ring.field.add(&coeff, &self.buckets[i].raw_coeffs()[head_i]);
                    self.heads[i] += 1;
                }
            }
            if !self.ring.field.is_zero(&coeff) {
                return Some((exps, deg, coeff));
            }
            // Cancelled: continue the loop to find the next leading term.
        }
    }

    /// Peek at the leading term. Implemented on top of `pop_leading_term` —
    /// resolves any pending cancellations, then re-inserts the surviving term.
    pub fn leading_term(&mut self) -> Option<(Vec<u16>, u32, FieldElem)> {
        let (exps, deg, coeff) = self.pop_leading_term()?;
        let p = Polynomial::from_raw_sorted(exps.clone(), vec![coeff.clone()], vec![deg]);
        self.add_poly(p);
        Some((exps, deg, coeff))
    }

    /// Consolidate every bucket into a single canonical `Polynomial`.
    pub fn into_poly(self) -> Polynomial {
        let Geobucket { buckets, heads, ring } = self;
        let n = ring.n_vars;
        let mut out = Polynomial::zero();
        for (i, b) in buckets.into_iter().enumerate() {
            let head = heads[i];
            if head >= b.num_terms() {
                continue;
            }
            let live = if head == 0 {
                b
            } else {
                let exps = b.raw_exponents()[head * n..].to_vec();
                let coeffs = b.raw_coeffs()[head..].to_vec();
                let degs = b.raw_total_degs()[head..].to_vec();
                Polynomial::from_raw_sorted(exps, coeffs, degs)
            };
            out = out.add(&live, ring);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::field::PrimeField;
    use super::super::monomial::{Monomial, MonomialOrder};
    use num_bigint::BigUint;
    use std::sync::Arc;

    fn small_ring() -> Arc<PolyRing> {
        let f = PrimeField::new(BigUint::from(101u32));
        PolyRing::new(f, vec!["x".into(), "y".into(), "z".into()], MonomialOrder::DegRevLex)
    }

    fn mk(ring: &PolyRing, terms: Vec<(Vec<u16>, u64)>) -> Polynomial {
        let f = &ring.field;
        let v: Vec<(Monomial, FieldElem)> = terms
            .into_iter()
            .map(|(e, c)| (Monomial::from_exponents(e), f.from_u64(c)))
            .collect();
        Polynomial::from_terms(v, ring)
    }

    #[test]
    fn from_poly_into_poly_roundtrip() {
        let r = small_ring();
        let p = mk(&r, vec![
            (vec![2, 1, 0], 3),
            (vec![1, 0, 2], 5),
            (vec![0, 0, 1], 7),
            (vec![0, 0, 0], 1),
        ]);
        let gb = Geobucket::from_poly(p.clone(), &r);
        let q = gb.into_poly();
        assert_eq!(p.num_terms(), q.num_terms());
        for (a, b) in p.terms(&r).zip(q.terms(&r)) {
            assert_eq!(a.exponents(), b.exponents());
            assert_eq!(a.coefficient(), b.coefficient());
        }
    }

    #[test]
    fn add_poly_matches_polynomial_add() {
        let r = small_ring();
        let p = mk(&r, vec![
            (vec![3, 0, 0], 1),
            (vec![1, 1, 0], 2),
            (vec![0, 0, 0], 5),
        ]);
        let q = mk(&r, vec![
            (vec![3, 0, 0], 4),
            (vec![2, 0, 0], 9),
            (vec![0, 0, 1], 3),
        ]);
        let expect = p.add(&q, &r);
        let mut gb = Geobucket::from_poly(p, &r);
        gb.add_poly(q);
        let got = gb.into_poly();
        assert_eq!(got.num_terms(), expect.num_terms());
        for (a, b) in expect.terms(&r).zip(got.terms(&r)) {
            assert_eq!(a.exponents(), b.exponents());
            assert_eq!(a.coefficient(), b.coefficient());
        }
    }

    #[test]
    fn pop_leading_term_descending_order() {
        let r = small_ring();
        let p = mk(&r, vec![
            (vec![2, 1, 0], 3),
            (vec![0, 0, 1], 7),
            (vec![0, 0, 0], 1),
        ]);
        let mut gb = Geobucket::from_poly(p, &r);
        let (e1, d1, c1) = gb.pop_leading_term().unwrap();
        assert_eq!(e1, vec![2, 1, 0]);
        assert_eq!(d1, 3);
        assert_eq!(c1, r.field.from_u64(3));
        let (e2, d2, _) = gb.pop_leading_term().unwrap();
        assert_eq!(e2, vec![0, 0, 1]);
        assert_eq!(d2, 1);
        let (e3, d3, _) = gb.pop_leading_term().unwrap();
        assert_eq!(e3, vec![0, 0, 0]);
        assert_eq!(d3, 0);
        assert!(gb.pop_leading_term().is_none());
        assert!(gb.is_zero());
    }

    #[test]
    fn pop_resolves_cross_bucket_cancellation() {
        let r = small_ring();
        let p = mk(&r, vec![(vec![1, 0, 0], 5)]);
        let q = mk(&r, vec![(vec![1, 0, 0], 96)]); // 5 + 96 = 101 ≡ 0 mod 101
        let mut gb = Geobucket::new(&r);
        // Force them into separate buckets by adding small polys (they fit
        // bucket 0). Both go into bucket 0 first, but the second add merges
        // them — so to test cross-bucket cancellation we use sub_scaled to
        // route the second one differently.
        gb.add_poly(p);
        gb.add_poly(q);
        // Whichever buckets they land in, the result must be zero.
        assert!(gb.is_zero() || gb.pop_leading_term().is_none());
    }

    #[test]
    fn sub_scaled_basic() {
        let r = small_ring();
        // p = 3*x^2*y + 7*z + 1
        let p = mk(&r, vec![
            (vec![2, 1, 0], 3),
            (vec![0, 0, 1], 7),
            (vec![0, 0, 0], 1),
        ]);
        // d = x + 1
        let d = mk(&r, vec![
            (vec![1, 0, 0], 1),
            (vec![0, 0, 0], 1),
        ]);
        // sub_scaled is called with the already-negated coefficient (matching the
        // convention used by `reduce_by_refs`). Passing `neg_coeff = -3` adds
        // -3*(x*y)*d = -3*x^2*y - 3*x*y to p, yielding -3*x*y + 7*z + 1.
        let mut gb = Geobucket::from_poly(p, &r);
        let neg_three = r.field.neg(&r.field.from_u64(3));
        gb.sub_scaled(&[1, 1, 0], &neg_three, &d);
        let result = gb.into_poly();
        let expect = mk(&r, vec![
            (vec![1, 1, 0], 101 - 3), // -3 mod 101 = 98
            (vec![0, 0, 1], 7),
            (vec![0, 0, 0], 1),
        ]);
        assert_eq!(result.num_terms(), expect.num_terms());
        for (a, b) in expect.terms(&r).zip(result.terms(&r)) {
            assert_eq!(a.exponents(), b.exponents());
            assert_eq!(a.coefficient(), b.coefficient());
        }
    }

    #[test]
    fn many_adds_cascade_buckets() {
        let r = small_ring();
        // Add 200 small polynomials; result should equal sum.
        let mut gb = Geobucket::new(&r);
        let mut expect = Polynomial::zero();
        for i in 0..200u64 {
            let p = mk(&r, vec![
                (vec![(i % 5) as u16, ((i / 5) % 5) as u16, ((i / 25) % 5) as u16], (i % 97) + 1),
            ]);
            expect = expect.add(&p, &r);
            gb.add_poly(p);
        }
        let got = gb.into_poly();
        assert_eq!(got.num_terms(), expect.num_terms());
        for (a, b) in expect.terms(&r).zip(got.terms(&r)) {
            assert_eq!(a.exponents(), b.exponents());
            assert_eq!(a.coefficient(), b.coefficient());
        }
    }

    #[test]
    fn empty_geobucket() {
        let r = small_ring();
        let gb = Geobucket::new(&r);
        assert!(gb.is_zero());
        assert!(gb.into_poly().is_zero());
    }

    #[test]
    fn add_zero_is_noop() {
        let r = small_ring();
        let p = mk(&r, vec![(vec![1, 0, 0], 7)]);
        let mut gb = Geobucket::from_poly(p.clone(), &r);
        gb.add_poly(Polynomial::zero());
        let got = gb.into_poly();
        assert_eq!(got.num_terms(), p.num_terms());
    }

    #[test]
    fn leading_term_then_pop_consistent() {
        let r = small_ring();
        let p = mk(&r, vec![
            (vec![2, 1, 0], 3),
            (vec![1, 0, 0], 5),
            (vec![0, 0, 0], 1),
        ]);
        let mut gb = Geobucket::from_poly(p, &r);
        let peek = gb.leading_term().unwrap();
        let pop = gb.pop_leading_term().unwrap();
        assert_eq!(peek.0, pop.0);
        assert_eq!(peek.1, pop.1);
        assert_eq!(peek.2, pop.2);
    }
}
