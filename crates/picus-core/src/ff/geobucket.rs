//! Geobucket data structure (Yan 1998) for efficient polynomial accumulation.
//!
//! A geobucket is a collection of "buckets" of geometrically increasing
//! capacity. Each bucket holds a sorted-descending polynomial. When a bucket
//! overflows its capacity, its contents are merged into the next bucket.
//! Adding a polynomial of length `L` costs O(L * log(N/L)) amortized vs.
//! O(N) for a naive single-vector accumulator — which is the dominant
//! speedup during multi-step polynomial reduction.
//!
//! Each bucket is stored as a `DensePoly` plus a `head` cursor so that
//! `pop_leading_term` can advance in O(1) without rebuilding the bucket.
//! Cross-bucket merges materialize only the live tail of each bucket
//! (terms at index `head..`).

use std::cmp::Ordering;

use super::field::FieldElem;
use super::geobucket_params::{BASE_CAPACITY, MAX_BUCKETS, RATIO};
use super::polynomial::{PolyRing, DensePoly};
use crate::metric;

pub struct Geobucket<'r> {
    buckets: Vec<DensePoly>,
    heads: Vec<usize>,
    ring: &'r PolyRing,
    /// Scratch buffers for `sub_scaled_tail` — capacity is preserved
    /// across calls. With GMP-backed `FieldElem`s, the bigger win than
    /// avoiding a `Vec` allocation is keeping the existing `FieldElem`
    /// instances (and their internal `mpz_t` storage) alive: reassigning
    /// values into them avoids the per-iteration `mpz_init` / `mpz_clear`
    /// pair that fresh Vec construction would incur.
    scratch_exps: Vec<u16>,
    scratch_coeffs: Vec<FieldElem>,
    scratch_degs: Vec<u32>,
}

impl<'r> Geobucket<'r> {
    pub fn new(ring: &'r PolyRing) -> Self {
        Geobucket {
            buckets: Vec::new(),
            heads: Vec::new(),
            ring,
            scratch_exps: Vec::new(),
            scratch_coeffs: Vec::new(),
            scratch_degs: Vec::new(),
        }
    }

    pub fn from_poly(poly: DensePoly, ring: &'r PolyRing) -> Self {
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
            self.buckets.push(DensePoly::zero());
            self.heads.push(0);
        }
    }

    fn bucket_is_empty(&self, idx: usize) -> bool {
        idx >= self.buckets.len() || self.heads[idx] >= self.buckets[idx].num_terms()
    }

    /// Take ownership of the live tail of bucket `idx`, leaving the bucket empty.
    fn take_bucket_live(&mut self, idx: usize) -> DensePoly {
        if idx >= self.buckets.len() {
            return DensePoly::zero();
        }
        let head = self.heads[idx];
        self.heads[idx] = 0;
        let existing = std::mem::replace(&mut self.buckets[idx], DensePoly::zero());
        if head == 0 {
            return existing;
        }
        if head >= existing.num_terms() {
            return DensePoly::zero();
        }
        let n = self.ring.n_vars;
        let exps = existing.raw_exponents()[head * n..].to_vec();
        let coeffs = existing.raw_coeffs()[head..].to_vec();
        let degs = existing.raw_total_degs()[head..].to_vec();
        DensePoly::from_raw_sorted(exps, coeffs, degs)
    }

    /// Add a polynomial. Amortized O(L * log(N/L)) where L = len(p), N = total size.
    pub fn add_poly(&mut self, p: DensePoly) {
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
            // Take ownership of bucket[idx]'s live tail and merge with
            // `cur`. Both `live` and `cur` are owned, so `merge_owned`
            // recycles their `FieldElem` allocations into the output
            // instead of cloning each.
            let live = self.take_bucket_live(idx);
            let merged = live.merge_owned(cur, self.ring, false);
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
    pub fn sub_scaled(&mut self, mul_exps: &[u16], neg_coeff: &FieldElem, divisor: &DensePoly) {
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
        divisor: &DensePoly,
    ) {
        let div_len = divisor.num_terms();
        if div_len <= 1 || self.ring.field.is_zero(neg_coeff) {
            return;
        }
        // One cached gb-stats read for both sub-region timers (this is a hot
        // reduction step); the gated `metric::timer!`s below add no per-call
        // thread-local config read.
        metric::gate!(stats);
        let scaled_tail = {
            metric::timer!(stats, crate::profile::SPLIT_GB.time_sub_scaled_setup_ns);
            let n = self.ring.n_vars;
            let mul_deg: u32 = mul_exps.iter().map(|&e| e as u32).sum();
            let tail_len = div_len - 1;
            self.scratch_exps.clear();
            self.scratch_coeffs.clear();
            self.scratch_degs.clear();
            self.scratch_exps.reserve(tail_len * n);
            self.scratch_coeffs.reserve(tail_len);
            self.scratch_degs.reserve(tail_len);
            let d_exps = divisor.raw_exponents();
            let d_coeffs = divisor.raw_coeffs();
            let d_degs = divisor.raw_total_degs();
            for i in 1..div_len {
                let base = &d_exps[i * n..(i + 1) * n];
                for k in 0..n {
                    let sum = base[k].checked_add(mul_exps[k])
                        .expect("exponent overflow in sub_scaled_tail");
                    self.scratch_exps.push(sum);
                }
                self.scratch_coeffs.push(self.ring.field.mul(&d_coeffs[i], neg_coeff));
                self.scratch_degs.push(d_degs[i] + mul_deg);
            }
            DensePoly::from_raw_sorted(
                std::mem::take(&mut self.scratch_exps),
                std::mem::take(&mut self.scratch_coeffs),
                std::mem::take(&mut self.scratch_degs),
            )
        };
        {
            metric::timer!(stats, crate::profile::SPLIT_GB.time_sub_scaled_addpoly_ns);
            self.add_poly(scaled_tail);
        }
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
                        if DensePoly::cmp_term_at(i_exps, i_deg, b_exps, b_deg, order)
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
                    // In-place add to avoid a per-merge `FieldElem`
                    // allocation. `coeff` is owned here; `add_assign`
                    // mutates it in place.
                    self.ring.field.add_assign(&mut coeff, &self.buckets[i].raw_coeffs()[head_i]);
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
        let p = DensePoly::from_raw_sorted(exps.clone(), vec![coeff.clone()], vec![deg]);
        self.add_poly(p);
        Some((exps, deg, coeff))
    }

    /// Consolidate every bucket into a single canonical `DensePoly`.
    pub fn into_poly(self) -> DensePoly {
        let Geobucket { buckets, heads, ring, .. } = self;
        let n = ring.n_vars;
        let mut out = DensePoly::zero();
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
                DensePoly::from_raw_sorted(exps, coeffs, degs)
            };
            out = out.add(&live, ring);
        }
        out
    }
}

#[cfg(test)]
#[path = "geobucket_tests.rs"]
mod tests;
