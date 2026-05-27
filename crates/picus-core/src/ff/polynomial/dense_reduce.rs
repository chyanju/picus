//! Dense-polynomial Gröbner reduction: the `reduce_by_refs*` family
//! (geobucket / DivMask-indexed reducers) and the `reduce_by_refs_naive`
//! cross-check oracle, as inherent `impl DensePoly` methods. Split out of
//! `polynomial.rs` (the future F4/CoCoA churn zone) so the dense arithmetic
//! and the reduction engine read separately; inherent methods need no
//! re-export, so `DensePoly::reduce_by_refs*` call sites are unchanged.

use super::*;

impl DensePoly {
    /// Like `reduce_by` but takes references to divisors — avoids cloning
    /// the divisor list when the caller already holds polynomials inside
    /// some larger container (e.g. `BuchbergerState::basis`).
    ///
    /// Geobucket-based accumulator (Yan 1998). Each reduction step is
    /// O(D · log(N / D)) where D is the divisor length and N is the
    /// running tail size.
    pub fn reduce_by_refs(&self, divisors: &[&DensePoly], ring: &PolyRing) -> DensePoly {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, None, None, None)
    }

    /// Cancel-aware variant of [`reduce_by_refs`]. On cancel, returns
    /// the partial remainder accumulated so far — sound (same residue
    /// class) but not necessarily a normal form. Hot paths (Buchberger
    /// main loop, interreduce, bit-prop `contains`) should prefer this
    /// over [`reduce_by_refs`] so the cancel token is honoured on
    /// dense polynomials.
    pub fn reduce_by_refs_cancel(
        &self,
        divisors: &[&DensePoly],
        ring: &PolyRing,
        cancel: &crate::timeout::CancelToken,
    ) -> DensePoly {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, Some(cancel), None, None)
    }

    /// Variant of [`reduce_by_refs_cancel`] that also records, in
    /// `use_counts`, how many times each divisor was selected as the
    /// reducer during this call. `use_counts.len()` must equal
    /// `divisors.len()`; entries are incremented (not zeroed).
    pub fn reduce_by_refs_counted_cancel(
        &self,
        divisors: &[&DensePoly],
        ring: &PolyRing,
        cancel: &crate::timeout::CancelToken,
        use_counts: &mut [u64],
    ) -> DensePoly {
        debug_assert_eq!(divisors.len(), use_counts.len());
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, Some(cancel), Some(use_counts), None)
    }

    /// Like [`reduce_by_refs_counted_cancel`] but reuses the caller's
    /// precomputed leading-term DivMasks (`div_dms[i]` for `divisors[i]`),
    /// skipping the per-call recompute. Result-identical.
    pub fn reduce_by_refs_counted_cancel_dms(
        &self,
        divisors: &[&DensePoly],
        ring: &PolyRing,
        cancel: &crate::timeout::CancelToken,
        use_counts: &mut [u64],
        div_dms: &[crate::ff::divmask::DivMask],
    ) -> DensePoly {
        debug_assert_eq!(divisors.len(), use_counts.len());
        debug_assert_eq!(divisors.len(), div_dms.len());
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, Some(cancel), Some(use_counts), Some(div_dms))
    }

    /// Non-cancel-aware version of [`reduce_by_refs_counted_cancel`].
    pub fn reduce_by_refs_counted(
        &self,
        divisors: &[&DensePoly],
        ring: &PolyRing,
        use_counts: &mut [u64],
    ) -> DensePoly {
        debug_assert_eq!(divisors.len(), use_counts.len());
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, None, Some(use_counts), None)
    }

    /// Like [`reduce_by_refs_counted`] but reuses the caller's precomputed
    /// leading-term DivMasks. Result-identical.
    pub fn reduce_by_refs_counted_dms(
        &self,
        divisors: &[&DensePoly],
        ring: &PolyRing,
        use_counts: &mut [u64],
        div_dms: &[crate::ff::divmask::DivMask],
    ) -> DensePoly {
        debug_assert_eq!(divisors.len(), use_counts.len());
        debug_assert_eq!(divisors.len(), div_dms.len());
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, None, Some(use_counts), Some(div_dms))
    }

    /// Geobucket-based reduction. Public for testing — production code should
    /// go through `reduce_by_refs` so the dispatch (currently always geobucket)
    /// stays in one place.
    ///
    /// When `use_counts` is provided, the per-divisor counter at the
    /// index of the selected reducer is incremented every iteration.
    pub fn reduce_by_refs_geobucket(
        &self,
        divisors: &[&DensePoly],
        ring: &PolyRing,
        cancel: Option<&crate::timeout::CancelToken>,
        mut use_counts: Option<&mut [u64]>,
        div_dms: Option<&[crate::ff::divmask::DivMask]>,
    ) -> DensePoly {
        let n = ring.n_vars;
        let stats_on = crate::profile::gb_stats_enabled();
        if stats_on {
            crate::profile::SPLIT_GB.reduce_calls
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        let setup_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };

        // Precompute LT info for each divisor: exponent slice (BORROWED,
        // no per-divisor Vec allocation), total degree, and DivMask. The
        // leading *coefficient* is not captured here — over a large prime a
        // `FieldElem` is a heap GMP integer, and only the divisor actually
        // selected needs its coefficient, so it is read lazily at selection
        // (once per reduction step, not once per divisor per call).
        use crate::ff::divmask::DivMask;
        let div_lt: Vec<Option<(&[u16], u32, DivMask)>> = divisors
            .iter()
            .enumerate()
            .map(|(i, d)| {
                if let Some(lt) = d.leading_term(ring) {
                    let exps = lt.exponents();  // borrows from divisor
                    let total_deg = lt.total_degree();
                    // Reuse the caller's precomputed leading-term DivMask
                    // when supplied (the Buchberger basis stores one per
                    // element); else compute it. Same value either way —
                    // tail reduction preserves the leading term — so the
                    // normal form is identical.
                    let dm = match div_dms {
                        Some(dms) => dms[i],
                        None => ring.divmask.compute_from_slice(exps),
                    };
                    Some((exps, total_deg, dm))
                } else {
                    None
                }
            })
            .collect();
        // When the divisor set is large, build an auxiliary index
        // sorted by leading-term total degree ascending. The lookup
        // loop iterates this index and `break`s on the first divisor
        // whose LT degree exceeds `lt_deg`. The normal-form output is
        // unchanged because the first divisor whose LT divides
        // `lt_exps` is unique on a Groebner-basis-shaped divisor set;
        // for small divisor sets the linear scan path is kept so
        // unit-tests' "reducer matches naive" property is preserved.
        const SORT_THRESHOLD: usize = 64;
        let order_opt: Option<Vec<usize>> = if div_lt.len() >= SORT_THRESHOLD {
            let mut order: Vec<usize> = (0..div_lt.len()).collect();
            order.sort_by_key(|&i| div_lt[i].as_ref().map(|t| t.1).unwrap_or(u32::MAX));
            Some(order)
        } else {
            None
        };

        // Hash-bucketed divisor index, keyed on `DivMask`. Only enabled
        // at ≥ 256 divisors, where `DivMask` filtering wins over the
        // sort + early-break path; below this threshold the cost of
        // building / iterating the buckets outweighs the savings.
        const BUCKET_THRESHOLD: usize = 256;
        let bucket_index_opt: Option<std::collections::HashMap<u128, Vec<usize>>> =
            if div_lt.len() >= BUCKET_THRESHOLD {
                let mut buckets: std::collections::HashMap<u128, Vec<usize>> =
                    std::collections::HashMap::new();
                for (i, lt_opt) in div_lt.iter().enumerate() {
                    if let Some((_, _, dm)) = lt_opt {
                        buckets.entry(dm.0).or_default().push(i);
                    }
                }
                // Sort each bucket by leading-term total degree
                // ascending so the lookup loop can `break` (not
                // `continue`) on the first divisor with deg > lt_deg.
                for indices in buckets.values_mut() {
                    indices.sort_by_key(|&i| div_lt[i].as_ref().map(|t| t.1).unwrap_or(u32::MAX));
                }
                Some(buckets)
            } else {
                None
            };

        let mut gb = crate::ff::geobucket::Geobucket::from_poly(self.clone(), ring);
        let mut result_exps: Vec<u16> = Vec::new();
        let mut result_coeffs: Vec<FieldElem> = Vec::new();
        let mut result_degs: Vec<u32> = Vec::new();
        let mut shift = vec![0u16; n];

        if let Some(t0) = setup_t0 {
            crate::profile::SPLIT_GB.time_div_lt_setup_ns
                .fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        let mut local_pops: u64 = 0;
        let mut local_lookups: u64 = 0;
        let mut local_sub_scaled: u64 = 0;
        let mut local_pop_ns: u64 = 0;
        let mut local_lookup_ns: u64 = 0;
        let mut local_sub_ns: u64 = 0;

        // Throttle the cancel check coarsely. Checking the atomic on
        // every iteration measurably slows reduction; period = 4096
        // keeps the per-iteration overhead unmeasurable while still
        // bounding cancel latency at the millisecond scale.
        let mut iter_counter: u32 = 0;
        const CANCEL_CHECK_PERIOD: u32 = 4096;
        // Bind the cancel reference outside the loop so the per-iteration
        // path doesn't re-pattern-match the Option.
        let cancel_ref = cancel;
        loop {
            let pop_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
            let popped = gb.pop_leading_term();
            if let Some(t0) = pop_t0 {
                local_pop_ns += t0.elapsed().as_nanos() as u64;
            }
            let (lt_exps, lt_deg, lt_coeff) = match popped {
                Some(t) => t,
                None => break,
            };
            local_pops += 1;
            iter_counter = iter_counter.wrapping_add(1);
            if iter_counter & (CANCEL_CHECK_PERIOD - 1) == 0 {
                if let Some(c) = cancel_ref {
                    if c.is_cancelled() {
                        // The current leading term was already popped above;
                        // re-attach it before draining the rest so the partial
                        // residue stays in the input's coset (same contract as
                        // the indexed and sparse cancel paths). It is the global
                        // maximum, so the result stays descending.
                        result_exps.extend_from_slice(&lt_exps);
                        result_coeffs.push(lt_coeff);
                        result_degs.push(lt_deg);
                        while let Some((e, d, c2)) = gb.pop_leading_term() {
                            result_exps.extend_from_slice(&e);
                            result_coeffs.push(c2);
                            result_degs.push(d);
                        }
                        if stats_on {
                            let g = &crate::profile::SPLIT_GB;
                            g.reduce_lt_pops.fetch_add(local_pops, std::sync::atomic::Ordering::Relaxed);
                            g.reduce_div_lookups.fetch_add(local_lookups, std::sync::atomic::Ordering::Relaxed);
                            g.reduce_sub_scaled_calls.fetch_add(local_sub_scaled, std::sync::atomic::Ordering::Relaxed);
                            g.time_pop_lt_ns.fetch_add(local_pop_ns, std::sync::atomic::Ordering::Relaxed);
                            g.time_div_lookup_ns.fetch_add(local_lookup_ns, std::sync::atomic::Ordering::Relaxed);
                            g.time_sub_scaled_ns.fetch_add(local_sub_ns, std::sync::atomic::Ordering::Relaxed);
                        }
                        return DensePoly::from_raw_sorted(result_exps, result_coeffs, result_degs);
                    }
                }
            }
            let lookup_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
            let cur_dm = ring.divmask.compute_from_slice(&lt_exps);
            let mut chosen: Option<usize> = None;
            if let Some(buckets) = &bucket_index_opt {
                // Hash-bucketed divisor lookup. Iterate only buckets
                // whose mask is a submask of `cur_dm` — others contain
                // divisors whose `DivMask` has bits `cur_dm` does not,
                // so they cannot divide. Within a compatible bucket
                // perform the full exponent check; break on the first
                // match. The pick is process-deterministic but may
                // differ from the linear-scan first-match across runs.
                let cur_bits = cur_dm.0;
                'outer: for (&mask, indices) in buckets {
                    if (mask & !cur_bits) != 0 {
                        // mask has bits cur_dm doesn't → no divisor in
                        // this bucket can divide LT.
                        continue;
                    }
                    for &di in indices {
                        local_lookups += 1;
                        if let Some((d_exps, d_deg, _)) = &div_lt[di] {
                            if *d_deg > lt_deg {
                                // Bucket is sorted by LT degree ascending;
                                // once it exceeds `lt_deg`, every later
                                // divisor in this bucket is also too big.
                                break;
                            }
                            let mut divides = true;
                            for k in 0..n {
                                if d_exps[k] > lt_exps[k] {
                                    divides = false;
                                    break;
                                }
                            }
                            if divides {
                                chosen = Some(di);
                                break 'outer;
                            }
                        }
                    }
                }
            } else if let Some(order) = &order_opt {
                // Sorted-ascending iteration with early break on
                // exceeded-degree divisors.
                for &di in order {
                    local_lookups += 1;
                    if let Some((d_exps, d_deg, d_dm)) = &div_lt[di] {
                        if *d_deg > lt_deg {
                            break;
                        }
                        if !d_dm.divides_consistent_with(cur_dm) {
                            continue;
                        }
                        let mut divides = true;
                        for k in 0..n {
                            if d_exps[k] > lt_exps[k] {
                                divides = false;
                                break;
                            }
                        }
                        if divides {
                            chosen = Some(di);
                            break;
                        }
                    }
                }
            } else {
                for (di, lt_opt) in div_lt.iter().enumerate() {
                    local_lookups += 1;
                    if let Some((d_exps, d_deg, d_dm)) = lt_opt {
                        if *d_deg > lt_deg {
                            continue;
                        }
                        if !d_dm.divides_consistent_with(cur_dm) {
                            continue;
                        }
                        let mut divides = true;
                        for k in 0..n {
                            if d_exps[k] > lt_exps[k] {
                                divides = false;
                                break;
                            }
                        }
                        if divides {
                            chosen = Some(di);
                            break;
                        }
                    }
                }
            }
            if let Some(t0) = lookup_t0 {
                local_lookup_ns += t0.elapsed().as_nanos() as u64;
            }

            if let Some(di) = chosen {
                let sub_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
                let (d_exps, _d_deg, _) = div_lt[di].as_ref().unwrap();
                // Read the divisor's leading coefficient lazily (only the
                // selected divisor needs it), avoiding a per-divisor clone
                // in the index build above.
                let d_lc = divisors[di].leading_coefficient().expect("nonzero divisor LC");
                let coeff_ratio = ring.field.div(&lt_coeff, d_lc).expect("nonzero divisor LC");
                let neg_coeff = ring.field.neg(&coeff_ratio);
                for k in 0..n {
                    shift[k] = lt_exps[k] - d_exps[k];
                }
                gb.sub_scaled_tail(&shift, &neg_coeff, divisors[di]);
                local_sub_scaled += 1;
                if let Some(counts) = use_counts.as_deref_mut() {
                    counts[di] = counts[di].saturating_add(1);
                }
                if let Some(t0) = sub_t0 {
                    local_sub_ns += t0.elapsed().as_nanos() as u64;
                }
            } else {
                result_exps.extend_from_slice(&lt_exps);
                result_coeffs.push(lt_coeff);
                result_degs.push(lt_deg);
            }
        }

        let fin_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
        let result = DensePoly::from_raw_sorted(result_exps, result_coeffs, result_degs);
        if let Some(t0) = fin_t0 {
            crate::profile::SPLIT_GB.time_finalize_ns
                .fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        if stats_on {
            let g = &crate::profile::SPLIT_GB;
            g.reduce_lt_pops.fetch_add(local_pops, std::sync::atomic::Ordering::Relaxed);
            g.reduce_div_lookups.fetch_add(local_lookups, std::sync::atomic::Ordering::Relaxed);
            g.reduce_sub_scaled_calls.fetch_add(local_sub_scaled, std::sync::atomic::Ordering::Relaxed);
            g.time_pop_lt_ns.fetch_add(local_pop_ns, std::sync::atomic::Ordering::Relaxed);
            g.time_div_lookup_ns.fetch_add(local_lookup_ns, std::sync::atomic::Ordering::Relaxed);
            g.time_sub_scaled_ns.fetch_add(local_sub_ns, std::sync::atomic::Ordering::Relaxed);
        }
        result
    }

    /// Reduce against a divisor set using a **prebuilt** [`ReducerIndex`]
    /// (the geobucket reducer's degree-order + DivMask-bucket lookup
    /// structure, owned so it can be cached across calls whose divisor set
    /// is unchanged). `divisors[i]` must be the divisor the index's entry
    /// `i` was built from — the leading *coefficient* is read lazily from
    /// `divisors` here, matching `reduce_by_refs_geobucket`. Result-identical
    /// to that method on a Gröbner-basis-shaped set (same first-divisor
    /// selection, same order-tolerance).
    pub fn reduce_by_refs_geobucket_indexed(
        &self,
        index: &ReducerIndex,
        divisors: &[&DensePoly],
        ring: &PolyRing,
        cancel: Option<&crate::timeout::CancelToken>,
        mut use_counts: Option<&mut [u64]>,
    ) -> DensePoly {
        let n = ring.n_vars;
        debug_assert_eq!(index.div_lt.len(), divisors.len(),
            "ReducerIndex size must match the divisor slice");
        if crate::profile::gb_stats_enabled() {
            crate::profile::SPLIT_GB.reduce_calls
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        let div_lt = &index.div_lt;
        let mut gb = crate::ff::geobucket::Geobucket::from_poly(self.clone(), ring);
        let mut result_exps: Vec<u16> = Vec::new();
        let mut result_coeffs: Vec<FieldElem> = Vec::new();
        let mut result_degs: Vec<u32> = Vec::new();
        let mut shift = vec![0u16; n];
        let mut iter_counter: u32 = 0;
        const CANCEL_CHECK_PERIOD: u32 = 4096;
        loop {
            let (lt_exps, lt_deg, lt_coeff) = match gb.pop_leading_term() {
                Some(t) => t,
                None => break,
            };
            iter_counter = iter_counter.wrapping_add(1);
            if iter_counter & (CANCEL_CHECK_PERIOD - 1) == 0 {
                if let Some(c) = cancel {
                    if c.is_cancelled() {
                        result_exps.extend_from_slice(&lt_exps);
                        result_coeffs.push(lt_coeff);
                        result_degs.push(lt_deg);
                        while let Some((e, d, c2)) = gb.pop_leading_term() {
                            result_exps.extend_from_slice(&e);
                            result_coeffs.push(c2);
                            result_degs.push(d);
                        }
                        return DensePoly::from_raw_sorted(result_exps, result_coeffs, result_degs);
                    }
                }
            }
            let cur_dm = ring.divmask.compute_from_slice(&lt_exps);
            let mut chosen: Option<usize> = None;
            if let Some(buckets) = &index.buckets {
                let cur_bits = cur_dm.0;
                'outer: for (&mask, indices) in buckets {
                    if (mask & !cur_bits) != 0 {
                        continue;
                    }
                    for &di in indices {
                        if let Some((d_exps, d_deg, _)) = &div_lt[di] {
                            if *d_deg > lt_deg { break; }
                            if d_exps.iter().zip(lt_exps.iter()).all(|(a, b)| a <= b) {
                                chosen = Some(di);
                                break 'outer;
                            }
                        }
                    }
                }
            } else if let Some(order) = &index.order {
                for &di in order {
                    if let Some((d_exps, d_deg, d_dm)) = &div_lt[di] {
                        if *d_deg > lt_deg { break; }
                        if !d_dm.divides_consistent_with(cur_dm) { continue; }
                        if d_exps.iter().zip(lt_exps.iter()).all(|(a, b)| a <= b) {
                            chosen = Some(di);
                            break;
                        }
                    }
                }
            } else {
                for (di, lt_opt) in div_lt.iter().enumerate() {
                    if let Some((d_exps, d_deg, d_dm)) = lt_opt {
                        if *d_deg > lt_deg { continue; }
                        if !d_dm.divides_consistent_with(cur_dm) { continue; }
                        if d_exps.iter().zip(lt_exps.iter()).all(|(a, b)| a <= b) {
                            chosen = Some(di);
                            break;
                        }
                    }
                }
            }
            if let Some(di) = chosen {
                let d_exps = &div_lt[di].as_ref().unwrap().0;
                let d_lc = divisors[di].leading_coefficient().expect("nonzero divisor LC");
                let coeff_ratio = ring.field.div(&lt_coeff, d_lc).expect("nonzero divisor LC");
                let neg_coeff = ring.field.neg(&coeff_ratio);
                for k in 0..n {
                    shift[k] = lt_exps[k] - d_exps[k];
                }
                gb.sub_scaled_tail(&shift, &neg_coeff, divisors[di]);
                if let Some(counts) = use_counts.as_deref_mut() {
                    counts[di] = counts[di].saturating_add(1);
                }
            } else {
                result_exps.extend_from_slice(&lt_exps);
                result_coeffs.push(lt_coeff);
                result_degs.push(lt_deg);
            }
        }
        DensePoly::from_raw_sorted(result_exps, result_coeffs, result_degs)
    }

    /// Single-vector reduction with fused `merge_sub_scaled_tail`. The
    /// cross-validation reference for the geobucket-based `reduce_by_refs`.
    pub fn reduce_by_refs_naive(&self, divisors: &[&DensePoly], ring: &PolyRing) -> DensePoly {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        let n = ring.n_vars;
        let mut current = self.clone();
        let mut cursor: usize = 0;
        let mut result_exps: Vec<u16> = Vec::new();
        let mut result_coeffs: Vec<FieldElem> = Vec::new();
        let mut result_degs: Vec<u32> = Vec::new();

        use crate::ff::divmask::DivMask;
        let div_lt: Vec<Option<(Vec<u16>, u32, FieldElem, DivMask)>> = divisors
            .iter()
            .map(|d| {
                if let Some(lt) = d.leading_term(ring) {
                    let mon = lt.monomial();
                    let dm = ring.divmask.compute(&mon);
                    Some((lt.exponents().to_vec(), lt.total_degree(), lt.coefficient().clone(), dm))
                } else {
                    None
                }
            })
            .collect();

        while cursor < current.coeffs.len() {
            let lt_exps: &[u16] = &current.exponents[cursor * n..(cursor + 1) * n];
            let lt_deg = current.total_degs[cursor];
            let cur_dm = ring.divmask.compute_from_slice(lt_exps);

            let mut chosen: Option<usize> = None;
            for (di, lt_opt) in div_lt.iter().enumerate() {
                if let Some((d_exps, d_deg, _, d_dm)) = lt_opt {
                    if *d_deg > lt_deg {
                        continue;
                    }
                    if !d_dm.divides_consistent_with(cur_dm) {
                        continue;
                    }
                    let mut divides = true;
                    for k in 0..n {
                        if d_exps[k] > lt_exps[k] {
                            divides = false;
                            break;
                        }
                    }
                    if divides {
                        chosen = Some(di);
                        break;
                    }
                }
            }

            if let Some(di) = chosen {
                let (d_exps, _d_deg, d_lc, _) = div_lt[di].as_ref().unwrap();
                let lt_coeff = &current.coeffs[cursor];
                let coeff_ratio = ring.field.div(lt_coeff, d_lc).expect("nonzero divisor LC");
                let neg_coeff = ring.field.neg(&coeff_ratio);
                let mut shift = vec![0u16; n];
                for k in 0..n {
                    shift[k] = lt_exps[k] - d_exps[k];
                }
                current = current.merge_sub_scaled_tail(
                    cursor, divisors[di], &shift, &neg_coeff, ring,
                );
                cursor = 0;
            } else {
                result_exps.extend_from_slice(&current.exponents[cursor * n..(cursor + 1) * n]);
                result_coeffs.push(current.coeffs[cursor].clone());
                result_degs.push(current.total_degs[cursor]);
                cursor += 1;
            }
        }

        DensePoly::from_raw_sorted(result_exps, result_coeffs, result_degs)
    }
}
