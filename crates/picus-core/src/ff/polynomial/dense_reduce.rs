//! Dense-polynomial Gröbner reduction: the `reduce_by_refs*` family
//! (geobucket / DivMask-indexed reducers) and the `reduce_by_refs_naive`
//! cross-check oracle, as inherent `impl DensePoly` methods. A submodule of
//! `polynomial` so these methods keep access to `DensePoly`'s private
//! fields and helpers; inherent methods need no re-export, so
//! `DensePoly::reduce_by_refs*` call sites are unchanged.

use super::*;
use crate::metric;

impl DensePoly {
    /// Like `reduce_by` but takes references to divisors — avoids cloning
    /// the divisor list when the caller already holds polynomials inside
    /// some larger container (e.g. `BuchbergerState::basis`).
    ///
    /// Geobucket-based accumulator (Yan 1998). Each reduction step is
    /// O(D · log(N / D)) where D is the divisor length and N is the
    /// running tail size.
    ///
    /// The normal form is term-for-term identical to `reduce_by_refs_naive`
    /// and to the sparse reducer only on a Gröbner-basis-shaped divisor set
    /// (at most one leading term divides any monomial). On an arbitrary
    /// non-GB set the degree-sorted / DivMask-bucketed reducer selection
    /// (enabled past `ReducerIndex::SORT_THRESHOLD`) may pick a different
    /// divisor than the linear first-match, yielding a different — but still
    /// same-coset, valid — remainder.
    pub fn reduce_by_refs(&self, divisors: &[&DensePoly], ring: &PolyRing) -> DensePoly {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, None, None, None)
    }

    /// Cancel-aware variant of [`Self::reduce_by_refs`]. On cancel, returns
    /// the partial remainder accumulated so far — sound (same residue
    /// class) but not necessarily a normal form. Hot paths (Buchberger
    /// main loop, interreduce, bit-prop `contains`) should prefer this
    /// over [`Self::reduce_by_refs`] so the cancel token is honoured on
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

    /// Variant of [`Self::reduce_by_refs_cancel`] that also records, in
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

    /// Like [`Self::reduce_by_refs_counted_cancel`] but reuses the caller's
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

    /// Non-cancel-aware version of [`Self::reduce_by_refs_counted_cancel`].
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

    /// Like [`Self::reduce_by_refs_counted`] but reuses the caller's precomputed
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

    /// Geobucket-based reduction: the shared implementation every
    /// `reduce_by_refs[_cancel|_counted|…]` wrapper forwards to (each
    /// selecting a different `(cancel, count, dms)` Option triple). Prefer
    /// the wrappers at call sites so the variant choice stays in one place.
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
        // Cached gb-stats gate: read once, used by the per-monomial timers in
        // the hot loop below without re-reading the thread-local config.
        metric::gate!(stats);
        metric::incr!(crate::profile::SPLIT_GB.reduce_calls);
        metric::stopwatch!(setup_sw);

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
        let order_opt: Option<Vec<usize>> = if div_lt.len() >= ReducerIndex::SORT_THRESHOLD {
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
        let bucket_index_opt: Option<std::collections::HashMap<u128, Vec<usize>>> =
            if div_lt.len() >= ReducerIndex::BUCKET_THRESHOLD {
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

        metric::scope! {
            let dt = setup_sw.map(|t| t.elapsed().as_nanos() as u64).unwrap_or(0);
            metric::add!(crate::profile::SPLIT_GB.time_div_lt_setup_ns, dt);
        }
        metric::def!(local_pops);
        metric::def!(local_lookups);
        metric::def!(local_sub_scaled);
        metric::def!(local_pop_ns);
        metric::def!(local_lookup_ns);
        metric::def!(local_sub_ns);

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
            let popped = {
                metric::timer_local!(stats, local_pop_ns);
                gb.pop_leading_term()
            };
            let (lt_exps, lt_deg, lt_coeff) = match popped {
                Some(t) => t,
                None => break,
            };
            metric::bump!(local_pops);
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
                        metric::scope! {
                            let g = &crate::profile::SPLIT_GB;
                            metric::add!(g.reduce_lt_pops, local_pops);
                            metric::add!(g.reduce_div_lookups, local_lookups);
                            metric::add!(g.reduce_sub_scaled_calls, local_sub_scaled);
                            metric::add!(g.time_pop_lt_ns, local_pop_ns);
                            metric::add!(g.time_div_lookup_ns, local_lookup_ns);
                            metric::add!(g.time_sub_scaled_ns, local_sub_ns);
                        }
                        return DensePoly::from_raw_sorted(result_exps, result_coeffs, result_degs);
                    }
                }
            }
            let cur_dm = ring.divmask.compute_from_slice(&lt_exps);
            let mut chosen: Option<usize> = None;
            {
            metric::timer_local!(stats, local_lookup_ns);
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
                        metric::bump!(local_lookups);
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
                    metric::bump!(local_lookups);
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
                    metric::bump!(local_lookups);
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
            }

            if let Some(di) = chosen {
                metric::timer_local!(stats, local_sub_ns);
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
                metric::bump!(local_sub_scaled);
                if let Some(counts) = use_counts.as_deref_mut() {
                    counts[di] = counts[di].saturating_add(1);
                }
            } else {
                result_exps.extend_from_slice(&lt_exps);
                result_coeffs.push(lt_coeff);
                result_degs.push(lt_deg);
            }
        }

        let result = {
            metric::timer!(crate::profile::SPLIT_GB.time_finalize_ns);
            DensePoly::from_raw_sorted(result_exps, result_coeffs, result_degs)
        };
        metric::scope! {
            let g = &crate::profile::SPLIT_GB;
            metric::add!(g.reduce_lt_pops, local_pops);
            metric::add!(g.reduce_div_lookups, local_lookups);
            metric::add!(g.reduce_sub_scaled_calls, local_sub_scaled);
            metric::add!(g.time_pop_lt_ns, local_pop_ns);
            metric::add!(g.time_div_lookup_ns, local_lookup_ns);
            metric::add!(g.time_sub_scaled_ns, local_sub_ns);
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
        metric::incr!(crate::profile::SPLIT_GB.reduce_calls);
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
