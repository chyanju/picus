//! Split-GB fixpoint loops.
//!
//! Two near-identical drivers:
//!
//! * [`split_gb_cancel`] builds a split GB from scratch — each partition
//!   starts empty and grows by [`Ideal::extend_with_cancel`] as the
//!   propagation loop emits cross-partition polynomials.
//! * [`split_gb_extend_cancel`] takes a pre-existing split GB (each
//!   partition already a reduced GB) and extends it with new generators.
//!   Used by [`super::search::split_zero_extend_cancel`] to grow each
//!   partition by one assignment polynomial per branching step.
//!
//! Each fixpoint iteration: (a) extends every partition by its pending
//! `new_polys`, (b) runs [`BitProp::get_bit_equalities_with_cancel`] to
//! derive new equalities, (c) for every emitted polynomial admitted by
//! partition `j`, tests ideal membership and either records it as
//! contained or queues it as a new generator for the next iteration. A
//! `(content_hash, basis_idx)` memo records positive containment results
//! across iterations.
//!
//! The propagation step is sound: once `p` belongs to `I_j`, no
//! subsequent extension or interreduce inside `I_j` can remove it.

use std::collections::BTreeSet;

use crate::bitprop::BitProp;
use crate::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::{CancelToken, Cancelled};
use crate::tracer::GbTracer;

use super::{admit, SplitGb};

/// Compute a split GB from scratch.
///
/// `generator_sets[i]` is the initial generator set for partition `i`.
/// On cancel, falls back to an empty split GB (one empty `Ideal` per
/// partition).
pub fn split_gb<'r>(
    poly_ring: &'r FfPolyRing,
    generator_sets: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
) -> SplitGb<'r> {
    let k = generator_sets.len();
    split_gb_cancel(poly_ring, generator_sets, bit_prop, &CancelToken::none())
        .unwrap_or_else(|_| {
            (0..k).map(|_| Ideal::from_gb(poly_ring, Vec::new())).collect()
        })
}

/// Cancel-aware split GB computation.
pub fn split_gb_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    generator_sets: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<SplitGb<'r>, Cancelled> {
    let _t = crate::profile::ScopedTimer::new("split_gb_cancel");
    let stats_on = crate::profile::gb_stats_enabled();
    let trace_on = crate::profile::gb_trace_enabled();
    let call_idx = if stats_on {
        crate::profile::SPLIT_GB.split_gb_extend_calls
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1
    } else { 0 };
    let k = generator_sets.len();
    let starting: SplitGb<'r> = (0..k)
        .map(|_| Ideal::from_gb(poly_ring, Vec::new()))
        .collect();
    run_fixpoint(
        poly_ring, starting, generator_sets, bit_prop, cancel,
        "split_gb_cancel", "split-gb-cancel-trace", call_idx,
        stats_on, trace_on,
    )
}

/// Incremental version of [`split_gb_cancel`].
///
/// Takes a pre-existing split GB (whose partitions are already reduced
/// GBs) plus per-partition `new_polys`, and runs the same bit-prop
/// fixpoint using [`Ideal::extend_with_cancel`] instead of full GB
/// recomputes. Equivalent to a full recomputation on the union of
/// generators.
pub(crate) fn split_gb_extend_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    starting: SplitGb<'r>,
    new_polys: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<SplitGb<'r>, Cancelled> {
    let _t = crate::profile::ScopedTimer::new("split_gb_extend_cancel");
    let stats_on = crate::profile::gb_stats_enabled();
    let trace_on = crate::profile::gb_trace_enabled();
    let call_idx = if stats_on {
        crate::profile::SPLIT_GB.split_gb_extend_calls
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1
    } else { 0 };
    debug_assert_eq!(starting.len(), new_polys.len(),
        "split_gb_extend_cancel: starting and new_polys must have same length");
    run_fixpoint(
        poly_ring, starting, new_polys, bit_prop, cancel,
        "split_gb_extend_cancel", "split-gb-trace", call_idx,
        stats_on, trace_on,
    )
}

/// Shared fixpoint body for [`split_gb_cancel`] and
/// [`split_gb_extend_cancel`]. The only difference between the two
/// entry points is whether `starting` is empty and whether `new_polys`
/// represents original inputs or incremental additions; the loop body
/// is identical.
fn run_fixpoint<'r>(
    poly_ring: &'r FfPolyRing,
    starting: SplitGb<'r>,
    new_polys: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
    fn_name: &'static str,
    trace_tag: &'static str,
    call_idx: u64,
    stats_on: bool,
    trace_on: bool,
) -> Result<SplitGb<'r>, Cancelled> {
    use std::sync::atomic::Ordering::Relaxed;

    let k = starting.len();
    let mut split_basis: SplitGb<'r> = starting;
    let mut new_polys: Vec<Vec<Poly>> = new_polys;

    // Cross-iteration memoisation of positive `contains` results.
    // Key: `(content_hash(p), basis_idx)`. Sound because once `p in
    // I_j` holds, `extend_with_cancel` and `interreduce_basis` only
    // add or rewrite generators within the same ideal — they cannot
    // remove `p` from the ideal.
    let mut contains_memo: std::collections::HashSet<(u64, usize)> =
        std::collections::HashSet::new();

    // Safety bound against pathological propagation loops on degenerate
    // inputs. The cancel token would also bound the loop; this cap
    // produces a deterministic exit independent of wall time.
    let max_fixpoint_iters = (k * 64).max(256);
    let mut fixpoint_iter: u64 = 0;

    loop {
        if cancel.is_cancelled() { return Err(Cancelled); }
        fixpoint_iter += 1;
        if fixpoint_iter > max_fixpoint_iters as u64 {
            log::warn!("{}: fixpoint iteration cap ({}) reached", fn_name, max_fixpoint_iters);
            break;
        }
        let iter_t0 = if trace_on { Some(std::time::Instant::now()) } else { None };

        // Extend each basis with its new polys via incremental Buchberger.
        let extend_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
        let mut iter_polys_in: u64 = 0;
        for i in 0..k {
            if !new_polys[i].is_empty() {
                iter_polys_in += new_polys[i].len() as u64;
                let added = std::mem::take(&mut new_polys[i]);
                let existing = std::mem::replace(
                    &mut split_basis[i],
                    Ideal::from_gb(poly_ring, Vec::new()),
                );
                split_basis[i] = existing.extend_with_cancel(added, cancel)?;
            }
        }
        if let Some(t0) = extend_t0 {
            let dt = t0.elapsed().as_nanos() as u64;
            crate::profile::SPLIT_GB.time_in_extend_with_cancel_ns
                .fetch_add(dt, Relaxed);
        }

        if stats_on {
            let g = &crate::profile::SPLIT_GB;
            g.fixpoint_iters_total.fetch_add(1, Relaxed);
            let mut max_basis = 0u64;
            let mut total_terms = 0u64;
            for b in &split_basis {
                let len = b.basis.len() as u64;
                if len > max_basis { max_basis = len; }
                for p in &b.basis {
                    total_terms += p.num_terms() as u64;
                }
            }
            g.observe_basis_size_max(max_basis);
            g.observe_basis_terms_max(total_terms);
        }

        if split_basis.iter().any(|b| b.is_whole_ring()) {
            break;
        }

        // Seed the memo with self-membership: every poly in basis j is
        // trivially `contains(p, j) = true`.
        for j in 0..k {
            for p in &split_basis[j].basis {
                contains_memo.insert((p.content_hash(), j));
            }
        }

        let bit_eq_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
        let mut to_propagate =
            bit_prop.get_bit_equalities_with_cancel(&split_basis, Some(cancel));
        if let Some(t0) = bit_eq_t0 {
            let dt = t0.elapsed().as_nanos() as u64;
            crate::profile::SPLIT_GB.time_in_bit_eq_ns.fetch_add(dt, Relaxed);
            crate::profile::SPLIT_GB.bit_eq_emitted_total
                .fetch_add(to_propagate.len() as u64, Relaxed);
        }
        if cancel.is_cancelled() { return Err(Cancelled); }
        for b in &split_basis {
            for p in &b.basis {
                to_propagate.push(poly_ring.ring.clone_el(p));
            }
        }

        let mut iter_contains_calls: u64 = 0;
        let mut iter_contains_true: u64 = 0;
        let mut iter_memo_hits: u64 = 0;
        let mut iter_polys_out: u64 = 0;
        let contains_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
        let mut any_new = false;
        for p in &to_propagate {
            if cancel.is_cancelled() { return Err(Cancelled); }
            let p_hash = p.content_hash();
            for j in 0..k {
                if admit(poly_ring, j, p) {
                    if stats_on {
                        crate::profile::SPLIT_GB.propagate_admit_passes
                            .fetch_add(1, Relaxed);
                    }
                    let key = (p_hash, j);
                    if contains_memo.contains(&key) {
                        iter_memo_hits += 1;
                        continue;
                    }
                    let in_basis = split_basis[j].contains_with_cancel(p, cancel);
                    iter_contains_calls += 1;
                    if in_basis {
                        iter_contains_true += 1;
                        contains_memo.insert(key);
                    } else {
                        new_polys[j].push(poly_ring.ring.clone_el(p));
                        iter_polys_out += 1;
                        any_new = true;
                        // Pre-record: after the next iteration's
                        // `extend_with_cancel`, p will be in basis j.
                        contains_memo.insert(key);
                    }
                }
            }
        }
        if let Some(t0) = contains_t0 {
            let dt = t0.elapsed().as_nanos() as u64;
            let g = &crate::profile::SPLIT_GB;
            g.time_in_contains_ns.fetch_add(dt, Relaxed);
            g.propagate_candidates_total
                .fetch_add(to_propagate.len() as u64, Relaxed);
            g.propagate_contains_calls.fetch_add(iter_contains_calls, Relaxed);
            g.propagate_contains_true.fetch_add(iter_contains_true, Relaxed);
            g.propagate_contains_false
                .fetch_add(iter_contains_calls - iter_contains_true, Relaxed);
            g.propagate_memo_hits.fetch_add(iter_memo_hits, Relaxed);
            g.new_polys_added_total.fetch_add(iter_polys_out, Relaxed);
            g.observe_polys_per_iter_max(iter_polys_out);
        }

        if let Some(t0) = iter_t0 {
            let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
            let basis_sizes: Vec<usize> = split_basis.iter().map(|b| b.basis.len()).collect();
            eprintln!(
                "[{} call={} iter={}] basis_sizes={:?} polys_in={} polys_out={} contains={} contains_true={} memo_hits={} elapsed_ms={:.2}",
                trace_tag, call_idx, fixpoint_iter, basis_sizes,
                iter_polys_in, iter_polys_out,
                iter_contains_calls, iter_contains_true, iter_memo_hits,
                elapsed_ms,
            );
        }

        if !any_new { break; }
    }

    if stats_on {
        crate::profile::SPLIT_GB.observe_iters_max(fixpoint_iter);
    }

    Ok(split_basis)
}

/// Result of [`split_gb_cancel_traced`]: the split basis plus, when
/// some partition became the whole ring during fixpoint, the precise
/// UNSAT core (a subset of original input indices).
pub struct TracedSplitGb<'r> {
    pub split_basis: SplitGb<'r>,
    /// `Some(core)` if a partition was reduced to the whole ring at
    /// some point and the trivial element's dependency set could be
    /// extracted. `None` if the split-GB terminated without UNSAT or
    /// if the tracer could not pinpoint a constant element.
    pub unsat_core: Option<Vec<usize>>,
}

/// Cancel-aware split GB computation **with per-polynomial dependency
/// tracking** for non-trivial UNSAT core extraction.
///
/// `initial_deps[k][i]` is the set of original input indices that
/// `generator_sets[k][i]` depends on. Inputs that should not contribute
/// to the user-facing UNSAT core (e.g. encoder-introduced bitsum
/// definitions) should have an empty dep set.
pub fn split_gb_cancel_traced<'r>(
    poly_ring: &'r FfPolyRing,
    generator_sets: Vec<Vec<Poly>>,
    initial_deps: Vec<Vec<BTreeSet<usize>>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<TracedSplitGb<'r>, Cancelled> {
    let _t = crate::profile::ScopedTimer::new("split_gb_cancel_traced");
    debug_assert_eq!(generator_sets.len(), initial_deps.len());
    for (gens, deps) in generator_sets.iter().zip(initial_deps.iter()) {
        debug_assert_eq!(gens.len(), deps.len());
    }
    let k = generator_sets.len();
    let starting: SplitGb<'r> = (0..k).map(|_| Ideal::from_gb(poly_ring, Vec::new())).collect();
    let starting_deps: Vec<Vec<BTreeSet<usize>>> = (0..k).map(|_| Vec::new()).collect();
    run_fixpoint_traced(
        poly_ring, starting, starting_deps, generator_sets, initial_deps, bit_prop, cancel,
    )
}

/// Traced variant of [`run_fixpoint`]. Mirrors the same fixpoint
/// structure but uses [`Ideal::extend_with_cancel_traced`] for each
/// per-partition extension and maintains a parallel
/// `basis_deps[k][i] -> BTreeSet<usize>` mapping each active basis
/// element to the union of original input indices it depends on.
/// Cross-partition propagations carry their source partition's per-poly
/// dep set forward, so by the time any partition becomes whole-ring,
/// the constant element's deps name a precise UNSAT core in the
/// original input numbering.
fn run_fixpoint_traced<'r>(
    poly_ring: &'r FfPolyRing,
    starting: SplitGb<'r>,
    starting_deps: Vec<Vec<BTreeSet<usize>>>,
    initial_new_polys: Vec<Vec<Poly>>,
    initial_new_deps: Vec<Vec<BTreeSet<usize>>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<TracedSplitGb<'r>, Cancelled> {
    let k = starting.len();
    let mut split_basis: SplitGb<'r> = starting;
    let mut basis_deps: Vec<Vec<BTreeSet<usize>>> = starting_deps;
    let mut new_polys: Vec<Vec<Poly>> = initial_new_polys;
    let mut new_polys_deps: Vec<Vec<BTreeSet<usize>>> = initial_new_deps;

    let mut contains_memo: std::collections::HashSet<(u64, usize)> =
        std::collections::HashSet::new();

    let max_fixpoint_iters = (k * 64).max(256);
    let mut fixpoint_iter: u64 = 0;

    loop {
        if cancel.is_cancelled() {
            return Err(Cancelled);
        }
        fixpoint_iter += 1;
        if fixpoint_iter > max_fixpoint_iters as u64 {
            break;
        }

        for i in 0..k {
            if new_polys[i].is_empty() {
                continue;
            }
            debug_assert_eq!(new_polys[i].len(), new_polys_deps[i].len());

            let existing_basis_len = split_basis[i].basis.len();
            let n_new = new_polys[i].len();
            let n_inputs = existing_basis_len + n_new;
            let mut tracer = GbTracer::new(n_inputs);

            let mut tracer_input_to_orig: Vec<BTreeSet<usize>> =
                Vec::with_capacity(n_inputs);
            tracer_input_to_orig.extend(basis_deps[i].iter().cloned());
            tracer_input_to_orig.extend(new_polys_deps[i].drain(..));

            let added = std::mem::take(&mut new_polys[i]);
            let existing = std::mem::replace(
                &mut split_basis[i],
                Ideal::from_gb(poly_ring, Vec::new()),
            );
            let extended = existing.extend_with_cancel_traced(added, cancel, &mut tracer)?;
            split_basis[i] = extended;

            if split_basis[i].is_whole_ring() {
                // Buchberger compacts the basis to `[1]` on trivial abort;
                // the contradiction polynomial is the last entry pushed
                // into the tracer (same indexing as `gb::compute_gb_with_timeout_traced`).
                let last_idx = tracer.basis_count();
                let tcis: Vec<usize> = if last_idx == 0 {
                    Vec::new()
                } else {
                    tracer.unsat_core_for(last_idx - 1)
                };
                let mut s: BTreeSet<usize> = BTreeSet::new();
                for ti in tcis {
                    if let Some(d) = tracer_input_to_orig.get(ti) {
                        s.extend(d.iter().copied());
                    }
                }
                let orig_core = if s.is_empty() {
                    None
                } else {
                    Some(s.into_iter().collect::<Vec<usize>>())
                };
                return Ok(TracedSplitGb {
                    split_basis,
                    unsat_core: orig_core,
                });
            }

            let new_basis_len = split_basis[i].basis.len();
            let mut new_basis_deps: Vec<BTreeSet<usize>> = Vec::with_capacity(new_basis_len);
            for bidx in 0..new_basis_len {
                let mut s: BTreeSet<usize> = BTreeSet::new();
                match tracer.deps_of(bidx) {
                    Some(tcis) => {
                        for &ti in tcis {
                            if let Some(d) = tracer_input_to_orig.get(ti) {
                                s.extend(d.iter().copied());
                            }
                        }
                    }
                    None => {
                        for d in &tracer_input_to_orig {
                            s.extend(d.iter().copied());
                        }
                    }
                }
                new_basis_deps.push(s);
            }
            basis_deps[i] = new_basis_deps;
        }

        if split_basis.iter().any(|b| b.is_whole_ring()) {
            break;
        }

        for j in 0..k {
            for p in &split_basis[j].basis {
                contains_memo.insert((p.content_hash(), j));
            }
        }

        let bit_eqs = bit_prop.get_bit_equalities_with_cancel(&split_basis, Some(cancel));
        if cancel.is_cancelled() {
            return Err(Cancelled);
        }

        // A derived bit equality depends on (a) the bitsum that
        // reduced to a constant, (b) every basis element used in that
        // reduction, and (c) the bit constraints on the participating
        // variables. `BitProp` does not record those contributors
        // individually, so each bit equality is conservatively attributed
        // to the union of deps across all current basis elements.
        let bit_eq_deps: BTreeSet<usize> = basis_deps
            .iter()
            .flat_map(|bd| bd.iter())
            .flat_map(|s| s.iter().copied())
            .collect();
        let mut to_propagate: Vec<(Poly, BTreeSet<usize>)> = Vec::new();
        for p in bit_eqs {
            to_propagate.push((p, bit_eq_deps.clone()));
        }
        for j in 0..k {
            for (idx, p) in split_basis[j].basis.iter().enumerate() {
                let deps = basis_deps[j].get(idx).cloned().unwrap_or_default();
                to_propagate.push((poly_ring.ring.clone_el(p), deps));
            }
        }

        let mut any_new = false;
        for (p, p_deps) in &to_propagate {
            if cancel.is_cancelled() {
                return Err(Cancelled);
            }
            let p_hash = p.content_hash();
            for j in 0..k {
                if admit(poly_ring, j, p) {
                    let key = (p_hash, j);
                    if contains_memo.contains(&key) {
                        continue;
                    }
                    if split_basis[j].contains_with_cancel(p, cancel) {
                        contains_memo.insert(key);
                    } else {
                        new_polys[j].push(poly_ring.ring.clone_el(p));
                        new_polys_deps[j].push(p_deps.clone());
                        any_new = true;
                        contains_memo.insert(key);
                    }
                }
            }
        }

        if !any_new {
            break;
        }
    }

    Ok(TracedSplitGb {
        split_basis,
        unsat_core: None,
    })
}
