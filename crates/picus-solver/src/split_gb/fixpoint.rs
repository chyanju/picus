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

use crate::frontend::bitprop::BitProp;
use crate::gb::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::{CancelToken, Cancelled};
use crate::gb::tracer::GbTracer;

use super::{classify_propagation, max_fixpoint_iters, seed_self_membership, Propagate, SplitGb};
use crate::metric;
use crate::profile::SPLIT_GB;

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
#[metric]
pub fn split_gb_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    generator_sets: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<SplitGb<'r>, Cancelled> {
    let k = generator_sets.len();
    let starting: SplitGb<'r> = (0..k)
        .map(|_| Ideal::from_gb(poly_ring, Vec::new()))
        .collect();
    run_fixpoint(
        poly_ring, starting, generator_sets, bit_prop, cancel,
        "split_gb_cancel", "split-gb-cancel-trace",
    )
}

/// Incremental version of [`split_gb_cancel`].
///
/// Takes a pre-existing split GB (whose partitions are already reduced
/// GBs) plus per-partition `new_polys`, and runs the same bit-prop
/// fixpoint using [`Ideal::extend_with_cancel`] instead of full GB
/// recomputes. Equivalent to a full recomputation on the union of
/// generators.
#[metric]
pub(crate) fn split_gb_extend_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    starting: SplitGb<'r>,
    new_polys: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<SplitGb<'r>, Cancelled> {
    debug_assert_eq!(starting.len(), new_polys.len(),
        "split_gb_extend_cancel: starting and new_polys must have same length");
    run_fixpoint(
        poly_ring, starting, new_polys, bit_prop, cancel,
        "split_gb_extend_cancel", "split-gb-trace",
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
) -> Result<SplitGb<'r>, Cancelled> {
    let k = starting.len();
    let mut split_basis: SplitGb<'r> = starting;
    let mut new_polys: Vec<Vec<Poly>> = new_polys;

    // Per-call sequence id for the trace tag (post-increment of the shared
    // call counter; 0 when metrics are disabled).
    metric::def!(call_idx = metric::next!(SPLIT_GB.split_gb_extend_calls));

    // Cross-iteration memoisation of positive `contains` results.
    // Key: `(content_hash(p), basis_idx)`. Sound because once `p in
    // I_j` holds, `extend_with_cancel` and `interreduce_basis` only
    // add or rewrite generators within the same ideal — they cannot
    // remove `p` from the ideal.
    let mut contains_memo: std::collections::HashSet<(u64, usize)> =
        std::collections::HashSet::new();

    let iter_cap = max_fixpoint_iters(k);
    let mut fixpoint_iter: u64 = 0;

    loop {
        if cancel.is_cancelled() { return Err(Cancelled); }
        fixpoint_iter += 1;
        if fixpoint_iter > iter_cap {
            log::warn!("{}: fixpoint iteration cap ({}) reached", fn_name, iter_cap);
            break;
        }
        metric::clock!(iter_clock);

        // Extend each basis with its new polys via incremental Buchberger.
        metric::def!(iter_polys_in);
        {
            metric::timer!(SPLIT_GB.time_in_extend_with_cancel_ns);
            for i in 0..k {
                if !new_polys[i].is_empty() {
                    metric::bump!(iter_polys_in, new_polys[i].len() as u64);
                    let added = std::mem::take(&mut new_polys[i]);
                    let existing = std::mem::replace(
                        &mut split_basis[i],
                        Ideal::from_gb(poly_ring, Vec::new()),
                    );
                    split_basis[i] = existing.extend_with_cancel(added, cancel)?;
                }
            }
        }

        metric::scope! {
            metric::incr!(SPLIT_GB.fixpoint_iters_total);
            let mut max_basis = 0u64;
            let mut total_terms = 0u64;
            for b in &split_basis {
                let len = b.basis.len() as u64;
                if len > max_basis { max_basis = len; }
                for p in &b.basis {
                    total_terms += p.num_terms() as u64;
                }
            }
            metric::max!(SPLIT_GB.basis_size_max, max_basis);
            metric::max!(SPLIT_GB.basis_size_total_terms_max, total_terms);
        }

        if split_basis.iter().any(|b| b.is_whole_ring()) {
            break;
        }

        // Seed the memo with self-membership: every poly in basis j is
        // trivially `contains(p, j) = true`.
        seed_self_membership(&mut contains_memo, &split_basis);

        let mut to_propagate = {
            metric::timer!(SPLIT_GB.time_in_bit_eq_ns);
            bit_prop.get_bit_equalities_with_cancel(&split_basis, Some(cancel))
        };
        metric::add!(SPLIT_GB.bit_eq_emitted_total, to_propagate.len() as u64);
        if cancel.is_cancelled() { return Err(Cancelled); }
        for b in &split_basis {
            for p in &b.basis {
                to_propagate.push(poly_ring.ring.clone_el(p));
            }
        }

        // Per-iteration accumulators consumed by both the per-iter aggregate
        // below and the trace line. Local to this loop iteration.
        metric::def!(iter_contains_calls);
        metric::def!(iter_contains_true);
        metric::def!(iter_memo_hits);
        metric::def!(iter_polys_out);
        metric::def!(iter_admit_passes);
        let mut any_new = false;
        {
            metric::timer!(SPLIT_GB.time_in_contains_ns);
            for p in &to_propagate {
                if cancel.is_cancelled() { return Err(Cancelled); }
                let p_hash = p.content_hash();
                for j in 0..k {
                    let outcome = classify_propagation(
                        poly_ring, &split_basis[j], j, p, p_hash, &mut contains_memo, cancel,
                    );
                    if outcome != Propagate::NotAdmitted {
                        metric::bump!(iter_admit_passes);
                    }
                    match outcome {
                        Propagate::NotAdmitted => {}
                        Propagate::MemoHit => { metric::bump!(iter_memo_hits); }
                        Propagate::InBasis => {
                            metric::bump!(iter_contains_calls);
                            metric::bump!(iter_contains_true);
                        }
                        Propagate::NewGenerator => {
                            metric::bump!(iter_contains_calls);
                            new_polys[j].push(poly_ring.ring.clone_el(p));
                            metric::bump!(iter_polys_out);
                            any_new = true;
                        }
                    }
                }
            }
        }
        metric::scope! {
            metric::add!(SPLIT_GB.propagate_admit_passes, iter_admit_passes);
            metric::add!(SPLIT_GB.propagate_candidates_total, to_propagate.len() as u64);
            metric::add!(SPLIT_GB.propagate_contains_calls, iter_contains_calls);
            metric::add!(SPLIT_GB.propagate_contains_true, iter_contains_true);
            metric::add!(SPLIT_GB.propagate_contains_false, iter_contains_calls - iter_contains_true);
            metric::add!(SPLIT_GB.propagate_memo_hits, iter_memo_hits);
            metric::add!(SPLIT_GB.new_polys_added_total, iter_polys_out);
            metric::max!(SPLIT_GB.new_polys_per_iter_max, iter_polys_out);
        }

        metric::trace! {
            let elapsed_ms = iter_clock.map(|t| t.elapsed().as_secs_f64() * 1000.0).unwrap_or(0.0);
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

    metric::max!(SPLIT_GB.fixpoint_iters_per_call_max, fixpoint_iter);

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
#[metric]
pub fn split_gb_cancel_traced<'r>(
    poly_ring: &'r FfPolyRing,
    generator_sets: Vec<Vec<Poly>>,
    initial_deps: Vec<Vec<BTreeSet<usize>>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<TracedSplitGb<'r>, Cancelled> {
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

    let iter_cap = max_fixpoint_iters(k);
    let mut fixpoint_iter: u64 = 0;

    loop {
        if cancel.is_cancelled() {
            return Err(Cancelled);
        }
        fixpoint_iter += 1;
        if fixpoint_iter > iter_cap {
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

            // Conservative dependency attribution (sound super-set).
            //
            // Every surviving basis element — and any extracted core — is
            // attributed the union of all original inputs that fed this
            // partition's extend. A per-index read would be unsound: the
            // tracer's `deps` are keyed by Buchberger push order, but the
            // returned basis is `active_polys()` — a compacted subsequence
            // (deactivated elements stay in the engine's vector but drop out of
            // the active list), and a batched new generator that reduces to
            // zero never gets a tracer input slot at all. Either break a
            // positional `deps_of(bidx)` / `tracer_input_to_orig[ti]`
            // correspondence, so a per-index read could attribute a *smaller*
            // dep set than the element truly has — an under-approximation,
            // yielding an unsound (too-small) UNSAT core that could drop a
            // needed generator and produce a wrong UNSAT in CDCL(T). The union
            // is a sound super-set: it can only widen the CDCL(T) conflict
            // clause, never flip a verdict. The default conjunctive path
            // discards the core entirely in the native_ff backend, so the
            // precision cost lands only on the CDCL(T)/disjunction path.
            let all_input_deps: BTreeSet<usize> = tracer_input_to_orig
                .iter()
                .flat_map(|d| d.iter().copied())
                .collect();

            if split_basis[i].is_whole_ring() {
                let orig_core = if all_input_deps.is_empty() {
                    None
                } else {
                    Some(all_input_deps.iter().copied().collect::<Vec<usize>>())
                };
                return Ok(TracedSplitGb {
                    split_basis,
                    unsat_core: orig_core,
                });
            }

            let new_basis_len = split_basis[i].basis.len();
            basis_deps[i] = vec![all_input_deps; new_basis_len];
        }

        if split_basis.iter().any(|b| b.is_whole_ring()) {
            break;
        }

        seed_self_membership(&mut contains_memo, &split_basis);

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
                if classify_propagation(
                    poly_ring, &split_basis[j], j, p, p_hash, &mut contains_memo, cancel,
                ) == Propagate::NewGenerator {
                    new_polys[j].push(poly_ring.ring.clone_el(p));
                    new_polys_deps[j].push(p_deps.clone());
                    any_new = true;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use num_bigint::BigUint;

    fn pr_one_var() -> FfPolyRing {
        FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()])
    }

    fn pr_two_vars() -> FfPolyRing {
        FfPolyRing::new(
            PrimeField::new(BigUint::from(7u32)),
            vec!["x".into(), "y".into()],
        )
    }

    // ─────── split_gb (fallback wrapper around split_gb_cancel) ───────

    #[test]
    fn split_gb_with_empty_generators_yields_per_partition_empty_basis() {
        let pr = pr_one_var();
        let generator_sets: Vec<Vec<Poly>> = vec![vec![], vec![]];
        let mut bp = BitProp::new(&pr);
        let split = split_gb(&pr, generator_sets, &mut bp);
        assert_eq!(split.len(), 2);
        for ideal in &split {
            assert!(ideal.basis.is_empty(), "partition basis should be empty");
        }
    }

    // ─────── split_gb_cancel ───────

    #[test]
    fn split_gb_cancel_pre_cancelled_returns_err() {
        let pr = pr_one_var();
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::cancelled();
        let out = split_gb_cancel(&pr, vec![vec![]], &mut bp, &cancel);
        assert!(matches!(out, Err(Cancelled)));
    }

    #[test]
    fn split_gb_cancel_with_consistent_input_keeps_generator_in_basis() {
        // [x - 3] is already a singleton GB; fixpoint should converge
        // without growth and the partition basis should contain it.
        let pr = pr_one_var();
        let f = pr.field();
        let p = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::none();
        let split = split_gb_cancel(&pr, vec![vec![p]], &mut bp, &cancel)
            .expect("not cancelled");
        assert_eq!(split.len(), 1);
        assert!(!split[0].basis.is_empty());
        assert!(!split[0].is_whole_ring(), "consistent system is not whole ring");
    }

    #[test]
    fn split_gb_cancel_inconsistent_input_yields_whole_ring() {
        // [x - 1, x - 2] → S-poly = 1, ideal = whole ring.
        let pr = pr_one_var();
        let f = pr.field();
        let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
        let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::none();
        let split = split_gb_cancel(&pr, vec![vec![p1, p2]], &mut bp, &cancel)
            .expect("not cancelled");
        assert!(split[0].is_whole_ring());
    }

    // ─────── split_gb_extend_cancel ───────

    #[test]
    fn split_gb_extend_cancel_from_empty_matches_from_scratch_via_split_gb_cancel() {
        // Both entry points should produce the same final basis when
        // `starting` is empty and `new_polys` is the original input.
        let pr = pr_one_var();
        let f = pr.field();
        let make_input = || vec![vec![pr.sub(pr.var(0), pr.constant(f.from_int(4)))]];

        let mut bp1 = BitProp::new(&pr);
        let from_scratch = split_gb_cancel(&pr, make_input(), &mut bp1, &CancelToken::none())
            .expect("not cancelled");

        let starting: SplitGb = vec![Ideal::from_gb(&pr, vec![])];
        let mut bp2 = BitProp::new(&pr);
        let extended = split_gb_extend_cancel(
            &pr, starting, make_input(), &mut bp2, &CancelToken::none(),
        ).expect("not cancelled");

        assert_eq!(from_scratch.len(), extended.len());
        assert_eq!(from_scratch[0].basis.len(), extended[0].basis.len());
    }

    #[test]
    fn split_gb_extend_cancel_with_empty_new_polys_is_noop() {
        let pr = pr_one_var();
        let f = pr.field();
        let seed = pr.sub(pr.var(0), pr.constant(f.from_int(5)));
        let starting: SplitGb = vec![Ideal::from_gb(&pr, vec![seed])];
        let starting_len = starting[0].basis.len();
        let mut bp = BitProp::new(&pr);
        let out = split_gb_extend_cancel(
            &pr, starting, vec![vec![]], &mut bp, &CancelToken::none(),
        ).expect("not cancelled");
        assert_eq!(out[0].basis.len(), starting_len);
    }

    #[test]
    fn split_gb_extend_cancel_pre_cancelled_returns_err() {
        let pr = pr_one_var();
        let starting: SplitGb = vec![Ideal::from_gb(&pr, vec![])];
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::cancelled();
        let out = split_gb_extend_cancel(&pr, starting, vec![vec![]], &mut bp, &cancel);
        assert!(matches!(out, Err(Cancelled)));
    }

    // ─────── split_gb_cancel_traced ───────

    #[test]
    fn split_gb_cancel_traced_consistent_returns_no_core() {
        let pr = pr_two_vars();
        let f = pr.field();
        // x - 3, y - 4: independent assignments, consistent.
        let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
        let p2 = pr.sub(pr.var(1), pr.constant(f.from_int(4)));
        let gens = vec![vec![p1, p2]];
        let deps: Vec<Vec<BTreeSet<usize>>> = vec![vec![
            [0].iter().copied().collect(),
            [1].iter().copied().collect(),
        ]];
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::none();
        let out = split_gb_cancel_traced(&pr, gens, deps, &mut bp, &cancel)
            .expect("not cancelled");
        assert!(out.unsat_core.is_none(), "consistent system → no core");
        assert!(!out.split_basis[0].is_whole_ring());
    }

    #[test]
    fn split_gb_cancel_traced_inconsistent_with_deps_returns_core() {
        // [x - 1, x - 2] → whole ring; deps name original input indices.
        let pr = pr_one_var();
        let f = pr.field();
        let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
        let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
        let gens = vec![vec![p1, p2]];
        let deps: Vec<Vec<BTreeSet<usize>>> = vec![vec![
            [0].iter().copied().collect(),
            [1].iter().copied().collect(),
        ]];
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::none();
        let out = split_gb_cancel_traced(&pr, gens, deps, &mut bp, &cancel)
            .expect("not cancelled");
        let core = out.unsat_core.expect("inconsistent → core extracted");
        // Conservative super-set: must mention both contributing inputs.
        assert!(core.contains(&0));
        assert!(core.contains(&1));
    }

    #[test]
    fn split_gb_cancel_traced_inconsistent_empty_deps_returns_none_core() {
        // Inconsistent system but every input is dep-free (encoder-internal):
        // `all_input_deps` is empty → tracer returns `unsat_core = None`.
        let pr = pr_one_var();
        let f = pr.field();
        let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
        let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
        let gens = vec![vec![p1, p2]];
        let deps: Vec<Vec<BTreeSet<usize>>> = vec![vec![BTreeSet::new(), BTreeSet::new()]];
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::none();
        let out = split_gb_cancel_traced(&pr, gens, deps, &mut bp, &cancel)
            .expect("not cancelled");
        assert!(out.split_basis[0].is_whole_ring());
        assert!(out.unsat_core.is_none(),
            "empty-dep inputs leave the core unattributable");
    }

    #[test]
    fn split_gb_cancel_traced_pre_cancelled_returns_err() {
        let pr = pr_one_var();
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::cancelled();
        let out = split_gb_cancel_traced(&pr, vec![vec![]], vec![vec![]], &mut bp, &cancel);
        assert!(matches!(out, Err(Cancelled)));
    }
}
