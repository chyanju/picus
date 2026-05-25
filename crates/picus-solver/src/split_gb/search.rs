//! Stack-based DFS over partial assignments that extends a [`SplitGb`]
//! to a complete model. Used by [`super::split_find_zero_cancel`] as the
//! inner search loop.
//!
//! Each iteration picks the next candidate `(var, val)` from the current
//! frame's [`Brancher`], computes the augmented split-GB via
//! [`super::fixpoint::split_gb_extend_cancel`], and pushes / pops frames
//! based on the outcome. Two pruning aids reduce redundant work:
//!
//! * **Phase saving** — the most recent value tried for a variable is
//!   reordered to the front of any future [`Brancher::Roots`] list for
//!   the same variable.
//! * **Nogood cache** — partial assignments proved infeasible are stored
//!   as `BTreeMap<usize, FieldElem>`s; a new candidate whose assignment is a
//!   superset of any stored nogood is rejected without GB work.

use std::collections::{BTreeMap, HashMap};

use crate::bitprop::BitProp;
use crate::brancher::Brancher;
use crate::ff::field::{FieldElem, PrimeField};
use crate::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;

use super::branching::apply_rule_multi;
use super::fixpoint::split_gb_extend_cancel;
use super::{PartialPoint, SplitGb, ZeroExtendResult};

/// Try to extend `cur_r` into a complete zero of the ideal whose generators
/// are `orig_polys`.
pub fn split_zero_extend<'r>(
    poly_ring: &'r FfPolyRing,
    orig_polys: &[Poly],
    cur_bases: SplitGb<'r>,
    cur_r: PartialPoint,
    bit_prop: &mut BitProp<'r>,
) -> ZeroExtendResult {
    split_zero_extend_cancel(poly_ring, orig_polys, cur_bases, cur_r, bit_prop, &CancelToken::none())
}

/// Cancel-aware version of [`split_zero_extend`].
///
/// Uses an explicit stack instead of recursion to avoid stack overflow
/// on deep searches. See the module docs for the phase-saving and
/// nogood-cache pruning aids.
pub fn split_zero_extend_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    orig_polys: &[Poly],
    initial_bases: SplitGb<'r>,
    initial_r: PartialPoint,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> ZeroExtendResult {
    let _t = crate::profile::ScopedTimer::new("split_zero_extend_cancel");
    let stats_on = crate::profile::gb_stats_enabled();
    if stats_on {
        crate::profile::SPLIT_DFS.split_zero_extend_calls
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
    // Each stack frame holds: (bases, partial_assignment, brancher)
    struct Frame<'r> {
        bases: SplitGb<'r>,
        r: PartialPoint,
        candidates: Brancher,
        /// `(var, val)` of the most recently attempted candidate from
        /// `candidates`. Used to feed `saved_phase` on backtrack.
        last_tried: Option<(usize, FieldElem)>,
    }

    // `saved_phase[v]` is the most recently popped value of variable `v`
    // across the whole search. When a future `Brancher::Roots` produces
    // candidates for `v`, the saved value is moved to the back of the
    // `Vec` so `Vec::pop` (Brancher::Roots semantics) tries it first.
    let mut saved_phase: HashMap<usize, FieldElem> = HashMap::new();

    // `nogoods` records partial assignments proved infeasible. Each
    // entry is the minimal prefix that triggered the infeasibility:
    // the path from the root plus the failing decision. A new candidate
    // is skipped if its partial assignment is a superset of any stored
    // nogood.
    let mut nogoods: Vec<BTreeMap<usize, FieldElem>> = Vec::new();
    const MAX_NOGOODS: usize = 4096;

    // Convert a PartialPoint to a compact map keyed by variable.
    fn point_to_map(r: &PartialPoint, fp: &PrimeField) -> BTreeMap<usize, FieldElem> {
        let mut m = BTreeMap::new();
        for (i, slot) in r.iter().enumerate() {
            if let Some(v) = slot {
                m.insert(i, fp.clone_el(v));
            }
        }
        m
    }

    // Subset check: returns true iff every (k, v) in `needle` matches `r[k]`.
    fn point_covers(needle: &BTreeMap<usize, FieldElem>, r: &PartialPoint) -> bool {
        for (k, v) in needle {
            match &r[*k] {
                Some(rv) if rv == v => continue,
                _ => return false,
            }
        }
        true
    }

    // Reorder a Brancher::Roots so the saved phase for a variable (if any)
    // is moved to the back of the Vec, so Vec::pop tries it first.
    fn apply_phase_save(b: &mut Brancher, saved: &HashMap<usize, FieldElem>) {
        if let Brancher::Roots(v) = b {
            for i in (0..v.len()).rev() {
                let (var, ref val) = v[i];
                if let Some(saved_val) = saved.get(&var) {
                    if val == saved_val {
                        let pair = v.remove(i);
                        v.push(pair);
                        return;
                    }
                }
            }
        }
    }

    let mut stack: Vec<Frame<'r>> = Vec::new();

    stack.push(Frame {
        bases: initial_bases,
        r: initial_r,
        candidates: Brancher::Roots(Vec::new()), // sentinel: populated below
        last_tried: None,
    });

    // Process the first frame specially (compute candidates).
    let first = stack.last_mut().unwrap();

    if first.bases.iter().any(|b| b.is_whole_ring()) {
        for p in orig_polys {
            if let Some(val) = evaluate_full(poly_ring, p, &first.r) {
                if !poly_ring.field.is_zero(&val) && !first.bases[0].contains(p) {
                    return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                }
            }
        }
        return ZeroExtendResult::NoZero { exhaustive: true };
    }

    let n_assigned = first.r.iter().filter(|v| v.is_some()).count();
    if n_assigned == poly_ring.n_vars {
        let out: Vec<FieldElem> = first.r.clone().into_iter().map(|v| v.unwrap()).collect();
        return ZeroExtendResult::Point(out);
    }

    first.candidates = apply_rule_multi(poly_ring, &first.bases, &first.r);
    apply_phase_save(&mut first.candidates, &saved_phase);
    log::trace!(
        "split_zero_extend: {} vars, {} assigned, brancher={}",
        poly_ring.n_vars,
        n_assigned,
        match &first.candidates {
            Brancher::Roots(v) => format!("Roots({})", v.len()),
            Brancher::RoundRobin { unassigned, .. } =>
                format!("RoundRobin({} vars)", unassigned.len()),
        }
    );

    let mut iter_count: u64 = 0;
    let mut bounded_search_used = false;
    loop {
        if cancel.is_cancelled() { return ZeroExtendResult::Cancelled; }
        iter_count += 1;

        if iter_count % 100 == 0 {
            log::trace!(
                "split_zero_extend: iter={}, stack_depth={}",
                iter_count, stack.len()
            );
        }
        if stats_on {
            crate::profile::SPLIT_DFS.observe_max_depth(stack.len() as u64);
        }

        if stack.is_empty() {
            return ZeroExtendResult::NoZero { exhaustive: !bounded_search_used };
        }
        let frame_idx = stack.len() - 1;

        // Try next candidate.
        let (var, val) = match stack[frame_idx].candidates.next(&poly_ring.field) {
            Some(c) => c,
            None => {
                // Brancher exhausted → backtrack. If it was a non-exhaustive
                // RoundRobin, the search did not cover the full space here.
                if !stack[frame_idx].candidates.is_exhaustive() {
                    bounded_search_used = true;
                }
                // Phase save: remember the last value tried on this frame
                // so future visits prefer it.
                if let Some((v, val)) = stack[frame_idx].last_tried.take() {
                    saved_phase.insert(v, val);
                }
                let _popped = stack.pop().unwrap();
                continue;
            }
        };
        // Record the candidate as the most-recent-tried for this frame
        // BEFORE attempting it, so a return-without-pop (cancel,
        // conflict) also leaves the trail in a consistent state.
        stack[frame_idx].last_tried = Some((var, poly_ring.field.clone_el(&val)));

        if stats_on {
            crate::profile::SPLIT_DFS.branches_tried
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }

        let mut new_r = stack[frame_idx].r.clone();
        new_r[var] = Some(poly_ring.field.clone_el(&val));
        let assign_poly = assignment_poly(poly_ring, var, &val);

        // Nogood subsumption check: if any recorded nogood is a subset
        // of the candidate's partial assignment `new_r`, this candidate
        // is already known UNSAT — skip without recomputing GB.
        if nogoods.iter().any(|ng| point_covers(ng, &new_r)) {
            if stats_on {
                crate::profile::SPLIT_DFS.nogood_subsumption_hits
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            continue;
        }

        // Quick UNSAT check: if substituting val for var in any basis
        // poly yields a nonzero constant, the branch is immediately
        // UNSAT.
        let qe_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
        let mut quick_unsat = false;
        for b in &stack[frame_idx].bases {
            for p in &b.basis {
                if let Some(v) = evaluate_full(poly_ring, p, &new_r) {
                    if !poly_ring.field.is_zero(&v) {
                        quick_unsat = true;
                        break;
                    }
                }
            }
            if quick_unsat { break; }
        }
        if let Some(t0) = qe_t0 {
            let dt = t0.elapsed().as_nanos() as u64;
            crate::profile::SPLIT_DFS.time_in_quick_eval_unsat_ns
                .fetch_add(dt, std::sync::atomic::Ordering::Relaxed);
        }
        if quick_unsat {
            if stats_on {
                crate::profile::SPLIT_DFS.quick_eval_unsat_hits
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            for p in orig_polys {
                if let Some(val) = evaluate_full(poly_ring, p, &new_r) {
                    if !poly_ring.field.is_zero(&val) && !stack[frame_idx].bases[0].contains(p) {
                        if stats_on {
                            crate::profile::SPLIT_DFS.conflicts_returned
                                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                        return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                    }
                }
            }
            if nogoods.len() < MAX_NOGOODS {
                nogoods.push(point_to_map(&new_r, &poly_ring.field));
            }
            continue; // backtrack
        }

        // Linear-only quick UNSAT pre-check. Before the full split-GB
        // extension on a candidate, test if adding the assignment to
        // the linear basis (basis 0) alone makes it the whole ring.
        //
        // For a basis whose elements all have degree <= 1, Buchberger
        // reduces to Gaussian elimination, so the test is exact:
        // `assign_poly mod lin_basis` is a non-zero constant iff the
        // augmented ideal is the whole ring.
        if !stack[frame_idx].bases.is_empty() {
            let lq_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
            let nf = stack[frame_idx].bases[0]
                .reduce_with_cancel(&assign_poly, cancel);
            if let Some(t0) = lq_t0 {
                let dt = t0.elapsed().as_nanos() as u64;
                crate::profile::SPLIT_DFS.time_in_linear_quick_unsat_ns
                    .fetch_add(dt, std::sync::atomic::Ordering::Relaxed);
            }
            if cancel.is_cancelled() { return ZeroExtendResult::Cancelled; }
            if !nf.is_zero() && nf.is_constant() {
                if stats_on {
                    crate::profile::SPLIT_DFS.linear_quick_unsat_hits
                        .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                // Linear basis ∪ {assign_poly} ⊇ {1} → whole ring → UNSAT.
                if nogoods.len() < MAX_NOGOODS {
                    nogoods.push(point_to_map(&new_r, &poly_ring.field));
                }
                continue;
            }
        }

        // Build a starting `SplitGb` of cloned ideals (each already a
        // reduced GB) and extend each with `assign_poly` as the single
        // new generator. The bit-prop fixpoint loop is preserved; only
        // the per-iteration GB recompute is replaced with incremental
        // Buchberger.
        let clone_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
        let starting: SplitGb<'r> = stack[frame_idx].bases.iter()
            .map(|b| {
                let cloned: Vec<Poly> = b.basis.iter()
                    .map(|p| poly_ring.ring.clone_el(p))
                    .collect();
                Ideal::from_gb(poly_ring, cloned)
            })
            .collect();
        let new_polys_per_split: Vec<Vec<Poly>> = (0..stack[frame_idx].bases.len())
            .map(|_| vec![poly_ring.ring.clone_el(&assign_poly)])
            .collect();
        if let Some(t0) = clone_t0 {
            let dt = t0.elapsed().as_nanos() as u64;
            crate::profile::SPLIT_DFS.time_in_basis_clone_ns
                .fetch_add(dt, std::sync::atomic::Ordering::Relaxed);
            crate::profile::SPLIT_DFS.branches_to_full_extend
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        let extend_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
        let new_bases = match split_gb_extend_cancel(
            poly_ring, starting, new_polys_per_split, bit_prop, cancel,
        ) {
            Ok(b) => b,
            Err(_) => return ZeroExtendResult::Cancelled,
        };
        if let Some(t0) = extend_t0 {
            let dt = t0.elapsed().as_nanos() as u64;
            crate::profile::SPLIT_DFS.time_in_split_gb_extend_ns
                .fetch_add(dt, std::sync::atomic::Ordering::Relaxed);
        }

        if new_bases.iter().any(|b| b.is_whole_ring()) {
            // UNSAT at this branch → look for conflict poly.
            for p in orig_polys {
                if let Some(val) = evaluate_full(poly_ring, p, &new_r) {
                    if !poly_ring.field.is_zero(&val) && !new_bases[0].contains(p) {
                        if stats_on {
                            crate::profile::SPLIT_DFS.conflicts_returned
                                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                        return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                    }
                }
            }
            if nogoods.len() < MAX_NOGOODS {
                nogoods.push(point_to_map(&new_r, &poly_ring.field));
            }
            // No conflict found; backtrack to next candidate.
            continue;
        }

        let n_assigned = new_r.iter().filter(|v| v.is_some()).count();
        if n_assigned == poly_ring.n_vars {
            if stats_on {
                crate::profile::SPLIT_DFS.points_returned
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            let out: Vec<FieldElem> = new_r.into_iter().map(|v| v.unwrap()).collect();
            return ZeroExtendResult::Point(out);
        }

        // Descend: compute candidates for the new state and push.
        let mut new_candidates = apply_rule_multi(poly_ring, &new_bases, &new_r);
        apply_phase_save(&mut new_candidates, &saved_phase);
        log::trace!(
            "split_zero_extend: depth={}, var={}, brancher={}",
            stack.len(),
            var,
            match &new_candidates {
                Brancher::Roots(v) => format!("Roots({})", v.len()),
                Brancher::RoundRobin { unassigned, .. } =>
                    format!("RoundRobin({} vars)", unassigned.len()),
            }
        );
        stack.push(Frame {
            bases: new_bases,
            r: new_r,
            candidates: new_candidates,
            last_tried: None,
        });
    }
}

/// Build a polynomial of the form `x_var - val`.
fn assignment_poly(pr: &FfPolyRing, var: usize, val: &FieldElem) -> Poly {
    let v = pr.var(var);
    let c = pr.constant(pr.field.clone_el(val));
    pr.sub(v, c)
}

/// Substitute the partial assignment into a polynomial and evaluate it.
/// Returns `Some(value)` if all variables in `p` are assigned (so it can
/// be fully evaluated); otherwise `None`.
pub(super) fn evaluate_full(pr: &FfPolyRing, p: &Poly, r: &PartialPoint) -> Option<FieldElem> {
    let ring = &pr.ring;
    let fp = &pr.field;
    let mut acc = fp.zero();
    for (c, m) in ring.terms(p) {
        let mut term_val = fp.clone_el(c);
        for v in 0..pr.n_vars {
            let e = ring.exponent_at(&m, v);
            if e == 0 { continue; }
            match &r[v] {
                None => return None,
                Some(val) => {
                    let pow = fp.pow_u64(val, e as u64);
                    fp.mul_assign(&mut term_val, &pow);
                }
            }
        }
        fp.add_assign(&mut acc, term_val);
    }
    Some(acc)
}
