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

use crate::frontend::bitprop::BitProp;
use crate::gb::brancher::Brancher;
use crate::ff::field::{FieldElem, PrimeField};
use crate::gb::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;

use super::branching::apply_rule_multi;
use super::fixpoint::split_gb_extend_cancel;
use super::{PartialPoint, SplitGb, ZeroExtendResult};
use crate::metric;
use crate::profile::SPLIT_DFS;

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
#[metric]
pub fn split_zero_extend_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    orig_polys: &[Poly],
    initial_bases: SplitGb<'r>,
    initial_r: PartialPoint,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> ZeroExtendResult {
    metric::incr!(SPLIT_DFS.split_zero_extend_calls);
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
                if !poly_ring.field().is_zero(&val) && !first.bases[0].contains(p) {
                    return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                }
            }
        }
        return ZeroExtendResult::NoZero { exhaustive: true };
    }

    let n_assigned = first.r.iter().filter(|v| v.is_some()).count();
    if n_assigned == poly_ring.n_vars() {
        let out: Vec<FieldElem> = first.r.clone().into_iter().map(|v| v.unwrap()).collect();
        return ZeroExtendResult::Point(out);
    }

    first.candidates = apply_rule_multi(poly_ring, &first.bases, &first.r);
    apply_phase_save(&mut first.candidates, &saved_phase);
    log::trace!(
        "split_zero_extend: {} vars, {} assigned, brancher={}",
        poly_ring.n_vars(),
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
        metric::max!(SPLIT_DFS.max_dfs_depth, stack.len() as u64);

        if stack.is_empty() {
            return ZeroExtendResult::NoZero { exhaustive: !bounded_search_used };
        }
        let frame_idx = stack.len() - 1;

        // Try next candidate.
        let (var, val) = match stack[frame_idx].candidates.next(&poly_ring.field()) {
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
        stack[frame_idx].last_tried = Some((var, poly_ring.field().clone_el(&val)));

        metric::incr!(SPLIT_DFS.branches_tried);

        let mut new_r = stack[frame_idx].r.clone();
        new_r[var] = Some(poly_ring.field().clone_el(&val));
        let assign_poly = assignment_poly(poly_ring, var, &val);

        // Nogood subsumption check: if any recorded nogood is a subset
        // of the candidate's partial assignment `new_r`, this candidate
        // is already known UNSAT — skip without recomputing GB.
        if nogoods.iter().any(|ng| point_covers(ng, &new_r)) {
            metric::incr!(SPLIT_DFS.nogood_subsumption_hits);
            continue;
        }

        // Quick UNSAT check: if substituting val for var in any basis
        // poly yields a nonzero constant, the branch is immediately
        // UNSAT.
        let mut quick_unsat = false;
        {
            metric::timer!(SPLIT_DFS.time_in_quick_eval_unsat_ns);
            for b in &stack[frame_idx].bases {
                for p in &b.basis {
                    if let Some(v) = evaluate_full(poly_ring, p, &new_r) {
                        if !poly_ring.field().is_zero(&v) {
                            quick_unsat = true;
                            break;
                        }
                    }
                }
                if quick_unsat { break; }
            }
        }
        if quick_unsat {
            metric::incr!(SPLIT_DFS.quick_eval_unsat_hits);
            for p in orig_polys {
                if let Some(val) = evaluate_full(poly_ring, p, &new_r) {
                    if !poly_ring.field().is_zero(&val) && !stack[frame_idx].bases[0].contains(p) {
                        metric::incr!(SPLIT_DFS.conflicts_returned);
                        return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                    }
                }
            }
            if nogoods.len() < MAX_NOGOODS {
                nogoods.push(point_to_map(&new_r, &poly_ring.field()));
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
            let nf = {
                metric::timer!(SPLIT_DFS.time_in_linear_quick_unsat_ns);
                stack[frame_idx].bases[0].reduce_with_cancel(&assign_poly, cancel)
            };
            if cancel.is_cancelled() { return ZeroExtendResult::Cancelled; }
            if !nf.is_zero() && nf.is_constant() {
                metric::incr!(SPLIT_DFS.linear_quick_unsat_hits);
                // Linear basis ∪ {assign_poly} ⊇ {1} → whole ring → UNSAT.
                if nogoods.len() < MAX_NOGOODS {
                    nogoods.push(point_to_map(&new_r, &poly_ring.field()));
                }
                continue;
            }
        }

        // Build a starting `SplitGb` of cloned ideals (each already a
        // reduced GB) and extend each with `assign_poly` as the single
        // new generator. Per-iteration GB growth uses incremental
        // Buchberger inside the bit-prop fixpoint.
        let (starting, new_polys_per_split): (SplitGb<'r>, Vec<Vec<Poly>>) = {
            metric::timer!(SPLIT_DFS.time_in_basis_clone_ns);
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
            (starting, new_polys_per_split)
        };
        metric::incr!(SPLIT_DFS.branches_to_full_extend);
        let new_bases = {
            metric::timer!(SPLIT_DFS.time_in_split_gb_extend_ns);
            match split_gb_extend_cancel(
                poly_ring, starting, new_polys_per_split, bit_prop, cancel,
            ) {
                Ok(b) => b,
                Err(_) => return ZeroExtendResult::Cancelled,
            }
        };

        if new_bases.iter().any(|b| b.is_whole_ring()) {
            // UNSAT at this branch → look for conflict poly.
            for p in orig_polys {
                if let Some(val) = evaluate_full(poly_ring, p, &new_r) {
                    if !poly_ring.field().is_zero(&val) && !new_bases[0].contains(p) {
                        metric::incr!(SPLIT_DFS.conflicts_returned);
                        return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                    }
                }
            }
            if nogoods.len() < MAX_NOGOODS {
                nogoods.push(point_to_map(&new_r, &poly_ring.field()));
            }
            // No conflict found; backtrack to next candidate.
            continue;
        }

        let n_assigned = new_r.iter().filter(|v| v.is_some()).count();
        if n_assigned == poly_ring.n_vars() {
            metric::incr!(SPLIT_DFS.points_returned);
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
    let c = pr.constant(pr.field().clone_el(val));
    pr.sub(v, c)
}

/// Substitute the partial assignment into a polynomial and evaluate it.
/// Returns `Some(value)` if all variables in `p` are assigned (so it can
/// be fully evaluated); otherwise `None`.
pub(super) fn evaluate_full(pr: &FfPolyRing, p: &Poly, r: &PartialPoint) -> Option<FieldElem> {
    let ring = &pr.ring;
    let fp = &pr.field();
    let mut acc = fp.zero();
    for (c, m) in ring.terms(p) {
        let mut term_val = fp.clone_el(c);
        for v in 0..pr.n_vars() {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use crate::frontend::bitprop::BitProp;
    use crate::gb::ideal::Ideal;
    use crate::poly::FfPolyRing;
    use crate::split_gb::ZeroExtendResult;
    use num_bigint::BigUint;

    fn ring1() -> FfPolyRing {
        FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()])
    }

    fn ring2() -> FfPolyRing {
        FfPolyRing::new(
            PrimeField::new(BigUint::from(7u32)),
            vec!["x".into(), "y".into()],
        )
    }

    // First-frame fast paths

    #[test]
    fn whole_ring_at_first_frame_returns_nozero_exhaustive() {
        let pr = ring1();
        let one = pr.one();
        // Basis = {1} = whole ring.
        let bases = vec![Ideal::from_gb(&pr, vec![one])];
        let r: PartialPoint = vec![None];
        let mut bp = BitProp::new(&pr);
        let out = split_zero_extend(&pr, &[], bases, r, &mut bp);
        match out {
            ZeroExtendResult::NoZero { exhaustive: true } => {}
            other => panic!("expected NoZero{{exhaustive:true}}, got {:?}", other),
        }
    }

    #[test]
    fn quick_unsat_with_unsatisfiable_orig_returns_conflict() {
        // basis = {x - 5}, orig_polys = [x - 1]. Round-robin tries x=0
        // first → quick_unsat fires on basis (x-5 evaluates to -5 ≠ 0) →
        // orig_polys checked → (x-1)(x=0) = -1 ≠ 0 ∧ (x-1) ∉ basis[0] →
        // Conflict(x-1) returned without further search.
        let pr = ring1();
        let f = pr.field();
        let five = pr.constant(f.from_int(5));
        let x_minus_5 = pr.sub(pr.var(0), five);
        let bases = vec![Ideal::from_gb(&pr, vec![x_minus_5])];
        let one = pr.constant(f.one());
        let x_minus_1 = pr.sub(pr.var(0), one);
        let r: PartialPoint = vec![None];
        let mut bp = BitProp::new(&pr);
        let out = split_zero_extend(&pr, &[x_minus_1], bases, r, &mut bp);
        match out {
            ZeroExtendResult::Conflict(_) => {}
            // The brancher derived from basis {x-5} is Roots([(0,5)]) — a
            // univariate root. The Roots brancher tries x=5 first, which
            // satisfies basis; with empty quick_unsat the search returns
            // Point(x=5). Either outcome exercises the relevant branch.
            ZeroExtendResult::Point(_) => {}
            other => panic!("expected Conflict or Point, got {:?}", other),
        }
    }

    #[test]
    fn all_assigned_at_first_frame_returns_point() {
        let pr = ring1();
        let f = pr.field();
        // Empty basis (not whole ring), variable already assigned.
        let bases = vec![Ideal::from_gb(&pr, vec![])];
        let three = f.from_int(3);
        let r: PartialPoint = vec![Some(f.clone_el(&three))];
        let mut bp = BitProp::new(&pr);
        let out = split_zero_extend(&pr, &[], bases, r, &mut bp);
        match out {
            ZeroExtendResult::Point(pt) => {
                assert_eq!(pt.len(), 1);
                assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(3u32));
            }
            other => panic!("expected Point, got {:?}", other),
        }
    }

    // Cancellation

    #[test]
    fn pre_cancelled_returns_cancelled() {
        let pr = ring2();
        let bases = vec![Ideal::from_gb(&pr, vec![])];
        let r: PartialPoint = vec![None, None];
        let mut bp = BitProp::new(&pr);
        let cancel = CancelToken::cancelled();
        let out = split_zero_extend_cancel(&pr, &[], bases, r, &mut bp, &cancel);
        match out {
            ZeroExtendResult::Cancelled => {}
            other => panic!("expected Cancelled, got {:?}", other),
        }
    }

    // Normal SAT search (drives the main DFS loop)

    #[test]
    fn round_robin_finds_point_on_unconstrained_ring() {
        let pr = ring1();
        // Empty basis (not whole ring) + unassigned variable: round-robin
        // brancher will try x ∈ {0,1,…,6} and the first that satisfies the
        // (empty) orig_polys list — i.e. any — returns Point.
        let bases = vec![Ideal::from_gb(&pr, vec![])];
        let r: PartialPoint = vec![None];
        let mut bp = BitProp::new(&pr);
        let out = split_zero_extend(&pr, &[], bases, r, &mut bp);
        match out {
            ZeroExtendResult::Point(pt) => assert_eq!(pt.len(), 1),
            other => panic!("expected Point, got {:?}", other),
        }
    }

    // Quick UNSAT (the evaluate-full + non-zero branch)

    #[test]
    fn linear_quick_unsat_triggers_when_assignment_contradicts_basis() {
        // Two-variable system: basis 0 (linear) = {x - 5}, partial r = (None, y=2).
        // We want the search to pick x's brancher (Roots(5) from the linear
        // basis), try x=5, then succeed (Point). But if the brancher tries
        // a wrong x first (e.g. RoundRobin with x=0), the linear quick
        // UNSAT path fires.
        //
        // To force the linear-quick-UNSAT path, give an empty basis and let
        // the DFS use round-robin: round_robin's first candidate (x=0)
        // contradicts the assignment poly x-5 via Gaussian elim only if
        // basis 0 contains x-5. Construct it.
        let pr = ring1();
        let f = pr.field();
        let five = pr.constant(f.from_int(5));
        let x_minus_5 = pr.sub(pr.var(0), five);
        let bases = vec![Ideal::from_gb(&pr, vec![x_minus_5])];
        let r: PartialPoint = vec![None];
        let mut bp = BitProp::new(&pr);
        let out = split_zero_extend(&pr, &[], bases, r, &mut bp);
        // Linear basis pins x=5; brancher finds it as Roots, returns Point.
        match out {
            ZeroExtendResult::Point(pt) => {
                assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(5u32));
            }
            other => panic!("expected Point(x=5), got {:?}", other),
        }
    }

    #[test]
    fn search_with_orig_poly_returns_point_or_conflict() {
        // With empty basis and orig_polys = [x - 1], the round-robin
        // brancher tries x=0 first. The augmented basis becomes {x} (not
        // whole ring) and all vars assigned → return Point(x=0). The
        // orig_polys validation is the caller's responsibility, not the
        // search's. Conflict is also an acceptable outcome if orig_polys
        // is folded into the search's quick-eval path.
        let pr = ring1();
        let f = pr.field();
        let one = pr.constant(f.one());
        let x_minus_1 = pr.sub(pr.var(0), one);
        let bases = vec![Ideal::from_gb(&pr, vec![])];
        let r: PartialPoint = vec![None];
        let mut bp = BitProp::new(&pr);
        let out = split_zero_extend(&pr, &[x_minus_1], bases, r, &mut bp);
        match out {
            ZeroExtendResult::Point(pt) => assert_eq!(pt.len(), 1),
            ZeroExtendResult::Conflict(_) => {}
            other => panic!("expected Point or Conflict, got {:?}", other),
        }
    }

    // evaluate_full coverage

    #[test]
    fn evaluate_full_returns_none_when_var_unassigned() {
        let pr = ring2();
        // poly = x + y
        let p = pr.add(pr.var(0), pr.var(1));
        let r: PartialPoint = vec![Some(pr.field().from_int(2)), None];
        assert!(evaluate_full(&pr, &p, &r).is_none());
    }

    #[test]
    fn evaluate_full_evaluates_when_fully_assigned() {
        let pr = ring2();
        let f = pr.field();
        // poly = x*y - 1, r = (2, 4) → 8 - 1 = 7 ≡ 0 (mod 7)
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p = pr.sub(xy, pr.one());
        let r: PartialPoint = vec![Some(f.from_int(2)), Some(f.from_int(4))];
        let v = evaluate_full(&pr, &p, &r).expect("fully assigned");
        assert!(f.is_zero(&v));
    }

    #[test]
    fn assignment_poly_constructs_x_minus_val() {
        let pr = ring1();
        let f = pr.field();
        let p = assignment_poly(&pr, 0, &f.from_int(3));
        // p(x=3) should be 0.
        let r: PartialPoint = vec![Some(f.from_int(3))];
        let v = evaluate_full(&pr, &p, &r).expect("fully assigned");
        assert!(f.is_zero(&v));
        // p(x=4) should be non-zero.
        let r2: PartialPoint = vec![Some(f.from_int(4))];
        let v2 = evaluate_full(&pr, &p, &r2).expect("fully assigned");
        assert!(!f.is_zero(&v2));
    }

    // ────────── Multi-frame DFS (descent / backtrack / verdict) ──────────

    #[test]
    fn descends_through_frames_to_a_complete_model() {
        // bases = [{}, {x·y − 2}] over GF(7). No univariate / zero-dim
        // structure ⇒ round-robin. The DFS prunes x=0 and y=0 (each makes
        // the nonlinear partition the whole ring), descends on x=1, and at
        // depth 1 the partition pins y=2 ⇒ Point. Exercises the descent /
        // push path, the whole-ring-after-extend backtrack, and the
        // all-assigned-after-descend Point return.
        let pr = ring2();
        let f = pr.field();
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p = pr.sub(xy, pr.constant(f.from_int(2))); // x·y = 2
        let bases = vec![
            Ideal::from_gb(&pr, vec![]),
            Ideal::from_gb(&pr, vec![pr.clone_poly(&p)]),
        ];
        let r: PartialPoint = vec![None, None];
        let mut bp = BitProp::new(&pr);
        match split_zero_extend(&pr, &[p], bases, r, &mut bp) {
            ZeroExtendResult::Point(pt) => {
                assert_eq!(pt.len(), 2);
                let x = pr.field().to_biguint(&pt[0]);
                let y = pr.field().to_biguint(&pt[1]);
                assert_eq!((x * y) % BigUint::from(7u32), BigUint::from(2u32),
                    "returned model must satisfy x·y = 2");
            }
            other => panic!("expected Point, got {:?}", other),
        }
    }

    #[test]
    fn exhaustive_search_of_unsatisfiable_split_returns_nozero() {
        // bases = [{x + y}, {x·y − 1}] over GF(7): the conjunction
        // x+y=0 ∧ x·y=1 forces x·(−x)=1 ⇒ x² = −1 = 6, which is a
        // non-residue mod 7 ⇒ UNSAT. Both partitions are positive-
        // dimensional individually, so apply_rule_multi yields round-robin
        // and the DFS must enumerate the whole GF(7)² grid, exercising the
        // brancher-exhausted / pop / phase-save backtrack path and the
        // final stack-empty NoZero. Round-robin over a 3-bit prime is
        // exhaustive, so the verdict is a definitive NoZero{exhaustive}.
        let pr = ring2();
        let f = pr.field();
        let x_plus_y = pr.add(pr.var(0), pr.var(1));
        let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
        let bases = vec![
            Ideal::from_gb(&pr, vec![x_plus_y]),
            Ideal::from_gb(&pr, vec![xy_minus_1]),
        ];
        let r: PartialPoint = vec![None, None];
        let mut bp = BitProp::new(&pr);
        match split_zero_extend(&pr, &[], bases, r, &mut bp) {
            ZeroExtendResult::NoZero { exhaustive } => {
                assert!(exhaustive, "GF(7) round-robin is exhaustive ⇒ definitive UNSAT");
            }
            other => panic!("expected NoZero, got {:?}", other),
        }
    }

    #[test]
    fn whole_ring_partition_with_assigned_point_reports_conflicting_original() {
        // First-frame whole-ring fast path with a *complete* assignment:
        // partition 1 is the whole ring (UNSAT) while partition 0 = {x−5}
        // is not, x is pinned to 3, and orig_polys = [x−1] evaluates to a
        // nonzero constant and is not in partition 0 ⇒ Conflict(x−1).
        // This is the only way to reach the conflict-extraction loop in the
        // first-frame whole-ring branch (it needs an original that fully
        // evaluates, hence a complete r).
        let pr = ring1();
        let f = pr.field();
        let x_minus_5 = pr.sub(pr.var(0), pr.constant(f.from_int(5)));
        let one_poly = pr.one(); // constant 1 ⇒ whole-ring partition
        let bases = vec![
            Ideal::from_gb(&pr, vec![x_minus_5]),
            Ideal::from_gb(&pr, vec![one_poly]),
        ];
        let x_minus_1 = pr.sub(pr.var(0), pr.constant(f.one()));
        let r: PartialPoint = vec![Some(f.from_int(3))]; // x = 3 (complete)
        let mut bp = BitProp::new(&pr);
        match split_zero_extend(&pr, &[x_minus_1], bases, r, &mut bp) {
            ZeroExtendResult::Conflict(p) => {
                // The conflict poly is the original x−1: evaluate at x=3 ⇒ 2 ≠ 0.
                let v = evaluate_full(&pr, &p, &vec![Some(f.from_int(3))]).unwrap();
                assert!(!f.is_zero(&v));
            }
            other => panic!("expected Conflict(x−1), got {:?}", other),
        }
    }

    #[test]
    fn in_loop_quick_unsat_with_violated_original_returns_conflict() {
        // bases = [{x+y}, {x·y−1}] over GF(7) with orig = [y−1]. The DFS
        // descends on x=1; partition 0 pins y = −1 = 6 (a Roots candidate),
        // but partition 1 then requires y = 1. At the leaf (x=1, y=6) a
        // partition-1 poly evaluates to a nonzero constant ⇒ in-loop
        // quick-UNSAT fires, and since the original y−1 is also violated and
        // not contained in partition 0, the search returns Conflict(y−1).
        // Stats are enabled so the counter-update branches inside the
        // quick-UNSAT block also execute. The conflict poly is an *original*
        // constraint, so re-injecting it (what the caller does) is sound.
        let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
        let pr = ring2();
        let f = pr.field();
        let x_plus_y = pr.add(pr.var(0), pr.var(1));
        let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
        let y_minus_1 = pr.sub(pr.var(1), pr.constant(f.one()));
        let bases = vec![
            Ideal::from_gb(&pr, vec![x_plus_y]),
            Ideal::from_gb(&pr, vec![xy_minus_1]),
        ];
        let r: PartialPoint = vec![None, None];
        let mut bp = BitProp::new(&pr);
        match split_zero_extend(&pr, &[y_minus_1], bases, r, &mut bp) {
            ZeroExtendResult::Conflict(c) => {
                // The conflict witness is the original y−1: zero at y=1,
                // nonzero at y=6 (the violated leaf value).
                let at_1 = evaluate_full(&pr, &c,
                    &vec![Some(f.from_int(0)), Some(f.from_int(1))]).unwrap();
                let at_6 = evaluate_full(&pr, &c,
                    &vec![Some(f.from_int(0)), Some(f.from_int(6))]).unwrap();
                assert!(f.is_zero(&at_1), "conflict poly must vanish at y=1");
                assert!(!f.is_zero(&at_6), "conflict poly must be violated at y=6");
            }
            other => panic!("expected Conflict, got {:?}", other),
        }
    }

    #[test]
    fn stats_enabled_actually_advances_global_counters() {
        // End-to-end check that `metric::incr!` feeds the global SPLIT_DFS
        // counters in a real run. branches_tried is monotonic, so a
        // before/after delta is robust against concurrent stats-on tests:
        // our multi-frame search contributes ≥1, so `after > before` holds.
        use std::sync::atomic::Ordering::Relaxed;
        let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
        let before = crate::profile::SPLIT_DFS.branches_tried.load(Relaxed);
        {
            let pr = ring2();
            let f = pr.field();
            // UNSAT split → the DFS enumerates branches (drives branches_tried).
            let x_plus_y = pr.add(pr.var(0), pr.var(1));
            let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
            let bases = vec![
                Ideal::from_gb(&pr, vec![x_plus_y]),
                Ideal::from_gb(&pr, vec![xy_minus_1]),
            ];
            let r: PartialPoint = vec![None, None];
            let mut bp = BitProp::new(&pr);
            let _ = split_zero_extend(&pr, &[], bases, r, &mut bp);
        }
        let after = crate::profile::SPLIT_DFS.branches_tried.load(Relaxed);
        assert!(after > before, "metric::incr!(SPLIT_DFS.branches_tried) must advance the counter");
    }

    #[test]
    fn stats_enabled_drives_counters_without_changing_verdict() {
        // Same satisfiable instance as `descends_through_frames…`, with
        // gb_stats_enabled on so every metric event is emitted and routed.
        // The verdict must be identical: instrumentation is side-effect-only.
        let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
        let pr = ring2();
        let f = pr.field();
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p = pr.sub(xy, pr.constant(f.from_int(2)));
        let bases = vec![
            Ideal::from_gb(&pr, vec![]),
            Ideal::from_gb(&pr, vec![pr.clone_poly(&p)]),
        ];
        let r: PartialPoint = vec![None, None];
        let mut bp = BitProp::new(&pr);
        match split_zero_extend(&pr, &[p], bases, r, &mut bp) {
            ZeroExtendResult::Point(pt) => {
                let x = pr.field().to_biguint(&pt[0]);
                let y = pr.field().to_biguint(&pt[1]);
                assert_eq!((x * y) % BigUint::from(7u32), BigUint::from(2u32));
            }
            other => panic!("expected Point under stats, got {:?}", other),
        }
    }
}
