//! Split Groebner Basis solver.
//!
//! Implements the algorithm from "Split Groebner Bases for Satisfiability
//! Modulo Finite Fields" (Ozdemir et al., CAV 2023).  Mirrors cvc5's
//! `theory/ff/split_gb.{h,cpp}`.
//!
//! The idea: instead of one big GB over all polynomials, maintain `k` GBs
//! over disjoint subsets, sharing only "small" polynomials between them.
//! The default split is into two ideals:
//!
//!   - **ideal 0** ("linear"):    accepts all polynomials with `deg <= 1`.
//!   - **ideal 1** ("nonlinear"): accepts polynomials with `deg <= 1` and
//!                                `numTerms <= 2` (binomial linear only).
//!
//! `splitGb` computes a fixpoint: each round it (a) adds new generators to
//! each ideal, (b) recomputes each ideal's GB, (c) extracts polynomials that
//! cross the admission boundary and (d) propagates them, including new
//! BitProp-derived equalities.

use std::collections::{BTreeMap, HashMap};

use crate::bitprop::BitProp;
use crate::brancher::Brancher;
use crate::field::FfEl;
use crate::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::{CancelToken, Cancelled};

/// A split Groebner basis: one `Ideal` per partition.
pub type SplitGb<'r> = Vec<Ideal<'r>>;

/// Default split-admission predicate (matches cvc5's `admit`).
///
/// cvc5's `split_gb.cpp:245-249`:
///   `admit(i, p) = deg(p) <= 1 && (i == 0 || numTerms(p) <= 2)`
///
///   - basis 0 (linear):    admits `p` iff `deg(p) <= 1`.
///   - basis 1 (nonlinear): admits `p` iff `deg(p) <= 1` and `numTerms(p) <= 2`.
///   - any other index: never admit.
pub fn admit(pr: &FfPolyRing, idx: usize, p: &Poly) -> bool {
    let ring = &pr.ring;
    let d = total_degree(ring, p);
    if d > 1 { return false; }
    match idx {
        0 => true,
        1 => num_terms(ring, p) <= 2,
        _ => false,
    }
}

/// Total degree of a polynomial.
pub fn total_degree(_ring: &crate::poly::PolyRingType, p: &Poly) -> usize {
    p.total_degree() as usize
}

/// Number of terms in a polynomial.
pub fn num_terms(_ring: &crate::poly::PolyRingType, p: &Poly) -> usize {
    p.num_terms()
}

/// Compute a split GB.  See cvc5's `splitGb`.
///
/// `generator_sets[i]` is the initial generator set for ideal `i`.
/// The function mutates `bit_prop` (used for propagation across bases).
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
    let k = generator_sets.len();
    let mut new_polys: Vec<Vec<Poly>> = generator_sets;
    let mut split_basis: SplitGb<'r> = (0..k)
        .map(|_| Ideal::from_gb(poly_ring, Vec::new()))
        .collect();

    let max_fixpoint_iters = (k * 64).max(256);
    let mut fixpoint_iter = 0;

    loop {
        if cancel.is_cancelled() { return Err(Cancelled); }
        fixpoint_iter += 1;
        if fixpoint_iter > max_fixpoint_iters {
            log::warn!("split_gb_cancel: fixpoint iteration cap ({max_fixpoint_iters}) reached");
            break;
        }

        // Incremental Buchberger — extend each existing basis with its
        // new polys instead of recomputing GB on the full union.  At
        // first iteration `split_basis[i]` is empty (line 99 above),
        // so `extend_with_cancel` short-circuits via
        // `compute_gb_with_order` on `new_polys[i]` alone.  On later
        // iterations the existing basis is a reduced GB (output of a
        // prior `extend_with_cancel`), so the incremental precondition
        // holds.
        for i in 0..k {
            if !new_polys[i].is_empty() {
                let added = std::mem::take(&mut new_polys[i]);
                let existing = std::mem::replace(
                    &mut split_basis[i],
                    Ideal::from_gb(poly_ring, Vec::new()),
                );
                split_basis[i] = existing.extend_with_cancel(added, cancel)?;
            }
        }

        if split_basis.iter().any(|b| b.is_whole_ring()) {
            break;
        }

        let mut to_propagate = bit_prop.get_bit_equalities(&split_basis);
        for b in &split_basis {
            for p in &b.basis {
                to_propagate.push(poly_ring.ring.clone_el(p));
            }
        }

        let mut any_new = false;
        for p in &to_propagate {
            for j in 0..k {
                if admit(poly_ring, j, p) && !split_basis[j].contains(p) {
                    new_polys[j].push(poly_ring.ring.clone_el(p));
                    any_new = true;
                }
            }
        }

        if !any_new { break; }
    }

    Ok(split_basis)
}

/// Incremental version of [`split_gb_cancel`].
///
/// Takes a *pre-existing* `SplitGb` (whose ideals are already reduced
/// GBs) plus per-split `new_polys`, and runs the bit-prop fixpoint
/// loop using `Ideal::extend_with_cancel` instead of full GB
/// recomputes.  This is a strict generalisation of `split_gb_cancel`:
/// the latter is equivalent to calling this function with an empty
/// starting `SplitGb` and `new_polys = generator_sets`.
///
/// # Why this matters
///
/// `split_zero_extend_cancel` calls `split_gb_cancel` from inside a
/// DFS loop where each iteration adds ONE assignment polynomial to
/// each split's basis.  Each such call recomputes the full GB
/// from scratch, even though every split's basis is already a reduced
/// GB and only one new generator is being added.  Using
/// `split_gb_extend_cancel` from that hot path lets each ideal grow
/// incrementally.
pub(crate) fn split_gb_extend_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    starting: SplitGb<'r>,
    new_polys: Vec<Vec<Poly>>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<SplitGb<'r>, Cancelled> {
    let _t = crate::profile::ScopedTimer::new("split_gb_extend_cancel");
    let k = starting.len();
    debug_assert_eq!(k, new_polys.len(),
        "split_gb_extend_cancel: starting and new_polys must have same length");
    let mut new_polys: Vec<Vec<Poly>> = new_polys;
    let mut split_basis: SplitGb<'r> = starting;

    let max_fixpoint_iters = (k * 64).max(256);
    let mut fixpoint_iter = 0;

    loop {
        if cancel.is_cancelled() { return Err(Cancelled); }
        fixpoint_iter += 1;
        if fixpoint_iter > max_fixpoint_iters {
            log::warn!("split_gb_extend_cancel: fixpoint iteration cap ({max_fixpoint_iters}) reached");
            break;
        }

        // Extend each basis with its new polys via incremental Buchberger.
        for i in 0..k {
            if !new_polys[i].is_empty() {
                let added = std::mem::take(&mut new_polys[i]);
                let existing = std::mem::replace(
                    &mut split_basis[i],
                    Ideal::from_gb(poly_ring, Vec::new()),
                );
                split_basis[i] = existing.extend_with_cancel(added, cancel)?;
            }
        }

        if split_basis.iter().any(|b| b.is_whole_ring()) {
            break;
        }

        let mut to_propagate = bit_prop.get_bit_equalities(&split_basis);
        for b in &split_basis {
            for p in &b.basis {
                to_propagate.push(poly_ring.ring.clone_el(p));
            }
        }

        let mut any_new = false;
        for p in &to_propagate {
            for j in 0..k {
                if admit(poly_ring, j, p) && !split_basis[j].contains(p) {
                    new_polys[j].push(poly_ring.ring.clone_el(p));
                    any_new = true;
                }
            }
        }

        if !any_new { break; }
    }

    Ok(split_basis)
}

/// A partial assignment of variable indices to field values.
pub type PartialPoint = Vec<Option<FfEl>>;

/// Result of the recursive `split_zero_extend`.
pub enum ZeroExtendResult {
    /// A complete assignment was found.
    Point(Vec<FfEl>),
    /// A conflict polynomial: not in `bases[0]` but evaluates to non-zero
    /// under the partial assignment.
    Conflict(Poly),
    /// No common zeros exist that extend the current partial assignment.
    /// `exhaustive = true` means the search proved UNSAT; `false` means
    /// the search exhausted a non-exhaustive round-robin brancher on a
    /// large prime and the result is INCONCLUSIVE (Unknown), not UNSAT.
    NoZero { exhaustive: bool },
    /// Computation was cancelled (timeout).
    Cancelled,
}

/// Build a polynomial of the form `x_var - val`.
fn assignment_poly(pr: &FfPolyRing, var: usize, val: &FfEl) -> Poly {
    let v = pr.var(var);
    let c = pr.constant(pr.field.field().clone_el(val));
    pr.sub(v, c)
}

/// Substitute the partial assignment into a polynomial and check if it's zero.
/// Returns Some(value) if all variables in `p` are assigned (so we can fully
/// evaluate); else None.
fn evaluate_full(pr: &FfPolyRing, p: &Poly, r: &PartialPoint) -> Option<FfEl> {
    let ring = &pr.ring;
    let fp = pr.field.field();
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

/// Try to extend `cur_r` into a complete zero of the ideal whose generators
/// are `orig_polys`.  Mirrors cvc5's `splitZeroExtend`.
pub fn split_zero_extend<'r>(
    poly_ring: &'r FfPolyRing,
    orig_polys: &[Poly],
    cur_bases: SplitGb<'r>,
    cur_r: PartialPoint,
    bit_prop: &mut BitProp<'r>,
) -> ZeroExtendResult {
    split_zero_extend_cancel(poly_ring, orig_polys, cur_bases, cur_r, bit_prop, &CancelToken::none())
}

/// Cancel-aware version of `split_zero_extend`.
///
/// Uses an explicit stack instead of recursion to avoid stack overflow
/// on deep searches (matching cvc5's iterative `splitZeroExtend`).
///
/// CDCL-lite enhancements:
///   * **Phase saving**: when a frame is popped, the partial assignment's
///     last-assigned `(var, val)` is remembered in `saved_phase`. When a
///     future `Brancher::Roots(v)` is constructed for the same variable,
///     the saved value (if present) is moved to the back of `v` so
///     `v.pop()` tries it first. This is a per-call cache, not per-frame:
///     a value that worked deep along one branch is preferred again.
///   * **Nogood cache**: each time a candidate `(var, val)` is proved
///     infeasible (quick UNSAT, linear-only whole-ring, or full split-GB
///     whole-ring), the resulting partial assignment is recorded as a
///     `Nogood`. Future candidates whose partial assignment is a
///     superset of any stored nogood are skipped without recomputing GB.
///     Keys are `BTreeMap<usize, FfEl>` so the subset check is linear in
///     the smaller map.
pub fn split_zero_extend_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    orig_polys: &[Poly],
    initial_bases: SplitGb<'r>,
    initial_r: PartialPoint,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> ZeroExtendResult {
    let _t = crate::profile::ScopedTimer::new("split_zero_extend_cancel");
    // Each stack frame holds: (bases, partial_assignment, brancher)
    struct Frame<'r> {
        bases: SplitGb<'r>,
        r: PartialPoint,
        candidates: Brancher,
        /// `(var, val)` of the most recently *attempted* candidate from
        /// `candidates` — used to feed `saved_phase` on backtrack.
        last_tried: Option<(usize, FfEl)>,
    }

    // ─── CDCL-lite: phase saving + nogood cache ───────────────────────────
    //
    // `saved_phase[v]` is the most recently popped value of variable `v`
    // (across the whole search). When a future Brancher::Roots produces
    // candidates for `v`, the saved value is moved to the back of the Vec
    // so `Vec::pop` (Brancher::Roots semantics, see split_gb.rs:Brancher
    // impl) tries it first.
    let mut saved_phase: HashMap<usize, FfEl> = HashMap::new();

    // `nogoods` records partial assignments proved infeasible. Each entry
    // is the *minimal* prefix that triggered the infeasibility: the path
    // from root + the failing decision. A new candidate is skipped if its
    // partial assignment is a superset of any stored nogood.
    let mut nogoods: Vec<BTreeMap<usize, FfEl>> = Vec::new();
    // Cap on stored nogoods to bound memory and per-candidate scan time.
    // Empirically generous; if exceeded, oldest entries are dropped.
    const MAX_NOGOODS: usize = 4096;

    // ─── CDCL-lite: tracer-driven nogood strengthening ───────────────────
    //
    // When the cheap linear-only fast-path detects whole-ring (UNSAT),
    // we run a SECOND, traced GB pass with `compute_gb_with_order_traced`
    // to extract the precise UNSAT core (which inputs were necessary
    // for the contradiction). The core indices are mapped back to
    // `(var, val)` decisions and recorded as a SHORTENED nogood — only
    // the implicated variables, not the full path. Subsumption-based
    // pruning of future candidates then provides effective non-chrono
    // backjumping at minimal hot-path cost (the tracer runs only on
    // confirmed UNSAT, not on every candidate).
    //
    // We keep `extend_with_cancel` as the primary detector to
    // avoid the per-candidate observer overhead seen with an always-on
    // `IncrementalGB` driver.
    //
    // No persistent IGB or tracer state is needed; each trivial event
    // gets its own short-lived tracer.

    // Convert a PartialPoint to a compact map keyed by variable.
    fn point_to_map(r: &PartialPoint, fp: &crate::field::FfField) -> BTreeMap<usize, FfEl> {
        let mut m = BTreeMap::new();
        for (i, slot) in r.iter().enumerate() {
            if let Some(v) = slot {
                m.insert(i, fp.field().clone_el(v));
            }
        }
        m
    }

    // Subset check: returns true iff every (k, v) in `needle` matches `r[k]`.
    fn point_covers(needle: &BTreeMap<usize, FfEl>, r: &PartialPoint) -> bool {
        for (k, v) in needle {
            match &r[*k] {
                Some(rv) if rv == v => continue,
                _ => return false,
            }
        }
        true
    }

    // Reorder a Brancher::Roots so the saved phase for a variable (if any)
    // is moved to the BACK of the Vec, so Vec::pop tries it first.
    fn apply_phase_save(b: &mut Brancher, saved: &HashMap<usize, FfEl>) {
        if let Brancher::Roots(v) = b {
            // Find the latest occurrence of (var, val) where val == saved[var]
            // and swap_remove it to the back.
            for i in (0..v.len()).rev() {
                let (var, ref val) = v[i];
                if let Some(saved_val) = saved.get(&var) {
                    if val == saved_val {
                        let pair = v.remove(i);
                        v.push(pair);
                        // One application is enough: Brancher::Roots either
                        // contains roots for one variable (cases 1/2 in
                        // apply_rule_multi) or a small mixed list. A single
                        // promotion still helps and avoids quadratic work
                        // for very large root sets.
                        return;
                    }
                }
            }
        }
    }

    let mut stack: Vec<Frame<'r>> = Vec::new();

    // Push the initial frame
    stack.push(Frame {
        bases: initial_bases,
        r: initial_r,
        candidates: Brancher::Roots(Vec::new()), // sentinel: will be populated below
        last_tried: None,
    });

    // Process the first frame specially (compute candidates)
    let first = stack.last_mut().unwrap();

    // Check whole ring
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

    // Check all assigned
    let n_assigned = first.r.iter().filter(|v| v.is_some()).count();
    if n_assigned == poly_ring.n_vars {
        let out: Vec<FfEl> = first.r.clone().into_iter().map(|v| v.unwrap()).collect();
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

        // If stack is empty, search exhausted
        if stack.is_empty() {
            return ZeroExtendResult::NoZero { exhaustive: !bounded_search_used };
        }
        let frame_idx = stack.len() - 1;

        // Try next candidate
        let (var, val) = match stack[frame_idx].candidates.next(&poly_ring.field) {
            Some(c) => c,
            None => {
                // Brancher exhausted → backtrack.  If it was a non-exhaustive
                // RoundRobin, the search did not cover the full space here.
                if !stack[frame_idx].candidates.is_exhaustive() {
                    bounded_search_used = true;
                }
                // Phase save: remember the last value we *tried* on this
                // frame so future visits prefer it.
                if let Some((v, val)) = stack[frame_idx].last_tried.take() {
                    saved_phase.insert(v, val);
                }
                let _popped = stack.pop().unwrap();
                continue;
            }
        };
        // Record the candidate as the most-recent-tried for this frame
        // BEFORE attempting it, so a return-without-pop (cancel, conflict)
        // also leaves the trail in a consistent state.
        stack[frame_idx].last_tried = Some((var, poly_ring.field.field().clone_el(&val)));

        let mut new_r = stack[frame_idx].r.clone();
        new_r[var] = Some(poly_ring.field.field().clone_el(&val));
        let assign_poly = assignment_poly(poly_ring, var, &val);

        // Nogood subsumption check: if any recorded nogood is a subset of
        // the candidate's partial assignment `new_r`, this candidate is
        // already known UNSAT — skip without recomputing GB.
        if nogoods.iter().any(|ng| point_covers(ng, &new_r)) {
            continue;
        }

        // Build new generator sets: each basis + the assignment polynomial
        // Quick UNSAT check: if substituting val for var in any basis poly
        // yields a nonzero constant, the branch is immediately UNSAT.
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
        if quick_unsat {
            // This branch is UNSAT without needing a full GB recomputation.
            // Check for conflict polynomial (same as the full UNSAT path).
            for p in orig_polys {
                if let Some(val) = evaluate_full(poly_ring, p, &new_r) {
                    if !poly_ring.field.is_zero(&val) && !stack[frame_idx].bases[0].contains(p) {
                        return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                    }
                }
            }
            // Record the failing partial assignment as a nogood for
            // subsumption-based pruning of future candidates.
            if nogoods.len() < MAX_NOGOODS {
                nogoods.push(point_to_map(&new_r, &poly_ring.field));
            }
            continue; // backtrack to next candidate
        }

        // Optimization: first check if adding the assignment to the linear
        // basis (basis 0) alone makes it the whole ring.  This is cheap
        // (~1ms) and eliminates UNSAT branches without the expensive
        // nonlinear basis recomputation (~12ms).
        //
        // Uses `extend_with_cancel` (incremental Buchberger seeded
        // from the parent frame's reduced GB) to avoid recomputing the
        // linear basis from scratch on every branching candidate.
        if !stack[frame_idx].bases.is_empty() {
            let cloned_basis: Vec<Poly> = stack[frame_idx].bases[0].basis.iter()
                .map(|p| poly_ring.ring.clone_el(p)).collect();
            let lin_ideal_seed = Ideal::from_gb(poly_ring, cloned_basis);
            let lin_ideal = match lin_ideal_seed.extend_with_cancel(
                vec![poly_ring.ring.clone_el(&assign_poly)], cancel,
            ) {
                Ok(i) => i,
                Err(_) => return ZeroExtendResult::Cancelled,
            };
            if lin_ideal.is_whole_ring() {
                // Linear basis alone is UNSAT — record full partial assignment
                // as a nogood. (Backjumping / projection deferred: an
                // earlier IGB-driven variant regressed `binadd1` due to
                // per-candidate observer overhead and lost interreduction.)
                if nogoods.len() < MAX_NOGOODS {
                    nogoods.push(point_to_map(&new_r, &poly_ring.field));
                }
                continue;
            }
        }

        // Instead of cloning every split's basis polys, appending
        // `assign_poly`, and recomputing each GB from scratch via
        // `split_gb_cancel`, build a starting `SplitGb` of cloned
        // ideals (already reduced GBs by invariant) and call
        // `split_gb_extend_cancel` with `assign_poly` as the single
        // new generator per split.  The bit-prop fixpoint loop is
        // preserved; only the per-iteration GB recompute is replaced
        // with incremental Buchberger.
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
        let new_bases = match split_gb_extend_cancel(
            poly_ring, starting, new_polys_per_split, bit_prop, cancel,
        ) {
            Ok(b) => b,
            Err(_) => return ZeroExtendResult::Cancelled,
        };

        // Check the new state
        if new_bases.iter().any(|b| b.is_whole_ring()) {
            // UNSAT at this branch → look for conflict poly
            for p in orig_polys {
                if let Some(val) = evaluate_full(poly_ring, p, &new_r) {
                    if !poly_ring.field.is_zero(&val) && !new_bases[0].contains(p) {
                        return ZeroExtendResult::Conflict(poly_ring.ring.clone_el(p));
                    }
                }
            }
            // Record the failing partial assignment as a nogood.
            if nogoods.len() < MAX_NOGOODS {
                nogoods.push(point_to_map(&new_r, &poly_ring.field));
            }
            // No conflict found, just backtrack (try next candidate)
            continue;
        }

        let n_assigned = new_r.iter().filter(|v| v.is_some()).count();
        if n_assigned == poly_ring.n_vars {
            let out: Vec<FfEl> = new_r.into_iter().map(|v| v.unwrap()).collect();
            return ZeroExtendResult::Point(out);
        }

        // Go deeper: compute candidates for the new state and push
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

/// Like `apply_rule` but checks ALL bases for univariate/zero-dim structure.
/// cvc5 only checks basis[0], but checking all bases can avoid expensive
/// round-robin by finding structure in the nonlinear basis.
fn apply_rule_multi<'r>(
    poly_ring: &'r FfPolyRing,
    bases: &[Ideal<'r>],
    r: &PartialPoint,
) -> Brancher {
    let _t = crate::profile::ScopedTimer::new("apply_rule_multi");
    let ring = &poly_ring.ring;
    let field = &poly_ring.field;

    // (1) Check ALL bases for univariate polynomial in an unassigned variable
    for gb in bases {
        for p in &gb.basis {
            let appearing = ring.appearing_indeterminates(p);
            if appearing.len() == 1 {
                let (var_idx, _) = appearing[0];
                if r[var_idx].is_none() {
                    if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                        let roots = crate::roots::find_roots(field, &coeffs);
                        return Brancher::Roots(
                            roots.into_iter().map(|v| (var_idx, v)).collect()
                        );
                    }
                }
            }
        }
    }

    // (2) Check ALL bases for zero-dim → minimal polynomial
    for gb in bases {
        if gb.is_zero_dim() {
            for v in 0..poly_ring.n_vars {
                if r[v].is_none() {
                    if let Some(coeffs) = gb.min_poly(v) {
                        let roots = crate::roots::find_roots(field, &coeffs);
                        return Brancher::Roots(
                            roots.into_iter().map(|val| (v, val)).collect()
                        );
                    }
                }
            }
        }
    }

    // (3) round-robin on basis[0]
    if !bases.is_empty() {
        apply_rule(poly_ring, &bases[0], r)
    } else {
        Brancher::Roots(Vec::new())
    }
}

/// Apply branching rule on a single basis.
///
/// (1) if `gb` has a univariate polynomial in some unassigned variable,
///     enumerate its roots over GF(p);
/// (2) if `gb` is zero-dimensional, compute the minimal polynomial of an
///     unassigned variable and enumerate its roots;
/// (3) otherwise, round-robin: for each unassigned variable, try values
///     in `0..min(p, cap)` (lazily generated, matching cvc5's
///     `RoundRobinEnumerator`).
pub fn apply_rule<'r>(
    poly_ring: &'r FfPolyRing,
    gb: &Ideal<'r>,
    r: &PartialPoint,
) -> Brancher {
    let ring = &poly_ring.ring;
    let field = &poly_ring.field;

    // (1) univariate polynomial in an unassigned variable
    for p in &gb.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, _) = appearing[0];
            if r[var_idx].is_none() {
                if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                    let roots = crate::roots::find_roots(field, &coeffs);
                    return Brancher::Roots(
                        roots.into_iter().map(|v| (var_idx, v)).collect()
                    );
                }
            }
        }
    }

    // (2) zero-dim: compute minimal polynomial
    if gb.is_zero_dim() {
        for v in 0..poly_ring.n_vars {
            if r[v].is_none() {
                if let Some(coeffs) = gb.min_poly(v) {
                    let roots = crate::roots::find_roots(field, &coeffs);
                    // Return roots as candidates. If roots is empty, the
                    // ideal is inconsistent under any assignment to this
                    // variable — return empty to trigger backtracking.
                    return Brancher::Roots(
                        roots.into_iter().map(|val| (v, val)).collect()
                    );
                }
            }
        }
    }

    // (3) round-robin: lazy generation matching cvc5's RoundRobinEnumerator
    let unassigned: Vec<usize> = (0..poly_ring.n_vars).filter(|i| r[*i].is_none()).collect();
    if unassigned.is_empty() {
        return Brancher::Roots(Vec::new());
    }

    let prime = &field.prime;
    // No per-variable cap — cvc5 relies on the solver-level timeout to
    // terminate enumeration. We follow that model: set the count to the
    // field size (capped at u64::MAX for huge primes).  The DFS
    // cancel-token check terminates exhaustive enumeration when time
    // runs out, just as in cvc5.
    let exhaustive = prime.bits() <= 16;
    let per_var: u64 = if exhaustive {
        let x = prime.iter_u64_digits().next().unwrap_or(2);
        x.max(2)
    } else {
        // Large prime: enumerate up to u64::MAX. Practically the cancel
        // token will fire long before this is exhausted.
        u64::MAX
    };
    let total = per_var.saturating_mul(unassigned.len() as u64);

    Brancher::RoundRobin {
        unassigned,
        idx: 0,
        total,
        exhaustive,
    }
}

/// Extract univariate coefficients (assumes only `var_idx` appears in `p`).
fn univariate_coeffs(
    poly_ring: &FfPolyRing,
    p: &Poly,
    var_idx: usize,
) -> Option<Vec<FfEl>> {
    let ring = &poly_ring.ring;
    let fp = poly_ring.field.field();
    let appearing = ring.appearing_indeterminates(p);
    for (v, _) in &appearing {
        if *v != var_idx { return None; }
    }
    let mut coeffs: HashMap<usize, FfEl> = HashMap::new();
    let mut max_deg = 0usize;
    for (c, m) in ring.terms(p) {
        let d = ring.exponent_at(&m, var_idx);
        if d > max_deg { max_deg = d; }
        let entry = coeffs.entry(d).or_insert_with(|| fp.zero());
        fp.add_assign(entry, fp.clone_el(c));
    }
    let mut out = Vec::with_capacity(max_deg + 1);
    for d in 0..=max_deg {
        out.push(coeffs.remove(&d).unwrap_or_else(|| fp.zero()));
    }
    Some(out)
}

/// Top-level `split` routine: encode `(orig_polys, bitsums)` into a split
/// GB, run the propagation fixpoint, then `splitFindZero` to extract a
/// model.
pub fn split_find_zero<'r>(
    poly_ring: &'r FfPolyRing,
    split_basis: SplitGb<'r>,
    bit_prop: &mut BitProp<'r>,
) -> SplitFindZeroOutcome {
    match split_find_zero_cancel(poly_ring, split_basis, bit_prop, &CancelToken::none()) {
        Ok(o) => o,
        Err(_) => SplitFindZeroOutcome::Unknown,
    }
}

/// Three-valued outcome of `split_find_zero`.
///
/// `Unknown` means the search exhausted its bounded round-robin cap on
/// a large prime field; the formula may still be SAT outside the range
/// we tried.  Callers must NOT treat `Unknown` as UNSAT.
#[derive(Debug)]
pub enum SplitFindZeroOutcome {
    Sat(Vec<FfEl>),
    Unsat,
    Unknown,
}

/// Cancel-aware model search.  Returns `Sat / Unsat / Unknown` on success;
/// `Err(Cancelled)` on timeout.
pub fn split_find_zero_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    split_basis: SplitGb<'r>,
    bit_prop: &mut BitProp<'r>,
    cancel: &CancelToken,
) -> Result<SplitFindZeroOutcome, Cancelled> {
    let mut split_basis = split_basis;
    loop {
        if cancel.is_cancelled() { return Err(Cancelled); }

        let mut all_gens: Vec<Poly> = Vec::new();
        for b in &split_basis {
            for p in &b.basis {
                all_gens.push(poly_ring.ring.clone_el(p));
            }
        }
        let null_partial: PartialPoint = vec![None; poly_ring.n_vars];

        let cur_bases: SplitGb<'r> = split_basis.iter()
            .map(|b| {
                let basis_clone: Vec<Poly> = b.basis.iter()
                    .map(|p| poly_ring.ring.clone_el(p))
                    .collect();
                Ideal::from_gb(poly_ring, basis_clone)
            })
            .collect();

        let result = split_zero_extend_cancel(poly_ring, &all_gens, cur_bases, null_partial, bit_prop, cancel);
        match result {
            ZeroExtendResult::Conflict(c) => {
                let new_polys: Vec<Vec<Poly>> = split_basis.iter()
                    .map(|_| vec![poly_ring.ring.clone_el(&c)])
                    .collect();
                split_basis = split_gb_extend_cancel(
                    poly_ring, split_basis, new_polys, bit_prop, cancel,
                )?;
            }
            ZeroExtendResult::NoZero { exhaustive: true } => {
                return Ok(SplitFindZeroOutcome::Unsat);
            }
            ZeroExtendResult::NoZero { exhaustive: false } => {
                return Ok(SplitFindZeroOutcome::Unknown);
            }
            ZeroExtendResult::Cancelled => {
                return Err(Cancelled);
            }
            ZeroExtendResult::Point(pt) => return Ok(SplitFindZeroOutcome::Sat(pt)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::FfField;
    use num_bigint::BigUint;

    fn ff(p: u32) -> FfField { FfField::new(&BigUint::from(p)) }

    #[test]
    fn test_admit() {
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let lin1 = pr.var(0); // 1 term, deg 1 -> admit by both
        let lin2 = pr.add(pr.var(0), pr.var(1)); // 2 terms, deg 1
        let nonlin = pr.mul(pr.var(0), pr.var(1));
        let lin3 = pr.add(pr.add(pr.var(0), pr.var(1)), pr.one()); // 3 terms, deg 1
        assert!(admit(&pr, 0, &lin1));
        assert!(admit(&pr, 1, &lin1));
        assert!(admit(&pr, 0, &lin2));
        assert!(admit(&pr, 1, &lin2));
        assert!(!admit(&pr, 0, &nonlin));
        assert!(!admit(&pr, 1, &nonlin));
        // lin3: 3 terms, deg 1 -> basis 0 admits (deg<=1), basis 1 rejects (terms>2)
        assert!(admit(&pr, 0, &lin3));
        assert!(!admit(&pr, 1, &lin3));
    }

    #[test]
    fn test_split_gb_simple_sat() {
        // x*y - 1 = 0,  x = 2  →  y = 4 in GF(7)
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let xy = pr.mul(pr.var(0), pr.var(1));
        let p1 = pr.sub(xy, pr.one());
        let two = pr.field.from_int(2);
        let p2 = pr.sub(pr.var(0), pr.constant(two));

        let mut bp = BitProp::new(&pr);
        let gens: Vec<Vec<Poly>> = vec![vec![pr.clone_poly(&p2)], vec![p1, p2]];
        let basis = split_gb(&pr, gens, &mut bp);
        assert!(!basis.iter().any(|b| b.is_whole_ring()));
        let pt = match split_find_zero(&pr, basis, &mut bp) {
            SplitFindZeroOutcome::Sat(pt) => pt,
            other => panic!("expected SAT, got {:?}", other),
        };
        // Check x = 2, y = 4 (or the other valid roots; should satisfy x*y=1).
        let x_val = pr.field.to_biguint(&pt[0]);
        let y_val = pr.field.to_biguint(&pt[1]);
        assert_eq!(x_val, BigUint::from(2u32));
        let prod = (x_val * y_val) % BigUint::from(7u32);
        assert_eq!(prod, BigUint::from(1u32));
    }

    #[test]
    fn test_split_gb_unsat() {
        // x = 2, x = 3 in GF(7): UNSAT
        let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
        let two = pr.field.from_int(2);
        let three = pr.field.from_int(3);
        let p1 = pr.sub(pr.var(0), pr.constant(two));
        let p2 = pr.sub(pr.var(0), pr.constant(three));
        let mut bp = BitProp::new(&pr);
        let basis = split_gb(&pr, vec![vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
                                       vec![p1, p2]], &mut bp);
        assert!(basis.iter().any(|b| b.is_whole_ring()));
    }

    #[test]
    fn test_apply_rule_round_robin_interleaves() {
        // Positive-dim ideal: empty (no constraints) over GF(5), 2 vars.
        // Should fall through to round-robin.  Verify the order:
        // (x,0), (y,0), (x,1), (y,1), (x,2), (y,2), (x,3), (y,3), (x,4), (y,4).
        let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
        let gb: Ideal = Ideal::from_gb(&pr, vec![]);
        let r: PartialPoint = vec![None, None];
        let mut brancher = apply_rule(&pr, &gb, &r);
        // first 2 candidates should be (0, 0) and (1, 0): same val, different var.
        let c0 = brancher.next(&pr.field).unwrap();
        assert_eq!(c0.0, 0);
        assert_eq!(pr.field.to_biguint(&c0.1), num_bigint::BigUint::from(0u32));
        let c1 = brancher.next(&pr.field).unwrap();
        assert_eq!(c1.0, 1);
        assert_eq!(pr.field.to_biguint(&c1.1), num_bigint::BigUint::from(0u32));
        // third candidate: var 0 again, val 1.
        let c2 = brancher.next(&pr.field).unwrap();
        assert_eq!(c2.0, 0);
        assert_eq!(pr.field.to_biguint(&c2.1), num_bigint::BigUint::from(1u32));
    }

    #[test]
    fn test_apply_rule_univariate() {
        // GB has y^2 - 4 = 0; should enumerate roots of y over GF(7) (i.e., 2 and 5).
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let four = pr.field.from_int(4);
        let y_sq = pr.mul(pr.var(1), pr.var(1));
        let p = pr.sub(y_sq, pr.constant(four));
        let gb = Ideal::new(&pr, vec![p]);
        let r: PartialPoint = vec![None, None];
        let mut brancher = apply_rule(&pr, &gb, &r);
        // Collect all candidates
        let mut cands = Vec::new();
        while let Some(c) = brancher.next(&pr.field) {
            cands.push(c);
        }
        // All candidates should be for variable 1 (y).
        assert!(cands.iter().all(|(v, _)| *v == 1));
        // Roots should include 2 and 5.
        let vals: Vec<num_bigint::BigUint> = cands.iter().map(|(_, v)| pr.field.to_biguint(v)).collect();
        assert!(vals.contains(&num_bigint::BigUint::from(2u32)));
        assert!(vals.contains(&num_bigint::BigUint::from(5u32)));
    }
}
