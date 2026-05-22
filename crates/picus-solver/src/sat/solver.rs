//! CDCL solver core.
//!
//! [`Solver`] implements the full CDCL loop: BCP via watched literals
//! ([`Solver::propagate`]), 1-UIP conflict analysis with VSIDS
//! activity bumps ([`Solver::analyze`]), backjumping
//! ([`Solver::backtrack_to`]), Luby-sequence restarts
//! ([`Solver::should_restart`] + [`perform_restart`]), and a top-level
//! [`Solver::solve`] driver. Theory clients call
//! [`Solver::add_theory_lemma`] to inject conflict / propagation
//! clauses and read assignments via [`Solver::value`] +
//! [`Solver::trail`].

use super::clause::{Clause, ClauseArena, ClauseRef};
use super::lit::{LBool, Lit, Var};

/// Outcome of a top-level `solve` call.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SolveResult {
    Sat,
    Unsat,
    Unknown,
}

/// CDCL solver state.
pub struct Solver {
    /// Number of allocated propositional variables.
    n_vars: usize,
    /// Per-variable current value (`assigns[var.index()]`).
    assigns: Vec<LBool>,
    /// Per-variable decision level (`level[var.index()]`). Meaningless
    /// when `assigns[v] == Undef`.
    level: Vec<i32>,
    /// Reason clause for each variable, or `None` if the assignment was
    /// a decision (not a propagation) or set at root by a unit input.
    reason: Vec<Option<ClauseRef>>,
    /// Assignment trail in commit order.
    trail: Vec<Lit>,
    /// `trail_lim[d]` = index in `trail` where decision level `d + 1`
    /// begins.
    trail_lim: Vec<usize>,
    /// Index into `trail` of the next literal whose propagation
    /// consequences have not yet been processed.
    qhead: usize,
    /// Clause arena (original + learnt).
    arena: ClauseArena,
    /// Per-literal watch lists. `watches[lit.index()]` contains every
    /// clause currently watching `lit` (one of its two watched literals
    /// equals `lit`).
    watches: Vec<Vec<ClauseRef>>,
    /// Persisted UNSAT flag (set by `add_clause` when an input clause
    /// is empty, or by `propagate` at decision level 0).
    unsat: bool,
    /// VSIDS activity score per variable. Bumped when the variable
    /// participates in conflict-clause resolution; decayed implicitly
    /// by growing `var_inc`.
    var_activity: Vec<f64>,
    /// Current activity bump amount. Multiplied by `var_decay` after
    /// each conflict so newer conflicts dominate older ones.
    var_inc: f64,
    /// Decay multiplier applied to `var_inc` per conflict (>1.0).
    var_decay: f64,
    /// Saved polarity per variable (last value assigned, kept across
    /// backtracks). Used by `pick_decision` for phase saving.
    saved_phase: Vec<LBool>,
    /// Cumulative conflict count. Incremented by `analyze`.
    n_conflicts: u64,
    /// Next conflict count at which a restart should fire.
    restart_step: u64,
    /// Base restart interval (conflicts) multiplied by the Luby
    /// sequence to derive successive thresholds.
    restart_base: u64,
    /// 1-indexed Luby sequence position for the next restart.
    luby_idx: u64,
    /// Max-heap on `var_activity` for [`Self::pick_decision`]. Vars
    /// are popped when selected, re-inserted on backtrack.
    order_heap: Vec<Var>,
    /// Index of each variable in `order_heap`, or `usize::MAX` when
    /// absent. Enables O(log n) percolate-up after a bump.
    heap_pos: Vec<usize>,
}

impl Solver {
    pub fn new() -> Self {
        Solver {
            n_vars: 0,
            assigns: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            arena: ClauseArena::new(),
            watches: Vec::new(),
            unsat: false,
            var_activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 1.05,
            saved_phase: Vec::new(),
            n_conflicts: 0,
            restart_step: 100,
            restart_base: 100,
            luby_idx: 1,
            order_heap: Vec::new(),
            heap_pos: Vec::new(),
        }
    }

    /// Allocate a fresh propositional variable.
    pub fn new_var(&mut self) -> Var {
        let v = Var(self.n_vars as u32);
        self.n_vars += 1;
        self.assigns.push(LBool::Undef);
        self.level.push(-1);
        self.reason.push(None);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.var_activity.push(0.0);
        self.saved_phase.push(LBool::Undef);
        self.heap_pos.push(usize::MAX);
        self.heap_insert(v);
        v
    }

    fn bump_var_activity(&mut self, v: Var) {
        self.var_activity[v.index()] += self.var_inc;
        if self.var_activity[v.index()] > 1e100 {
            for a in self.var_activity.iter_mut() {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        let pos = self.heap_pos[v.index()];
        if pos != usize::MAX {
            self.heap_percolate_up(pos);
        }
    }

    fn heap_insert(&mut self, v: Var) {
        if self.heap_pos[v.index()] != usize::MAX {
            return;
        }
        let pos = self.order_heap.len();
        self.order_heap.push(v);
        self.heap_pos[v.index()] = pos;
        self.heap_percolate_up(pos);
    }

    fn heap_remove_max(&mut self) -> Option<Var> {
        let n = self.order_heap.len();
        if n == 0 {
            return None;
        }
        let top = self.order_heap[0];
        self.heap_pos[top.index()] = usize::MAX;
        let last = self.order_heap.pop().expect("heap non-empty");
        if n > 1 {
            self.order_heap[0] = last;
            self.heap_pos[last.index()] = 0;
            self.heap_percolate_down(0);
        }
        Some(top)
    }

    fn heap_percolate_up(&mut self, mut i: usize) {
        let v = self.order_heap[i];
        let v_act = self.var_activity[v.index()];
        while i > 0 {
            let parent = (i - 1) / 2;
            let p = self.order_heap[parent];
            if self.var_activity[p.index()] >= v_act {
                break;
            }
            self.order_heap[i] = p;
            self.heap_pos[p.index()] = i;
            i = parent;
        }
        self.order_heap[i] = v;
        self.heap_pos[v.index()] = i;
    }

    /// Sift element at index `i` down while a child has higher activity.
    fn heap_percolate_down(&mut self, mut i: usize) {
        let n = self.order_heap.len();
        let v = self.order_heap[i];
        let v_act = self.var_activity[v.index()];
        loop {
            let l = 2 * i + 1;
            if l >= n {
                break;
            }
            let r = l + 1;
            let best = if r < n
                && self.var_activity[self.order_heap[r].index()]
                    > self.var_activity[self.order_heap[l].index()]
            {
                r
            } else {
                l
            };
            if self.var_activity[self.order_heap[best].index()] <= v_act {
                break;
            }
            let b = self.order_heap[best];
            self.order_heap[i] = b;
            self.heap_pos[b.index()] = i;
            i = best;
        }
        self.order_heap[i] = v;
        self.heap_pos[v.index()] = i;
    }

    fn decay_var_activity(&mut self) {
        self.var_inc *= self.var_decay;
    }

    /// Cumulative conflict count.
    pub fn n_conflicts(&self) -> u64 {
        self.n_conflicts
    }

    /// `true` iff the conflict count has reached the next Luby
    /// restart threshold.
    pub fn should_restart(&self) -> bool {
        self.n_conflicts >= self.restart_step
    }

    /// Backtrack to level 0 and bump the next Luby restart threshold.
    /// Callers in CDCL(T) must also pop any theory-level state down
    /// to match the new decision level.
    pub fn perform_restart(&mut self) {
        self.backtrack_to(0);
        let factor = luby(self.luby_idx);
        self.luby_idx += 1;
        self.restart_step = self.n_conflicts.saturating_add(self.restart_base.saturating_mul(factor));
    }
}

/// `i`-th element of the Luby sequence (1-indexed):
/// `1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, …`.
fn luby(mut i: u64) -> u64 {
    loop {
        let mut k: u32 = 1;
        while (1u64 << k) - 1 < i {
            k += 1;
        }
        if (1u64 << k) - 1 == i {
            return 1u64 << (k - 1);
        }
        i = i - (1u64 << (k - 1)) + 1;
    }
}

impl Solver {

    pub fn n_vars(&self) -> usize {
        self.n_vars
    }

    /// Current value of a variable.
    pub fn value(&self, v: Var) -> LBool {
        self.assigns[v.index()]
    }

    /// Current decision level (0 = root).
    pub fn decision_level(&self) -> i32 {
        self.trail_lim.len() as i32
    }

    /// Has the formula been proved UNSAT at the root?
    pub fn is_unsat(&self) -> bool {
        self.unsat
    }

    /// Value of a literal under the current assignment.
    pub fn lit_value(&self, lit: Lit) -> LBool {
        let v = self.value(lit.var());
        if lit.is_positive() {
            v
        } else {
            v.negate()
        }
    }

    /// Add a clause from the input formula. Returns `false` if the
    /// formula is trivially UNSAT at the root level (an empty clause
    /// was added, or unit propagation produced an immediate
    /// contradiction).
    ///
    /// Assumes the solver is at decision level 0 and propagation is
    /// quiet (post-`new` or post-clean restart).
    pub fn add_clause(&mut self, mut lits: Vec<Lit>) -> bool {
        if self.unsat {
            return false;
        }
        debug_assert_eq!(self.decision_level(), 0);

        // Drop duplicates; detect tautology (`x ∨ ¬x`).
        lits.sort_by_key(|l| l.raw());
        let mut i = 0usize;
        let mut j = 1usize;
        while j < lits.len() {
            if lits[j] == lits[i] {
                j += 1;
                continue;
            }
            if lits[j] == -lits[i] {
                // Tautology: discard the whole clause.
                return true;
            }
            i += 1;
            lits[i] = lits[j];
            j += 1;
        }
        lits.truncate(i + 1);

        // Simplify by current root-level assignment: drop false lits,
        // shortcut if any is true.
        let mut simplified: Vec<Lit> = Vec::with_capacity(lits.len());
        for l in lits {
            match self.lit_value(l) {
                LBool::True => return true,
                LBool::False => {}
                LBool::Undef => simplified.push(l),
            }
        }

        if simplified.is_empty() {
            self.unsat = true;
            return false;
        }
        if simplified.len() == 1 {
            // Unit clause: enqueue without a reason (root-level fact)
            // and propagate immediately so root-level conflicts are
            // reported by `add_clause` itself.
            if !self.enqueue(simplified[0], None) {
                self.unsat = true;
                return false;
            }
            if self.propagate().is_some() {
                // `propagate` set `self.unsat` to true (decision_level == 0).
                return false;
            }
            return true;
        }

        // Add to arena and watch the first two literals. Convention:
        // `watches[lit]` contains every clause where `lit` is in one
        // of the two watched positions; the list is consulted when
        // `lit` becomes False (equivalently when `-lit` is enqueued
        // True).
        let cref = self.arena.add(Clause::new(simplified.clone(), false));
        let lits = &self.arena.get(cref).lits;
        let w0 = lits[0];
        let w1 = lits[1];
        self.watches[w0.index()].push(cref);
        self.watches[w1.index()].push(cref);
        true
    }

    /// Decide a fresh literal: open a new decision level and enqueue
    /// `lit` as a decision (no reason). Returns `false` when the
    /// literal is already assigned to the opposite value.
    pub fn decide(&mut self, lit: Lit) -> bool {
        let v = lit.var();
        match self.assigns[v.index()] {
            LBool::Undef => {
                self.trail_lim.push(self.trail.len());
                self.enqueue(lit, None)
            }
            LBool::True => lit.is_positive(),
            LBool::False => !lit.is_positive(),
        }
    }

    /// Assign `lit` to True with the given reason. Returns `false`
    /// when the assignment conflicts with the existing value of
    /// `lit.var()` (i.e. we are trying to assign True to something
    /// already False).
    fn enqueue(&mut self, lit: Lit, reason: Option<ClauseRef>) -> bool {
        let v = lit.var();
        match self.assigns[v.index()] {
            LBool::Undef => {
                let polarity = lit.is_positive();
                self.assigns[v.index()] = LBool::from_bool(polarity);
                self.level[v.index()] = self.decision_level();
                self.reason[v.index()] = reason;
                self.trail.push(lit);
                self.saved_phase[v.index()] = LBool::from_bool(polarity);
                true
            }
            LBool::True => lit.is_positive(),
            LBool::False => !lit.is_positive(),
        }
    }

    /// Watched-literal unit propagation. Returns `Some(conflict)` for
    /// the first clause whose literals are all False under the current
    /// assignment, or `None` when the queue drains without conflict.
    pub fn propagate(&mut self) -> Option<ClauseRef> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            // Take `watches[-p]` out so we can mutate `self` while iterating.
            let neg_p_idx = (-p).index();
            let mut watchers = std::mem::take(&mut self.watches[neg_p_idx]);
            let mut write = 0usize;
            let mut read = 0usize;
            let mut conflict: Option<ClauseRef> = None;
            'next_clause: while read < watchers.len() {
                let cref = watchers[read];
                read += 1;
                // Place `-p` at index 1; the other watched literal is at 0.
                let other;
                let lits_len;
                {
                    let clause = self.arena.get_mut(cref);
                    if clause.lits[0] == -p {
                        clause.lits.swap(0, 1);
                    }
                    debug_assert_eq!(clause.lits[1], -p);
                    other = clause.lits[0];
                    lits_len = clause.lits.len();
                }
                let other_value = self.lit_value(other);
                if other_value == LBool::True {
                    // Already satisfied; keep this watcher.
                    watchers[write] = cref;
                    write += 1;
                    continue 'next_clause;
                }
                // Look for a replacement watched literal in positions ≥ 2.
                let mut replacement: Option<usize> = None;
                {
                    let clause = self.arena.get(cref);
                    for k in 2..lits_len {
                        if self.lit_value(clause.lits[k]) != LBool::False {
                            replacement = Some(k);
                            break;
                        }
                    }
                }
                if let Some(k) = replacement {
                    let new_watch = {
                        let clause = self.arena.get_mut(cref);
                        clause.lits.swap(1, k);
                        clause.lits[1]
                    };
                    self.watches[new_watch.index()].push(cref);
                    continue 'next_clause;
                }
                // No replacement: unit or conflict.
                watchers[write] = cref;
                write += 1;
                if other_value == LBool::False {
                    // Conflict: preserve remaining watchers.
                    while read < watchers.len() {
                        watchers[write] = watchers[read];
                        write += 1;
                        read += 1;
                    }
                    conflict = Some(cref);
                    break 'next_clause;
                }
                let ok = self.enqueue(other, Some(cref));
                debug_assert!(ok, "unit-propagated literal must be Undef");
            }
            watchers.truncate(write);
            self.watches[neg_p_idx] = watchers;
            if conflict.is_some() {
                if self.decision_level() == 0 {
                    self.unsat = true;
                }
                return conflict;
            }
        }
        None
    }

    /// Number of clauses in the arena. Test-only helper for SAT-layer
    /// assertions; production code uses observer hooks for counting.
    #[cfg(test)]
    pub fn n_clauses(&self) -> usize {
        self.arena.len()
    }

    #[allow(dead_code)]
    pub(crate) fn arena(&self) -> &ClauseArena {
        &self.arena
    }

    /// View of the trail (in commit order).
    pub fn trail(&self) -> &[Lit] {
        &self.trail
    }

    /// Add a theory-supplied lemma clause. All literals must currently
    /// be False. Sorts by descending decision level, computes the
    /// assertion level (largest literal-level strictly less than the
    /// max, or `max_level - 1` if every literal sits at the max),
    /// backtracks, then registers via [`Self::learn_clause`]. Returns
    /// `false` when the lemma forces root-level UNSAT.
    pub fn add_theory_lemma(&mut self, lits: Vec<Lit>) -> bool {
        self.add_theory_lemma_with_trail(lits).is_some()
    }

    /// Like [`Self::add_theory_lemma`], but on success returns the trail
    /// length right after the internal backtrack and before
    /// `learn_clause` enqueues the asserting literal. Callers thread
    /// this through their `notified` pointer so the asserting literal
    /// is included in the next theory-notify pass.
    pub fn add_theory_lemma_with_trail(&mut self, mut lits: Vec<Lit>) -> Option<usize> {
        if lits.is_empty() {
            self.unsat = true;
            return None;
        }
        lits.sort_by_key(|&l| std::cmp::Reverse(self.level[l.var().index()]));
        let max_level = self.level[lits[0].var().index()];
        if max_level <= 0 {
            self.unsat = true;
            return None;
        }
        let assertion_level = lits
            .iter()
            .skip(1)
            .map(|l| self.level[l.var().index()])
            .filter(|&lv| lv < max_level && lv >= 0)
            .max()
            .unwrap_or(max_level - 1);
        self.backtrack_to(assertion_level);
        let trail_pre_lemma = self.trail.len();
        self.learn_clause(lits);
        Some(trail_pre_lemma)
    }

    /// Number of literals on the trail.
    pub fn trail_len(&self) -> usize {
        self.trail.len()
    }

    /// `true` iff every variable has a defined value (no decision
    /// variable remains).
    pub fn all_assigned(&self) -> bool {
        self.trail.len() == self.n_vars
    }

    /// 1-UIP conflict analysis. Returns `(learnt, bt_level)` where
    /// `learnt[0]` is the asserting literal (negated 1-UIP), `learnt[1..]`
    /// are lower-level literals, and `bt_level` is the second-highest
    /// decision level among the learnt clause (0 if length 1).
    pub fn analyze(&mut self, conflict: ClauseRef) -> (Vec<Lit>, i32) {
        let cur_level = self.decision_level();
        debug_assert!(cur_level > 0, "analyze called at root level");
        self.n_conflicts += 1;

        let mut seen = vec![false; self.n_vars];
        // `seen` is cleared during the trail walk; `to_bump` records the
        // full touched set so VSIDS bumps the 1-UIP and intermediate
        // resolved vars too, not only the `learnt[1..]` survivors.
        let mut to_bump = vec![false; self.n_vars];
        let mut learnt: Vec<Lit> = vec![Lit::pos(Var(0)); 1]; // placeholder at index 0
        let mut counter: i32 = 0;
        let mut pivot: Option<Lit> = None;
        let mut conf = Some(conflict);
        let mut trail_idx = self.trail.len();

        loop {
            let cref = conf.expect("conflict must be set");
            let clause = self.arena.get(cref);
            for &q in &clause.lits {
                if Some(q) == pivot {
                    continue;
                }
                let vq = q.var();
                if seen[vq.index()] {
                    continue;
                }
                let lvl = self.level[vq.index()];
                if lvl <= 0 {
                    // Root-level literals simplify away.
                    continue;
                }
                seen[vq.index()] = true;
                to_bump[vq.index()] = true;
                if lvl == cur_level {
                    counter += 1;
                } else {
                    learnt.push(q);
                }
            }
            let next_lit = loop {
                debug_assert!(trail_idx > 0, "trail exhausted before 1-UIP");
                trail_idx -= 1;
                let l = self.trail[trail_idx];
                if seen[l.var().index()] {
                    break l;
                }
            };
            seen[next_lit.var().index()] = false;
            counter -= 1;
            if counter == 0 {
                pivot = Some(next_lit);
                break;
            }
            conf = self.reason[next_lit.var().index()];
            debug_assert!(conf.is_some(), "non-final pivot must have a reason");
            pivot = Some(next_lit);
        }

        let asserting = -pivot.expect("pivot set on loop exit");
        learnt[0] = asserting;

        let bt_level = if learnt.len() == 1 {
            0
        } else {
            learnt[1..]
                .iter()
                .map(|l| self.level[l.var().index()])
                .max()
                .unwrap_or(0)
        };

        for i in 0..self.n_vars {
            if to_bump[i] {
                self.bump_var_activity(Var(i as u32));
            }
        }
        self.decay_var_activity();

        (learnt, bt_level)
    }

    /// Cancel assignments down to (but not including) `level + 1`, so
    /// the next decision will be at level `level + 1`. `qhead` is reset
    /// to the current trail length so propagation re-examines the
    /// surviving prefix. Any variable unassigned here is re-inserted
    /// into the activity heap so [`Self::pick_decision`] can pick it.
    pub fn backtrack_to(&mut self, level: i32) {
        debug_assert!(level >= 0);
        debug_assert!(level <= self.decision_level());
        if level >= self.decision_level() {
            return;
        }
        let limit = self.trail_lim[level as usize];
        while self.trail.len() > limit {
            let lit = self.trail.pop().expect("trail invariant");
            let v = lit.var();
            self.assigns[v.index()] = LBool::Undef;
            self.level[v.index()] = -1;
            self.reason[v.index()] = None;
            self.heap_insert(v);
        }
        self.trail_lim.truncate(level as usize);
        self.qhead = self.trail.len();
    }

    /// Run CDCL to completion. Returns `Sat` once every variable has
    /// a value, `Unsat` on a root-level conflict, or `Unknown` if an
    /// external limit (none defined in this module) cuts the search.
    ///
    /// Decision strategy: lowest-index Undef variable, positive
    /// polarity. Replace [`Self::pick_decision`] for a richer heuristic.
    pub fn solve(&mut self) -> SolveResult {
        if self.unsat {
            return SolveResult::Unsat;
        }
        // Drain any pending root-level propagation. `add_clause` already
        // propagates after each unit, but later callers may have
        // enqueued without propagating.
        if self.propagate().is_some() {
            return SolveResult::Unsat;
        }
        loop {
            let next = self.pick_decision();
            let lit = match next {
                None => return SolveResult::Sat,
                Some(l) => l,
            };
            let ok = self.decide(lit);
            debug_assert!(ok, "picked literal must be Undef");
            // Inner conflict loop: keep propagating + learning until
            // either propagation is quiet (back to decision picking) or
            // a root-level conflict is detected (UNSAT).
            loop {
                match self.propagate() {
                    None => break,
                    Some(conflict) => {
                        if self.decision_level() == 0 {
                            return SolveResult::Unsat;
                        }
                        let (learnt, bt) = self.analyze(conflict);
                        self.backtrack_to(bt);
                        self.learn_clause(learnt);
                        if self.should_restart() {
                            self.perform_restart();
                            break;
                        }
                    }
                }
            }
        }
    }

    /// Pop the highest-activity Undef variable from the heap, applying
    /// the saved phase (positive when none was saved).
    pub fn pick_decision(&mut self) -> Option<Lit> {
        while let Some(v) = self.heap_remove_max() {
            if matches!(self.assigns[v.index()], LBool::Undef) {
                let lit = match self.saved_phase[v.index()] {
                    LBool::False => Lit::neg(v),
                    _ => Lit::pos(v),
                };
                return Some(lit);
            }
        }
        None
    }

    /// Enqueue a theory-propagated literal with a justification clause
    /// `(lit ∨ ¬r_i …)` added (learnt) and watched. Requires `lit` Undef
    /// and `reason_facts` non-empty (each currently True); returns
    /// `false` otherwise.
    pub fn enqueue_theory(&mut self, lit: Lit, reason_facts: Vec<Lit>) -> bool {
        if !matches!(self.value(lit.var()), LBool::Undef) {
            return false;
        }
        if reason_facts.is_empty() {
            return false;
        }
        let mut clause_lits: Vec<Lit> = Vec::with_capacity(reason_facts.len() + 1);
        clause_lits.push(lit);
        let mut reason_neg: Vec<Lit> = reason_facts.iter().map(|&r| -r).collect();
        // lits[1] = highest-level reason negation, mirroring `learn_clause`.
        reason_neg.sort_by_key(|&l| std::cmp::Reverse(self.level[l.var().index()]));
        for r in &reason_neg {
            debug_assert!(
                matches!(self.lit_value(*r), LBool::False),
                "negated reason fact must be currently False"
            );
        }
        clause_lits.extend(reason_neg);
        let cref = self.arena.add(Clause::new(clause_lits, true));
        let lits_ref = &self.arena.get(cref).lits;
        let w0 = lits_ref[0];
        let w1 = lits_ref[1];
        self.watches[w0.index()].push(cref);
        self.watches[w1.index()].push(cref);
        self.enqueue(lit, Some(cref))
    }

    /// Add a learnt clause and enqueue its asserting literal (`lits[0]`).
    /// Assumes the solver has already backtracked to the asserting
    /// level (i.e. all literals in `lits[1..]` are currently False and
    /// `lits[0]` is currently Undef).
    pub fn learn_clause(&mut self, lits: Vec<Lit>) -> ClauseRef {
        debug_assert!(!lits.is_empty(), "cannot learn empty clause");
        let asserting = lits[0];
        if lits.len() == 1 {
            let cref = self.arena.add(Clause::new(lits, true));
            let ok = self.enqueue(asserting, Some(cref));
            debug_assert!(ok, "asserting literal must be Undef before learning");
            return cref;
        }
        // Watch lits[0] (1-UIP) and lits[1] (next-highest level, per
        // analyze()'s ordering invariant).
        let cref = self.arena.add(Clause::new(lits, true));
        let lits_ref = &self.arena.get(cref).lits;
        let w0 = lits_ref[0];
        let w1 = lits_ref[1];
        self.watches[w0.index()].push(cref);
        self.watches[w1.index()].push(cref);
        let ok = self.enqueue(asserting, Some(cref));
        debug_assert!(ok, "asserting literal must be Undef before learning");
        cref
    }
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_solver() {
        let s = Solver::new();
        assert_eq!(s.n_vars(), 0);
        assert_eq!(s.decision_level(), 0);
    }

    #[test]
    fn new_vars_have_undef_value() {
        let mut s = Solver::new();
        let v0 = s.new_var();
        let v1 = s.new_var();
        let v2 = s.new_var();
        assert_eq!(v0, Var(0));
        assert_eq!(v1, Var(1));
        assert_eq!(v2, Var(2));
        assert_eq!(s.n_vars(), 3);
        assert_eq!(s.value(v0), LBool::Undef);
        assert_eq!(s.value(v1), LBool::Undef);
        assert_eq!(s.value(v2), LBool::Undef);
    }

    #[test]
    fn watch_slots_allocated_per_polarity() {
        let mut s = Solver::new();
        s.new_var();
        s.new_var();
        // 2 vars × 2 polarities = 4 watch lists.
        assert_eq!(s.watches.len(), 4);
    }

    fn vars(s: &mut Solver, n: usize) -> Vec<Var> {
        (0..n).map(|_| s.new_var()).collect()
    }

    #[test]
    fn add_unit_clause_propagates_at_root() {
        let mut s = Solver::new();
        let v = vars(&mut s, 1);
        // Clause: (x0)
        assert!(s.add_clause(vec![Lit::pos(v[0])]));
        assert_eq!(s.value(v[0]), LBool::True);
        assert!(s.propagate().is_none());
    }

    #[test]
    fn empty_clause_marks_unsat() {
        let mut s = Solver::new();
        assert!(!s.add_clause(Vec::new()));
        assert!(s.is_unsat());
    }

    #[test]
    fn contradictory_units_at_root_unsat() {
        let mut s = Solver::new();
        let v = vars(&mut s, 1);
        assert!(s.add_clause(vec![Lit::pos(v[0])]));
        // (¬x0) conflicts with the previous unit at root.
        let ok = s.add_clause(vec![Lit::neg(v[0])]);
        // The second clause simplifies to empty under the existing
        // root assignment ⇒ UNSAT.
        assert!(!ok);
        assert!(s.is_unsat());
    }

    #[test]
    fn tautology_is_discarded() {
        let mut s = Solver::new();
        let v = vars(&mut s, 1);
        // (x0 ∨ ¬x0) — discarded.
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[0])]));
        assert_eq!(s.n_clauses(), 0);
        assert_eq!(s.value(v[0]), LBool::Undef);
    }

    #[test]
    fn duplicate_literals_collapsed() {
        let mut s = Solver::new();
        let v = vars(&mut s, 1);
        // (x0 ∨ x0) — collapses to unit (x0).
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[0])]));
        assert_eq!(s.value(v[0]), LBool::True);
    }

    #[test]
    fn binary_clause_unit_propagates() {
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        // (x0 ∨ x1) and (¬x0). After both adds, x1 must be true.
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::neg(v[0])]));
        // Propagate to consume the queue.
        assert!(s.propagate().is_none());
        assert_eq!(s.value(v[0]), LBool::False);
        assert_eq!(s.value(v[1]), LBool::True);
    }

    #[test]
    fn propagation_chain_three_clauses() {
        let mut s = Solver::new();
        let v = vars(&mut s, 3);
        // (¬x0 ∨ x1) (¬x1 ∨ x2) (x0)  ⇒  all positive.
        assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::neg(v[1]), Lit::pos(v[2])]));
        assert!(s.add_clause(vec![Lit::pos(v[0])]));
        assert!(s.propagate().is_none());
        assert_eq!(s.value(v[0]), LBool::True);
        assert_eq!(s.value(v[1]), LBool::True);
        assert_eq!(s.value(v[2]), LBool::True);
    }

    #[test]
    fn propagation_detects_conflict() {
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        // (x0 ∨ x1) (¬x1) (¬x0)  →  conflict at root.
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::neg(v[1])]));
        let ok = s.add_clause(vec![Lit::neg(v[0])]);
        assert!(!ok);
        assert!(s.is_unsat());
    }

    #[test]
    fn analyze_simple_binary_conflict() {
        // Clauses:  (x0 ∨ x1)   (x0 ∨ ¬x1)
        // Decide x0=False at level 1; propagation:
        //   from (x0 ∨ x1):    forces x1=True
        //   from (x0 ∨ ¬x1):   needs x1=False  → conflict
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[1])]));
        assert!(s.decide(Lit::neg(v[0])));
        let conflict = s.propagate();
        assert!(conflict.is_some(), "expected propagation conflict");
        let (learnt, bt) = s.analyze(conflict.unwrap());
        // 1-UIP should be x0 (decision). Learnt clause asserts -(-x0) = x0.
        assert_eq!(learnt.len(), 1);
        assert_eq!(learnt[0], Lit::pos(v[0]));
        assert_eq!(bt, 0);
    }

    #[test]
    fn backtrack_clears_assignments_above_level() {
        let mut s = Solver::new();
        let v = vars(&mut s, 3);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.decide(Lit::neg(v[0]))); // level 1: x0=False
        assert!(s.propagate().is_none());
        assert_eq!(s.value(v[0]), LBool::False);
        assert_eq!(s.value(v[1]), LBool::True);
        assert_eq!(s.decision_level(), 1);

        // Decide x2 at level 2 to ensure we have something to undo.
        assert!(s.decide(Lit::pos(v[2])));
        assert_eq!(s.decision_level(), 2);
        assert_eq!(s.value(v[2]), LBool::True);

        // Backtrack to level 0: every assignment vanishes.
        s.backtrack_to(0);
        assert_eq!(s.decision_level(), 0);
        assert_eq!(s.value(v[0]), LBool::Undef);
        assert_eq!(s.value(v[1]), LBool::Undef);
        assert_eq!(s.value(v[2]), LBool::Undef);
        assert!(s.trail().is_empty());
    }

    #[test]
    fn learn_then_propagate_drives_decision() {
        // Same setup as `analyze_simple_binary_conflict`: after learning
        // the unit `(x0)`, backtracking to level 0 and re-propagating
        // must force x0=True (and then x1=True from the original).
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[1])]));
        assert!(s.decide(Lit::neg(v[0])));
        let conflict = s.propagate().expect("conflict expected");
        let (learnt, bt) = s.analyze(conflict);
        s.backtrack_to(bt);
        s.learn_clause(learnt);
        assert!(s.propagate().is_none());
        assert_eq!(s.value(v[0]), LBool::True);
    }

    #[test]
    fn solve_trivial_sat() {
        // (x0 ∨ x1) — many models exist.
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert_eq!(s.solve(), SolveResult::Sat);
    }

    #[test]
    fn solve_trivial_unsat() {
        // (x0) (¬x0) — root-level conflict.
        let mut s = Solver::new();
        let v = vars(&mut s, 1);
        assert!(s.add_clause(vec![Lit::pos(v[0])]));
        // Adding the second is detected as root UNSAT by add_clause.
        assert!(!s.add_clause(vec![Lit::neg(v[0])]));
        assert_eq!(s.solve(), SolveResult::Unsat);
    }

    #[test]
    fn solve_backtrack_required() {
        // 3-var formula requiring at least one wrong guess + learn.
        //   (x0 ∨ x1)
        //   (x0 ∨ x2)
        //   (¬x1 ∨ ¬x2)
        // Deciding ¬x0 forces x1 and x2 both True → contradiction with
        // (¬x1 ∨ ¬x2). Learnt unit (x0); re-propagate → SAT with
        // x0=True.
        let mut s = Solver::new();
        let v = vars(&mut s, 3);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[2])]));
        assert!(s.add_clause(vec![Lit::neg(v[1]), Lit::neg(v[2])]));
        assert_eq!(s.solve(), SolveResult::Sat);
        assert_eq!(s.value(v[0]), LBool::True);
    }

    #[test]
    fn solve_unsat_via_learning() {
        // (x0 ∨ x1) (¬x0 ∨ x1) (x0 ∨ ¬x1) (¬x0 ∨ ¬x1) ── UNSAT.
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[1])]));
        assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::neg(v[1])]));
        assert_eq!(s.solve(), SolveResult::Unsat);
    }

    #[test]
    fn solve_satisfies_model_consistency() {
        // 5-var random-style SAT formula. After solve == Sat we check
        // every clause has at least one True literal under the
        // returned model.
        let mut s = Solver::new();
        let v = vars(&mut s, 5);
        let clauses: Vec<Vec<Lit>> = vec![
            vec![Lit::pos(v[0]), Lit::neg(v[1]), Lit::pos(v[2])],
            vec![Lit::neg(v[0]), Lit::pos(v[3])],
            vec![Lit::pos(v[1]), Lit::pos(v[4])],
            vec![Lit::neg(v[2]), Lit::neg(v[4])],
            vec![Lit::pos(v[0]), Lit::pos(v[3]), Lit::pos(v[4])],
        ];
        for c in clauses.iter() {
            assert!(s.add_clause(c.clone()));
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        for c in &clauses {
            let satisfied = c.iter().any(|l| s.lit_value(*l) == LBool::True);
            assert!(satisfied, "clause {:?} unsatisfied by model", c);
        }
    }

    #[test]
    fn solve_pigeonhole_3_pigeons_2_holes_unsat() {
        // Classic UNSAT: 3 pigeons in 2 holes. Var x_{i,j} = pigeon i in hole j.
        // Constraints:
        //   each pigeon in some hole: for i in 1..=3, (x_{i,1} ∨ x_{i,2}).
        //   no two pigeons in same hole: for j in 1..=2, for i1<i2,
        //                                  (¬x_{i1,j} ∨ ¬x_{i2,j}).
        let mut s = Solver::new();
        let mut x: Vec<Vec<Var>> = Vec::new();
        for _ in 0..3 {
            x.push((0..2).map(|_| s.new_var()).collect());
        }
        for i in 0..3 {
            assert!(s.add_clause(vec![Lit::pos(x[i][0]), Lit::pos(x[i][1])]));
        }
        for j in 0..2 {
            for i1 in 0..3 {
                for i2 in (i1 + 1)..3 {
                    assert!(s.add_clause(vec![Lit::neg(x[i1][j]), Lit::neg(x[i2][j])]));
                }
            }
        }
        assert_eq!(s.solve(), SolveResult::Unsat);
    }

    #[test]
    fn analyze_propagation_resolves_to_decision() {
        // Clauses:
        //   (a ∨ b)         ── if a=False, forces b=True
        //   (a ∨ c)         ── if a=False, forces c=True
        //   (¬b ∨ ¬c)       ── b and c can't both be True
        //
        // Decide a=False (level 1). Propagation:
        //   from (a ∨ b): b=True
        //   from (a ∨ c): c=True
        //   from (¬b ∨ ¬c): both False ⇒ conflict
        //
        // 1-UIP analysis walks back through reasons of b, c, and the
        // decision a; learnt clause asserts ¬(¬a) = a, with bt_level 0.
        let mut s = Solver::new();
        let v = vars(&mut s, 3);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[2])]));
        assert!(s.add_clause(vec![Lit::neg(v[1]), Lit::neg(v[2])]));
        assert!(s.decide(Lit::neg(v[0])));
        let conflict = s.propagate().expect("conflict expected");
        let (learnt, bt) = s.analyze(conflict);
        assert_eq!(learnt.len(), 1);
        assert_eq!(learnt[0], Lit::pos(v[0]));
        assert_eq!(bt, 0);
    }

    #[test]
    fn satisfied_clause_does_not_propagate() {
        let mut s = Solver::new();
        let v = vars(&mut s, 3);
        // (x0 ∨ x1 ∨ x2)
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::pos(v[2])]));
        // Satisfy with x1.
        assert!(s.add_clause(vec![Lit::pos(v[1])]));
        assert!(s.propagate().is_none());
        // x0 and x2 remain undefined.
        assert_eq!(s.value(v[0]), LBool::Undef);
        assert_eq!(s.value(v[1]), LBool::True);
        assert_eq!(s.value(v[2]), LBool::Undef);
    }

    // ─────────── Luby sequence ───────────

    #[test]
    fn luby_first_15_values() {
        // Standard 1-indexed Luby sequence (cvc5 minisat/core/Solver.cc).
        let expected: [u64; 15] = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        for (i, &want) in expected.iter().enumerate() {
            let got = luby((i + 1) as u64);
            assert_eq!(got, want, "luby({}) = {}; expected {}", i + 1, got, want);
        }
    }

    // ─────────── Phase saving + restart ───────────

    #[test]
    fn phase_saving_remembers_after_backtrack() {
        // Decide x = False, then backtrack to root. The next decision
        // on x should reuse the saved (False) phase.
        let mut s = Solver::new();
        let v = vars(&mut s, 1);
        assert!(s.decide(Lit::neg(v[0])));
        assert_eq!(s.value(v[0]), LBool::False);
        s.backtrack_to(0);
        assert_eq!(s.value(v[0]), LBool::Undef);
        let pick = s.pick_decision().expect("undef var available");
        assert_eq!(pick, Lit::neg(v[0]), "saved phase should drive negative pick");
    }

    #[test]
    fn vsids_prefers_higher_activity_variable() {
        let mut s = Solver::new();
        let v = vars(&mut s, 4);
        assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[3])]));
        assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::neg(v[3])]));
        assert!(s.decide(Lit::pos(v[0])));
        let conflict = s.propagate().expect("conflict expected");
        let (learnt, bt) = s.analyze(conflict);
        assert_eq!(learnt.len(), 1);
        assert_eq!(learnt[0], Lit::neg(v[0]));
        assert_eq!(bt, 0);
        assert!(s.var_activity[0] > 0.0, "1-UIP v[0] must be bumped");
        assert!(s.var_activity[3] > 0.0, "intermediate v[3] must be bumped");
        assert_eq!(s.var_activity[1], 0.0);
        assert_eq!(s.var_activity[2], 0.0);
        s.backtrack_to(0);
        s.learn_clause(learnt);
        assert!(s.propagate().is_none());
        assert_eq!(s.value(v[0]), LBool::False);
        let pick = s.pick_decision().expect("undef var available");
        assert_eq!(pick.var(), v[3]);
    }

    #[test]
    fn vsids_bumps_intermediate_resolved_variables() {
        // VSIDS must bump every variable that participates in the
        // conflict-analysis resolution chain, including the 1-UIP
        // and intermediate resolved variables — not just the
        // literals that survive into the learnt clause. The chosen
        // formula has a 1-UIP that collapses to a unit clause, so
        // a survivors-only bump policy would leave all activities at
        // zero.
        let mut s = Solver::new();
        let v = vars(&mut s, 3);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[2])]));
        assert!(s.add_clause(vec![Lit::neg(v[1]), Lit::neg(v[2])]));
        assert!(s.decide(Lit::neg(v[0])));
        let conflict = s.propagate().expect("conflict expected");
        let (learnt, _) = s.analyze(conflict);
        assert_eq!(learnt.len(), 1, "test premise: 1-UIP collapses to a unit");
        for i in 0..3 {
            assert!(
                s.var_activity[i] > 0.0,
                "v[{}] participated in resolution; activity must be > 0 (got {})",
                i,
                s.var_activity[i],
            );
        }
    }

    #[test]
    fn restart_preserves_root_level_units() {
        let mut s = Solver::new();
        let v = vars(&mut s, 4);
        assert!(s.add_clause(vec![Lit::pos(v[0])]));
        assert!(s.add_clause(vec![Lit::neg(v[1])]));
        assert!(s.decide(Lit::pos(v[2])));
        assert!(s.decide(Lit::pos(v[3])));
        assert_eq!(s.decision_level(), 2);
        s.perform_restart();
        assert_eq!(s.decision_level(), 0);
        assert_eq!(s.value(v[0]), LBool::True);
        assert_eq!(s.value(v[1]), LBool::False);
        assert_eq!(s.value(v[2]), LBool::Undef);
        assert_eq!(s.value(v[3]), LBool::Undef);
    }

    #[test]
    fn enqueue_theory_assigns_with_reason() {
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        assert!(s.decide(Lit::pos(v[0])));
        let before = s.n_clauses();
        let ok = s.enqueue_theory(Lit::pos(v[1]), vec![Lit::pos(v[0])]);
        assert!(ok);
        assert_eq!(s.value(v[1]), LBool::True);
        assert_eq!(s.n_clauses(), before + 1);
        s.backtrack_to(0);
        assert_eq!(s.value(v[0]), LBool::Undef);
        assert_eq!(s.value(v[1]), LBool::Undef);
    }

    #[test]
    fn enqueue_theory_with_multi_level_reasons_sorts_highest_as_second_watch() {
        let mut s = Solver::new();
        let v = vars(&mut s, 5);
        assert!(s.decide(Lit::pos(v[0])));
        assert!(s.decide(Lit::pos(v[1])));
        assert!(s.decide(Lit::pos(v[2])));
        let n_before = s.n_clauses();
        assert!(s.enqueue_theory(
            Lit::pos(v[3]),
            vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::pos(v[2])],
        ));
        let cref = s.reason[v[3].index()].expect("reason set");
        let clause_lits = &s.arena.get(cref).lits;
        assert_eq!(clause_lits[0], Lit::pos(v[3]));
        // Highest-level reason (v[2] at level 3) → lits[1].
        assert_eq!(clause_lits[1], Lit::neg(v[2]));
        assert_eq!(s.n_clauses(), n_before + 1);
    }

    #[test]
    fn enqueue_theory_propagates_again_after_backtrack_via_reason_clause() {
        // Reason clause persists across backtrack and re-fires on
        // re-decision of its reason facts.
        let mut s = Solver::new();
        let v = vars(&mut s, 3);
        assert!(s.decide(Lit::pos(v[0])));
        assert!(s.decide(Lit::pos(v[1])));
        assert!(s.enqueue_theory(Lit::pos(v[2]), vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        s.backtrack_to(1);
        assert_eq!(s.value(v[1]), LBool::Undef);
        assert_eq!(s.value(v[2]), LBool::Undef);
        assert!(s.decide(Lit::pos(v[1])));
        assert!(s.propagate().is_none());
        assert_eq!(s.value(v[2]), LBool::True);
    }

    #[test]
    fn enqueue_theory_reason_clause_shape_and_reason_pointer() {
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        assert!(s.decide(Lit::pos(v[0])));
        assert!(s.enqueue_theory(Lit::pos(v[1]), vec![Lit::pos(v[0])]));
        let cref = s.reason[v[1].index()].expect("reason pointer set");
        let lits = &s.arena.get(cref).lits;
        assert_eq!(lits.len(), 2);
        assert_eq!(lits[0], Lit::pos(v[1]));
        assert_eq!(lits[1], Lit::neg(v[0]));
    }

    #[test]
    fn enqueue_theory_rejects_empty_reason() {
        // Empty reason would yield a length-1 unwatched reason clause.
        let mut s = Solver::new();
        let v = vars(&mut s, 1);
        let before = s.n_clauses();
        assert!(!s.enqueue_theory(Lit::pos(v[0]), Vec::new()));
        assert_eq!(s.value(v[0]), LBool::Undef);
        assert_eq!(s.n_clauses(), before);
    }

    #[test]
    fn enqueue_theory_rejects_assigned_lit() {
        let mut s = Solver::new();
        let v = vars(&mut s, 2);
        assert!(s.decide(Lit::pos(v[0])));
        assert!(s.decide(Lit::pos(v[1])));
        let before = s.n_clauses();
        assert!(!s.enqueue_theory(Lit::pos(v[1]), vec![Lit::pos(v[0])]));
        assert_eq!(s.n_clauses(), before);
    }

    #[test]
    fn perform_restart_resets_decision_level() {
        let mut s = Solver::new();
        let v = vars(&mut s, 3);
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.decide(Lit::neg(v[0])));
        assert!(s.propagate().is_none());
        assert_eq!(s.decision_level(), 1);
        s.perform_restart();
        assert_eq!(s.decision_level(), 0, "restart must return to root");
        // v[0] was a decision (level 1), so it should be cleared.
        assert_eq!(s.value(v[0]), LBool::Undef);
    }
}
