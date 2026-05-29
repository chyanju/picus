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
    let (learnt, bt) = s
        .analyze(conflict.unwrap())
        .expect("analyze produces a clause");
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
    let (learnt, bt) = s.analyze(conflict).expect("analyze produces a clause");
    s.backtrack_to(bt);
    s.learn_clause(learnt);
    assert!(s.propagate().is_none());
    assert_eq!(s.value(v[0]), LBool::True);
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
    assert_eq!(
        pick,
        Lit::neg(v[0]),
        "saved phase should drive negative pick"
    );
}

#[test]
fn vsids_prefers_higher_activity_variable() {
    let mut s = Solver::new();
    let v = vars(&mut s, 4);
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[3])]));
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::neg(v[3])]));
    assert!(s.decide(Lit::pos(v[0])));
    let conflict = s.propagate().expect("conflict expected");
    let (learnt, bt) = s.analyze(conflict).expect("analyze produces a clause");
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
    let (learnt, _) = s.analyze(conflict).expect("analyze produces a clause");
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
fn bump_var_activity_rescales_above_threshold() {
    // When a variable's activity exceeds 1e100 the whole activity array
    // and var_inc are scaled by 1e-100 to avoid float overflow.
    let mut s = Solver::new();
    let v = vars(&mut s, 2);
    // Seed a second variable so we can confirm the array-wide rescale.
    s.var_activity[v[1].index()] = 5.0;
    s.var_activity[v[0].index()] = 1e101;
    let inc_before = s.var_inc;
    s.bump_var_activity(v[0]);
    // v[0] += var_inc (≈1.0) is still > 1e100, so every entry is *1e-100.
    let expected_v0 = (1e101 + inc_before) * 1e-100;
    assert!((s.var_activity[v[0].index()] - expected_v0).abs() < 1e-6);
    assert!((s.var_activity[v[1].index()] - 5.0 * 1e-100).abs() < 1e-110);
    assert!((s.var_inc - inc_before * 1e-100).abs() < 1e-110);
}

#[test]
fn n_conflicts_starts_zero_and_bumps_on_analyze() {
    let mut s = Solver::new();
    let v = vars(&mut s, 2);
    assert_eq!(s.n_conflicts(), 0);
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[1])]));
    assert!(s.decide(Lit::neg(v[0])));
    let conflict = s.propagate().expect("conflict expected");
    let _ = s.analyze(conflict).expect("analyze produces a clause");
    assert_eq!(s.n_conflicts(), 1);
}

#[test]
fn add_clause_after_unsat_returns_false_immediately() {
    let mut s = Solver::new();
    let v = vars(&mut s, 1);
    // Mark UNSAT with an empty clause.
    assert!(!s.add_clause(Vec::new()));
    assert!(s.is_unsat());
    let before = s.n_clauses();
    // Any further add_clause short-circuits to false without processing.
    assert!(!s.add_clause(vec![Lit::pos(v[0])]));
    assert_eq!(s.n_clauses(), before, "no clause stored after UNSAT");
    assert_eq!(s.value(v[0]), LBool::Undef);
}

#[test]
fn add_clause_satisfied_by_root_literal_not_stored() {
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    // Unit (x0) makes x0 True at root.
    assert!(s.add_clause(vec![Lit::pos(v[0])]));
    let before = s.n_clauses();
    // (x0 ∨ x1 ∨ x2) is already satisfied by x0=True ⇒ discarded.
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::pos(v[2])]));
    assert_eq!(s.n_clauses(), before, "satisfied clause must not be stored");
    assert_eq!(s.value(v[1]), LBool::Undef);
    assert_eq!(s.value(v[2]), LBool::Undef);
}

#[test]
fn arena_accessor_reflects_stored_clauses() {
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    assert_eq!(s.arena().len(), 0);
    // Binary clause is stored in the arena.
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
    assert_eq!(s.arena().len(), 1);
    // Force a propagation so a reason ClauseRef points into the arena,
    // then read the stored clause back through the accessor.
    assert!(s.decide(Lit::neg(v[0])));
    assert!(s.propagate().is_none());
    let cref = s.reason[v[1].index()].expect("x1 propagated with a reason");
    let lits = &s.arena().get(cref).lits;
    assert_eq!(lits.len(), 2);
}

#[test]
fn add_theory_lemma_empty_sets_unsat_not_giveup() {
    let mut s = Solver::new();
    let _ = vars(&mut s, 1);
    assert_eq!(s.add_theory_lemma_with_trail(Vec::new()), None);
    assert!(s.is_unsat());
    assert!(!s.gave_up());
}

#[test]
fn add_theory_lemma_two_max_level_lits_resolves_via_analyze() {
    // Conflict lemma with two literals at the top decision level must
    // be routed through 1-UIP analysis + learn rather than learnt raw.
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[2])]));
    assert!(s.decide(Lit::neg(v[0]))); // level 1: x0=False
    assert!(s.propagate().is_none());
    // x1=True, x2=True, both forced at level 1.
    assert_eq!(s.value(v[1]), LBool::True);
    assert_eq!(s.value(v[2]), LBool::True);
    // Lemma (¬x1 ∨ ¬x2): both literals currently False, both at level 1
    // (the max), so n_at_max == 2 → analyze + learn path.
    let trail_pre = s
        .add_theory_lemma_with_trail(vec![Lit::neg(v[1]), Lit::neg(v[2])])
        .expect("multi-max-level lemma resolves to a learnt asserting clause");
    assert!(!s.gave_up());
    // 1-UIP collapses to unit (x0): learn backtracks to root, so the
    // pre-learn trail length is 0, then x0 is enqueued True.
    assert_eq!(trail_pre, 0);
    assert_eq!(s.decision_level(), 0);
    assert_eq!(s.value(v[0]), LBool::True);
}

#[test]
fn trail_len_tracks_assignments() {
    let mut s = Solver::new();
    let v = vars(&mut s, 1);
    assert_eq!(s.trail_len(), 0);
    assert!(s.add_clause(vec![Lit::pos(v[0])]));
    // Unit clause enqueues + propagates one literal at root.
    assert_eq!(s.trail_len(), 1);
}

#[test]
fn analyze_backtrack_level_is_second_highest() {
    // Build a conflict whose learnt clause spans two decision levels so
    // bt_level is the second-highest (not the conflict level).
    //   x0 decided True at level 1; (¬x0 ∨ x1) forces x1=True (level 1).
    //   x2 decided True at level 2; (¬x2 ∨ x3) forces x3=True (level 2);
    //   the ternary (¬x1 ∨ ¬x2 ∨ ¬x3) is then all-false ⇒ conflict at
    //   level 2. (Ternary, not binary, so it is not unit at level 1 and
    //   does not pre-force x2/x3.)
    // 1-UIP is the level-2 decision x2; resolving x3 against its reason
    // leaves {¬x2, ¬x1}, so the learnt clause carries the level-1 literal
    // ¬x1 and bt_level = 1.
    let mut s = Solver::new();
    let v = vars(&mut s, 4);
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[1])]));
    assert!(s.add_clause(vec![Lit::neg(v[2]), Lit::pos(v[3])]));
    assert!(s.add_clause(vec![Lit::neg(v[1]), Lit::neg(v[2]), Lit::neg(v[3])]));
    assert!(s.decide(Lit::pos(v[0]))); // level 1
    assert!(s.propagate().is_none());
    assert_eq!(s.value(v[1]), LBool::True);
    assert!(s.decide(Lit::pos(v[2]))); // level 2
    let conflict = s.propagate().expect("conflict expected");
    let (learnt, bt) = s.analyze(conflict).expect("analyze produces a clause");
    assert!(learnt.len() >= 2, "learnt clause must span two levels");
    // 1-UIP asserting literal is at the conflict level (2).
    assert_eq!(s.level[learnt[0].var().index()], 2);
    // bt_level equals the max decision level over learnt[1..].
    let want_bt = learnt[1..]
        .iter()
        .map(|l| s.level[l.var().index()])
        .max()
        .unwrap();
    assert_eq!(bt, want_bt);
    assert_eq!(bt, 1, "second-highest level is 1, below conflict level 2");
}

#[test]
fn backtrack_to_at_or_above_current_level_is_noop() {
    let mut s = Solver::new();
    let v = vars(&mut s, 2);
    assert!(s.decide(Lit::pos(v[0]))); // level 1
    assert_eq!(s.decision_level(), 1);
    // Backtracking to the current level hits the early-return guard
    // (`level >= decision_level()`) and is a no-op.
    s.backtrack_to(1);
    assert_eq!(s.decision_level(), 1);
    assert_eq!(s.value(v[0]), LBool::True);
}

#[test]
fn solve_drains_pending_root_propagation_to_unsat() {
    // Set up clauses that only conflict once a manually-enqueued root
    // literal is propagated. solve() must drain that pending queue
    // before the CDCL loop and report Unsat.
    let mut s = Solver::new();
    let v = vars(&mut s, 2);
    // (¬x0 ∨ x1) (¬x0 ∨ ¬x1): binary clauses are not propagated by add.
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[1])]));
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::neg(v[1])]));
    // Enqueue x0=True at root WITHOUT propagating.
    assert!(s.enqueue(Lit::pos(v[0]), None));
    assert!(!s.is_unsat());
    // solve() drains the pending propagation: x0 forces x1 then ¬x1.
    assert_eq!(s.solve(), SolveResult::Unsat);
    assert!(s.is_unsat());
}

#[test]
fn enqueue_theory_rejects_reason_fact_not_true() {
    // A reason fact that is currently False (its negation True) makes the
    // justification clause malformed; enqueue_theory must bail.
    let mut s = Solver::new();
    let v = vars(&mut s, 2);
    // x0=False at level 1.
    assert!(s.decide(Lit::neg(v[0])));
    assert_eq!(s.value(v[0]), LBool::False);
    let before = s.n_clauses();
    // reason_facts = [x0] claims x0 True, but x0 is False ⇒ reject.
    assert!(!s.enqueue_theory(Lit::pos(v[1]), vec![Lit::pos(v[0])]));
    assert_eq!(s.value(v[1]), LBool::Undef);
    assert_eq!(s.n_clauses(), before, "no justification clause stored");
}

#[test]
fn decide_already_assigned_same_var_returns_consistency() {
    // `decide` on a variable that already has a value returns whether the
    // requested polarity agrees with the existing assignment, without
    // opening a new level.
    let mut s = Solver::new();
    let v = vars(&mut s, 1);
    // x0 = True at level 1.
    assert!(s.decide(Lit::pos(v[0])));
    assert_eq!(s.decision_level(), 1);
    // Re-deciding the same positive literal: assignment True, request
    // positive ⇒ consistent (true), no new level.
    assert!(s.decide(Lit::pos(v[0])));
    assert_eq!(s.decision_level(), 1);
    // Deciding the negative literal against a True assignment ⇒ false.
    assert!(!s.decide(Lit::neg(v[0])));
    assert_eq!(s.decision_level(), 1);
}

#[test]
fn decide_already_false_var_returns_consistency() {
    // The `LBool::False` arm of `decide`.
    let mut s = Solver::new();
    let v = vars(&mut s, 1);
    // x0 = False at level 1.
    assert!(s.decide(Lit::neg(v[0])));
    assert_eq!(s.value(v[0]), LBool::False);
    // Negative request against False ⇒ consistent.
    assert!(s.decide(Lit::neg(v[0])));
    // Positive request against False ⇒ inconsistent.
    assert!(!s.decide(Lit::pos(v[0])));
    assert_eq!(s.decision_level(), 1);
}

#[test]
fn enqueue_already_assigned_returns_consistency() {
    // `enqueue` on an already-assigned variable short-circuits to a
    // consistency check (the `LBool::True` / `LBool::False` match arms),
    // without pushing onto the trail.
    let mut s = Solver::new();
    let v = vars(&mut s, 1);
    // x0 = True at root.
    assert!(s.enqueue(Lit::pos(v[0]), None));
    let trail_before = s.trail_len();
    // True arm: positive request agrees, negative disagrees.
    assert!(s.enqueue(Lit::pos(v[0]), None));
    assert!(!s.enqueue(Lit::neg(v[0]), None));
    assert_eq!(s.trail_len(), trail_before, "no new trail entry");
}

#[test]
fn enqueue_already_false_returns_consistency() {
    // The `LBool::False` arm of `enqueue`.
    let mut s = Solver::new();
    let v = vars(&mut s, 1);
    // x0 = False at root.
    assert!(s.enqueue(Lit::neg(v[0]), None));
    let trail_before = s.trail_len();
    // False arm: negative request agrees, positive disagrees.
    assert!(s.enqueue(Lit::neg(v[0]), None));
    assert!(!s.enqueue(Lit::pos(v[0]), None));
    assert_eq!(s.trail_len(), trail_before, "no new trail entry");
}

#[test]
fn analyze_drops_root_level_literals_from_learnt() {
    // A clause literal sitting at decision level 0 (root fact) simplifies
    // away during 1-UIP analysis (the `lvl <= 0 { continue }` branch): it
    // must not appear in the learnt clause.
    //   Add the ternary (x0 ∨ ¬x1 ∨ ¬x2) while x2 is still Undef so the
    //   ¬x2 literal is retained in the stored clause; only then force
    //   x2=True at root via the unit (x2).
    //   Decide x0=False at level 1; (x0 ∨ x1) forces x1=True; the ternary
    //   is then all-false ⇒ conflict. ¬x2 is a root-level literal of the
    //   conflict clause and is dropped during 1-UIP, so the learnt clause
    //   collapses to the unit (x0).
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[1]), Lit::neg(v[2])]));
    assert!(s.add_clause(vec![Lit::pos(v[2])])); // root unit ⇒ x2=True at level 0
    assert_eq!(s.level[v[2].index()], 0);
    assert!(s.decide(Lit::neg(v[0]))); // level 1
    let conflict = s.propagate().expect("conflict expected");
    let (learnt, bt) = s.analyze(conflict).expect("analyze produces a clause");
    // Root-level ¬x2 dropped; 1-UIP is the decision x0 ⇒ unit (x0).
    assert_eq!(learnt.len(), 1, "root literal must be dropped from learnt");
    assert_eq!(learnt[0], Lit::pos(v[0]));
    assert_eq!(bt, 0);
    // The learnt clause carries no level-0 literal.
    assert!(learnt.iter().all(|l| s.level[l.var().index()] != 0));
}

#[test]
fn heap_percolate_down_selects_higher_right_child() {
    // `heap_percolate_down` picks the larger of the two children when the
    // right child has strictly higher activity than the left (the `best =
    // r` branch). Seed a 3-element heap whose root is the smallest and
    // whose right child outranks the left, then sift the root down.
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    // Heap layout indices: 0 = root, 1 = left child, 2 = right child.
    s.order_heap = vec![v[0], v[1], v[2]];
    s.heap_pos[v[0].index()] = 0;
    s.heap_pos[v[1].index()] = 1;
    s.heap_pos[v[2].index()] = 2;
    // Right child (v[2]) outranks the left (v[1]); root is the smallest.
    s.var_activity[v[0].index()] = 1.0;
    s.var_activity[v[1].index()] = 2.0;
    s.var_activity[v[2].index()] = 9.0;
    s.heap_percolate_down(0);
    // The highest-activity variable must bubble to the root.
    assert_eq!(s.order_heap[0], v[2]);
    assert_eq!(s.heap_pos[v[2].index()], 0);
    // And the heap_pos index of whatever now sits at slot 2 is consistent.
    assert_eq!(s.order_heap[s.heap_pos[v[0].index()]], v[0]);
}

#[test]
fn solve_restart_drain_detects_root_conflict_unsat() {
    // Drive solve() so the restart-drain path (the `propagate().is_some()
    // ⇒ Unsat` arm after `perform_restart`) actually fires. With an
    // every-conflict restart schedule:
    //   pick_decision first decides x0=True (level 1).
    //   (¬x0 ∨ x1) forces x1=True; (¬x0 ∨ ¬x1) then conflicts.
    //   1-UIP learns the root unit (¬x0); restart fires.
    //   Draining ¬x0 at root via (x0 ∨ x2)/(x0 ∨ ¬x2) re-conflicts ⇒ UNSAT
    //   detected inside the restart drain.
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[1])]));
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::neg(v[1])]));
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[2])]));
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[2])]));
    s.restart_base = 1;
    s.restart_step = 1; // restart fires after the first conflict
    assert_eq!(s.solve(), SolveResult::Unsat);
    assert!(s.is_unsat());
    assert!(!s.gave_up(), "verdict is a sound UNSAT, not a give-up");
}

#[test]
fn solve_restart_drain_clean_then_continues_to_sat() {
    // Companion to the UNSAT drain test: here the restart-drain is clean
    // (no root conflict), so solve() takes the `break` arm after
    // `perform_restart` and resumes deciding until SAT.
    //   x0=True decided; (¬x0 ∨ x1) forces x1; (¬x0 ∨ ¬x1) conflicts.
    //   Learn root unit (¬x0); restart fires; draining ¬x0 forces nothing
    //   further (the remaining clause (x2 ∨ x3) is unrelated), so the
    //   search continues and finds a model.
    let mut s = Solver::new();
    let v = vars(&mut s, 4);
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[1])]));
    assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::neg(v[1])]));
    assert!(s.add_clause(vec![Lit::pos(v[2]), Lit::pos(v[3])]));
    s.restart_base = 1;
    s.restart_step = 1;
    assert_eq!(s.solve(), SolveResult::Sat);
    // The learnt unit forced ¬x0; the clause (x2 ∨ x3) is satisfied.
    assert_eq!(s.value(v[0]), LBool::False);
    let sat = s.lit_value(Lit::pos(v[2])) == LBool::True
        || s.lit_value(Lit::pos(v[3])) == LBool::True;
    assert!(sat, "(x2 ∨ x3) must hold under the model");
}

#[test]
fn learn_clause_two_literals_watches_and_enqueues_asserting() {
    // After backjump, learn a 2-literal clause whose lits[0] is Undef
    // (asserting) and lits[1] is False: enqueue lits[0], watch both.
    let mut s = Solver::new();
    let v = vars(&mut s, 2);
    // Make x1 False at level 1 via a decision.
    assert!(s.decide(Lit::neg(v[1])));
    assert_eq!(s.value(v[1]), LBool::False);
    assert_eq!(s.value(v[0]), LBool::Undef);
    let before = s.n_clauses();
    // Learnt clause (x0 ∨ x1): x0 Undef (asserting), x1 currently False.
    let cref = s.learn_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]);
    // Clause stored and watched on both literals.
    assert_eq!(s.n_clauses(), before + 1);
    let lits = &s.arena().get(cref).lits;
    assert_eq!(lits.len(), 2);
    assert!(s.watches[lits[0].index()].contains(&cref));
    assert!(s.watches[lits[1].index()].contains(&cref));
    // Asserting literal enqueued True with this clause as its reason.
    assert_eq!(s.value(v[0]), LBool::True);
    assert_eq!(s.reason[v[0].index()], Some(cref));
}

// ─────────── SPEC-DRIVEN PROPERTY TESTS ───────────
//
// Expected values are derived from the SAT spec (MATH/RFC), NOT from
// reading the solver's control flow. A failing property test indicates
// a real bug in Solver::solve.
//
// Conventions:
//   - `eval_clause(s, c)` = "some literal in c evaluates to True under
//     the current model". This is the textbook clause-satisfaction
//     predicate.
//   - "model satisfies formula" = every clause in the formula evaluates
//     to True (Tarskian semantics).
//
// We treat tautological / duplicate-literal pre-processing as a
// LOGICAL equivalence (P ∧ (x ∨ ¬x) ≡ P), so add_clause's discarding of
// tautologies is sound and the model still satisfies the conceptual
// formula because (x ∨ ¬x) is True regardless of x.

/// Build a fresh solver, add `n_vars` propositional vars, then add all
/// `clauses`. Returns the solver and the var vector. None of the
/// clauses may trivially propagate to UNSAT — caller ensures that.
fn build_solver(n_vars: usize, clauses: &[Vec<Lit>]) -> Solver {
    let mut s = Solver::new();
    for _ in 0..n_vars {
        s.new_var();
    }
    for c in clauses {
        // add_clause may return false (root UNSAT) — that is a valid
        // formula state. The test using this helper should still check
        // verdict afterwards.
        let _ = s.add_clause(c.clone());
    }
    s
}

/// Vars-builder mirroring `vars` but parameterised so a caller can map
/// var index -> Var without a fresh solver.
fn make_var(i: usize) -> Var {
    Var(i as u32)
}

/// True iff `c` has at least one literal whose current value is True.
/// SPEC: a disjunctive clause is satisfied iff some literal is True.
fn clause_is_sat(s: &Solver, c: &[Lit]) -> bool {
    c.iter().any(|&l| s.lit_value(l) == LBool::True)
}

/// SPEC class 5: SAT model satisfies every clause. Property:
/// Solver::solve()==Sat ⇒ for every input clause c, some literal in c has
/// value True under the solver's final assignment. Derivation: definition
/// of "satisfying assignment" in propositional logic.
#[test]
fn property_sat_model_satisfies_every_clause_larger() {
    let v: Vec<Var> = (0..5).map(make_var).collect();
    // Satisfiable: x0=T, x1=F, x2=T, x3=F, x4=T works.
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1])],
        vec![Lit::pos(v[2]), Lit::neg(v[1])],
        vec![Lit::neg(v[3]), Lit::pos(v[4])],
        vec![Lit::pos(v[0]), Lit::neg(v[3])],
        vec![Lit::pos(v[2]), Lit::pos(v[4])],
        vec![Lit::neg(v[1]), Lit::pos(v[4])],
        vec![Lit::pos(v[0]), Lit::pos(v[2]), Lit::pos(v[4])],
        vec![Lit::neg(v[3]), Lit::neg(v[1]), Lit::pos(v[0])],
    ];
    let mut s = build_solver(5, &clauses);
    assert_eq!(s.solve(), SolveResult::Sat);
    for c in &clauses {
        assert!(
            clause_is_sat(&s, c),
            "SPEC violation: SAT model leaves clause {:?} unsatisfied",
            c
        );
    }
}

/// SPEC class 8: DETERMINISM. Two fresh Solvers with the same input
/// must produce the same verdict.
/// Derivation: Solver::solve is a pure function of its inputs (no
/// hidden global state, no PRNG sourced outside the input).
#[test]
fn property_determinism_same_clauses_same_verdict_unsat() {
    let v: Vec<Var> = (0..3).map(make_var).collect();
    // 3-var UNSAT: forces all 8 assignments out one by one.
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::pos(v[2])],
        vec![Lit::neg(v[0]), Lit::pos(v[1]), Lit::pos(v[2])],
        vec![Lit::pos(v[0]), Lit::neg(v[1]), Lit::pos(v[2])],
        vec![Lit::neg(v[0]), Lit::neg(v[1]), Lit::pos(v[2])],
        vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::neg(v[2])],
        vec![Lit::neg(v[0]), Lit::pos(v[1]), Lit::neg(v[2])],
        vec![Lit::pos(v[0]), Lit::neg(v[1]), Lit::neg(v[2])],
        vec![Lit::neg(v[0]), Lit::neg(v[1]), Lit::neg(v[2])],
    ];
    let mut s1 = build_solver(3, &clauses);
    let mut s2 = build_solver(3, &clauses);
    let r1 = s1.solve();
    let r2 = s2.solve();
    assert_eq!(r1, SolveResult::Unsat);
    assert_eq!(r1, r2, "SPEC violation: two fresh Solvers disagree on UNSAT");
}

/// SPEC class 5: Adding a TAUTOLOGY to a formula preserves the verdict.
/// Derivation: (x ∨ ¬x) ≡ True, so F ∧ (x ∨ ¬x) ≡ F.
#[test]
fn property_tautology_preserves_sat_verdict() {
    // Base SAT formula.
    let v: Vec<Var> = (0..3).map(make_var).collect();
    let base: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1])],
        vec![Lit::neg(v[1]), Lit::pos(v[2])],
    ];
    let mut s_base = build_solver(3, &base);
    let r_base = s_base.solve();
    assert_eq!(r_base, SolveResult::Sat);

    // Same formula plus a tautology on a different variable.
    let mut augmented: Vec<Vec<Lit>> = base.clone();
    augmented.push(vec![Lit::pos(v[0]), Lit::neg(v[0])]);
    let mut s_aug = build_solver(3, &augmented);
    let r_aug = s_aug.solve();
    assert_eq!(
        r_aug, r_base,
        "SPEC violation: adding a tautology changed the verdict"
    );
    // And the SAT model still satisfies the base clauses.
    for c in &base {
        assert!(clause_is_sat(&s_aug, c));
    }
}

/// SPEC class 5: Duplicating a clause preserves the verdict.
/// Derivation: C ∧ C ≡ C.
#[test]
fn property_clause_duplication_preserves_verdict_sat() {
    let v: Vec<Var> = (0..3).map(make_var).collect();
    let base: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1])],
        vec![Lit::neg(v[1]), Lit::pos(v[2])],
    ];
    let mut s_base = build_solver(3, &base);
    assert_eq!(s_base.solve(), SolveResult::Sat);

    // Duplicate every clause.
    let mut dup = base.clone();
    for c in &base {
        dup.push(c.clone());
    }
    let mut s_dup = build_solver(3, &dup);
    assert_eq!(
        s_dup.solve(),
        SolveResult::Sat,
        "SPEC violation: clause duplication changed verdict"
    );
}

/// SPEC class 5: Empty formula is SAT (vacuously).
/// Derivation: an empty conjunction is True.
#[test]
fn property_empty_formula_is_sat() {
    let mut s = Solver::new();
    // No vars, no clauses.
    assert_eq!(
        s.solve(),
        SolveResult::Sat,
        "SPEC violation: empty formula should be SAT (vacuous truth)"
    );
    // Even with vars but no clauses, every assignment is a model.
    let mut s2 = Solver::new();
    for _ in 0..5 {
        s2.new_var();
    }
    assert_eq!(
        s2.solve(),
        SolveResult::Sat,
        "SPEC violation: vars-only formula should be SAT"
    );
}

/// SPEC class 5: NEGATION SYMMETRY. Negate every literal in every
/// clause; the formula's (un)satisfiability is preserved.
/// Derivation: If model m satisfies F, then m' (flip every variable's
/// value) satisfies the negated formula F'. Bijection on models.
#[test]
fn property_global_negation_preserves_verdict_sat() {
    let v: Vec<Var> = (0..3).map(make_var).collect();
    let pos_form: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1])],
        vec![Lit::neg(v[1]), Lit::pos(v[2])],
    ];
    let neg_form: Vec<Vec<Lit>> = pos_form
        .iter()
        .map(|c| c.iter().map(|&l| -l).collect())
        .collect();
    let mut s_pos = build_solver(3, &pos_form);
    let mut s_neg = build_solver(3, &neg_form);
    assert_eq!(
        s_pos.solve(),
        s_neg.solve(),
        "SPEC violation: global negation flipped verdict"
    );
}

/// SPEC class 5: NEGATION SYMMETRY on the (x0∨x1)∧(¬x0∨¬x1) "XOR"
/// formula, which is SAT (one True, one False). Negating it yields
/// (¬x0∨¬x1)∧(x0∨x1), the same formula reordered ⇒ still SAT.
#[test]
fn property_xor_2var_is_sat_and_model_is_xor() {
    let v: Vec<Var> = (0..2).map(make_var).collect();
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1])], // at least one True
        vec![Lit::neg(v[0]), Lit::neg(v[1])], // not both True
    ];
    let mut s = build_solver(2, &clauses);
    assert_eq!(s.solve(), SolveResult::Sat);
    // SPEC: exactly one of x0, x1 must be True (XOR).
    let v0 = s.value(v[0]);
    let v1 = s.value(v[1]);
    assert!(v0.is_defined() && v1.is_defined());
    assert_ne!(
        v0, v1,
        "SPEC violation: XOR(x0,x1) model must have exactly one True"
    );
}

/// SPEC class 8 + 5: DETERMINISM combined with restart-schedule
/// independence. Same SAT input under three different restart_base
/// schedules must all return Sat AND produce satisfying models.
#[test]
fn property_sat_stable_across_restart_schedules_with_model_check() {
    let v: Vec<Var> = (0..5).map(make_var).collect();
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1])],
        vec![Lit::neg(v[1]), Lit::pos(v[2])],
        vec![Lit::neg(v[2]), Lit::pos(v[3])],
        vec![Lit::neg(v[3]), Lit::pos(v[4])],
        vec![Lit::pos(v[0]), Lit::pos(v[4])],
    ];
    for &rb in &[1u64, 7, 100] {
        let mut s = build_solver(5, &clauses);
        s.restart_base = rb;
        s.restart_step = rb;
        assert_eq!(
            s.solve(),
            SolveResult::Sat,
            "SPEC violation: SAT verdict flipped under restart_base={}",
            rb
        );
        for c in &clauses {
            assert!(
                clause_is_sat(&s, c),
                "SPEC violation: restart_base={} produced model that does not satisfy clause {:?}",
                rb,
                c
            );
        }
    }
}

/// SPEC class 5: SAT model is TOTAL — every variable has a defined value.
/// Derivation: Solver::solve returns Sat only when "every variable has a value"
/// (definition of "all_assigned"). This is the standard SAT spec.
#[test]
fn property_sat_model_is_total() {
    let v: Vec<Var> = (0..6).map(make_var).collect();
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::pos(v[2])],
        vec![Lit::neg(v[1]), Lit::pos(v[3])],
        vec![Lit::pos(v[4]), Lit::neg(v[5])],
    ];
    let mut s = build_solver(6, &clauses);
    assert_eq!(s.solve(), SolveResult::Sat);
    for var in &v {
        assert!(
            s.value(*var).is_defined(),
            "SPEC violation: SAT model leaves var {:?} undefined",
            var
        );
    }
}

/// SPEC of luby (Luby–Sinclair–Zuckerman): the sequence satisfies the
/// recursive identity
///   ∀ k ≥ 1: luby(2^k - 1) = 2^(k-1)
/// and for 2^(k-1) ≤ i < 2^k - 1: luby(i) = luby(i - 2^(k-1) + 1).
/// Derivation: original LSZ 1993 paper, Definition 2.
#[test]
fn property_luby_satisfies_recursive_spec() {
    // Check luby(2^k - 1) = 2^(k-1) for k = 1..=6.
    for k in 1u64..=6 {
        let i = (1u64 << k) - 1;
        let want = 1u64 << (k - 1);
        let got = luby(i);
        assert_eq!(got, want, "SPEC violation: luby(2^{}-1)={} expected {}", k, got, want);
    }
    // Check recursive identity on a range of i.
    // For each k such that 2^(k-1) ≤ i < 2^k - 1, luby(i) = luby(i - 2^(k-1) + 1).
    for i in 1u64..=63 {
        // Find unique k with 2^(k-1) ≤ i ≤ 2^k - 1.
        let mut k = 1u64;
        while (1u64 << k) - 1 < i {
            k += 1;
        }
        if (1u64 << k) - 1 == i {
            // Boundary case handled above.
            continue;
        }
        let shifted = i - (1u64 << (k - 1)) + 1;
        assert_eq!(
            luby(i),
            luby(shifted),
            "SPEC violation: luby({}) ≠ luby({})",
            i,
            shifted
        );
    }
}

/// SPEC class 5: A 3-SAT formula with ALL 2^n minterm clauses except
/// one is SAT, and the unique model is the complement of the missing
/// minterm. Derivation: every clause (l1∨l2∨l3) forbids the assignment
/// (¬l1,¬l2,¬l3); listing 7 of 8 minterm-forbidding clauses on 3
/// variables leaves exactly one allowed assignment.
#[test]
fn property_seven_of_eight_minterms_forces_unique_model() {
    let v: Vec<Var> = (0..3).map(make_var).collect();
    // The MISSING clause is (¬x0 ∨ ¬x1 ∨ ¬x2). Its absence allows the
    // assignment that falsifies it: x0=T, x1=T, x2=T.
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::pos(v[2])], // forbids 000
        vec![Lit::neg(v[0]), Lit::pos(v[1]), Lit::pos(v[2])], // forbids 100
        vec![Lit::pos(v[0]), Lit::neg(v[1]), Lit::pos(v[2])], // forbids 010
        vec![Lit::neg(v[0]), Lit::neg(v[1]), Lit::pos(v[2])], // forbids 110
        vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::neg(v[2])], // forbids 001
        vec![Lit::neg(v[0]), Lit::pos(v[1]), Lit::neg(v[2])], // forbids 101
        vec![Lit::pos(v[0]), Lit::neg(v[1]), Lit::neg(v[2])], // forbids 011
        // Missing: forbids 111 — so 111 is the unique satisfying model.
    ];
    let mut s = build_solver(3, &clauses);
    assert_eq!(s.solve(), SolveResult::Sat);
    // SPEC: unique model is x0=x1=x2=T.
    assert_eq!(s.value(v[0]), LBool::True);
    assert_eq!(s.value(v[1]), LBool::True);
    assert_eq!(s.value(v[2]), LBool::True);
}

// ─────────── HARD-PROBE: SAT restart × theory propagation ───────────
//
// These tests target the restart/theory-propagation interaction risk
// surface where the only real verdict-soundness bug was just found (the
// restart-drain regression at solve()'s restart point). Expected values
// derive ONLY from propositional-logic semantics — never from inspecting
// the solver's current control flow.

/// SPEC: PHP(3,2) is UNSAT regardless of restart cadence. Sweep
/// `restart_base` ∈ {1, 2, 3, 7, 11, 100} so the restart fires at
/// different depths into the conflict trace — verdict must be stable.
/// Hypothesis: restart at any cadence cannot turn UNSAT → Sat / Unknown.
#[test]
fn hardprobe_php_3_2_unsat_under_full_restart_sweep() {
    fn build() -> (Solver, Vec<Vec<Var>>) {
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
        (s, x)
    }
    for &rb in &[1u64, 2, 3, 7, 11, 100] {
        let (mut s, _x) = build();
        s.restart_base = rb;
        s.restart_step = rb;
        assert_eq!(
            s.solve(),
            SolveResult::Unsat,
            "SPEC: PHP(3,2) UNSAT must be invariant under restart_base={rb}"
        );
        assert!(!s.gave_up(), "verdict must be sound UNSAT (no give-up) for rb={rb}");
    }
}

/// SPEC: The XOR-conflict family
/// `(x0∨x1)(¬x0∨x1)(x0∨¬x1)(¬x0∨¬x1)` is UNSAT under any restart cadence.
/// Padded with extra free vars so the search tree is larger and restart
/// can fire at varying points; sweep restart_base across multiple Luby
/// positions so the restart fires at varying conflict-trace depths.
#[test]
fn hardprobe_xor_conflict_unsat_with_padding_full_sweep() {
    let build = |n_pad: usize| -> Solver {
        let mut s = Solver::new();
        let v: Vec<Var> = (0..2 + n_pad).map(|_| s.new_var()).collect();
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[1])]));
        assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[1])]));
        assert!(s.add_clause(vec![Lit::neg(v[0]), Lit::neg(v[1])]));
        s
    };
    for &rb in &[1u64, 2, 3, 7, 11, 100] {
        for &pad in &[0usize, 1, 3, 5] {
            let mut s = build(pad);
            s.restart_base = rb;
            s.restart_step = rb;
            assert_eq!(
                s.solve(),
                SolveResult::Unsat,
                "SPEC: XOR-conflict UNSAT must hold for restart_base={rb}, pad={pad}"
            );
        }
    }
}

/// SPEC: Transitive implication chain `(a) → (b) → ... → (k)` rooted at
/// a unit (a) forces every variable True. Restarting at any cadence
/// must preserve the root-level units (a, b, c, ... already at level 0)
/// and yield SAT with all-True model.
/// Hypothesis: a restart that drops a learnt root unit would flip the
/// verdict; sweep restart_base across the conflict count to expose it.
#[test]
fn hardprobe_implication_chain_sat_across_restart_sweep() {
    let build = |n: usize| -> (Solver, Vec<Var>) {
        let mut s = Solver::new();
        let v: Vec<Var> = (0..n).map(|_| s.new_var()).collect();
        // (v0) and (¬v_{i} ∨ v_{i+1}) for i = 0..n-1.
        assert!(s.add_clause(vec![Lit::pos(v[0])]));
        for i in 0..n - 1 {
            assert!(s.add_clause(vec![Lit::neg(v[i]), Lit::pos(v[i + 1])]));
        }
        (s, v)
    };
    for &rb in &[1u64, 2, 3, 7, 11, 100] {
        let (mut s, v) = build(8);
        s.restart_base = rb;
        s.restart_step = rb;
        assert_eq!(s.solve(), SolveResult::Sat, "rb={rb}: SAT expected");
        for var in &v {
            assert_eq!(
                s.value(*var),
                LBool::True,
                "rb={rb}: SPEC violation — implication chain forces v={:?} True",
                var
            );
        }
    }
}

/// SPEC: All-8-minterms over 3 vars is UNSAT. Sweep restart_base so the
/// restart fires at several distinct points in the conflict trace.
#[test]
fn hardprobe_all_minterms_unsat_across_restart_sweep() {
    let v: Vec<Var> = (0..3).map(make_var).collect();
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::pos(v[2])],
        vec![Lit::neg(v[0]), Lit::pos(v[1]), Lit::pos(v[2])],
        vec![Lit::pos(v[0]), Lit::neg(v[1]), Lit::pos(v[2])],
        vec![Lit::neg(v[0]), Lit::neg(v[1]), Lit::pos(v[2])],
        vec![Lit::pos(v[0]), Lit::pos(v[1]), Lit::neg(v[2])],
        vec![Lit::neg(v[0]), Lit::pos(v[1]), Lit::neg(v[2])],
        vec![Lit::pos(v[0]), Lit::neg(v[1]), Lit::neg(v[2])],
        vec![Lit::neg(v[0]), Lit::neg(v[1]), Lit::neg(v[2])],
    ];
    for &rb in &[1u64, 2, 3, 7, 11, 100] {
        let mut s = build_solver(3, &clauses);
        s.restart_base = rb;
        s.restart_step = rb;
        assert_eq!(s.solve(), SolveResult::Unsat, "rb={rb}: all-minterms must be UNSAT");
    }
}

/// SPEC: A theory-style enqueue at the root level (via `enqueue_theory`
/// with a root-level reason fact) installs a permanent root assignment.
/// A subsequent `perform_restart` MUST preserve that root assignment —
/// since restart only backtracks to level 0 and root literals stay at
/// level 0. Hypothesis: a malformed restart could drop a theory-derived
/// root assignment, flipping a later UNSAT to SAT.
#[test]
fn hardprobe_root_enqueue_theory_persists_across_perform_restart() {
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    // Make v[0] True at root via a unit clause; v[1] is then a theory-
    // derived consequence at root with reason [v[0]].
    assert!(s.add_clause(vec![Lit::pos(v[0])]));
    assert_eq!(s.value(v[0]), LBool::True);
    assert!(s.enqueue_theory(Lit::pos(v[1]), vec![Lit::pos(v[0])]));
    assert_eq!(s.value(v[1]), LBool::True);
    assert_eq!(s.level[v[1].index()], 0, "root reason ⇒ enqueue at level 0");
    // perform_restart only re-arms the Luby cadence; root facts stay.
    s.perform_restart();
    assert_eq!(s.value(v[0]), LBool::True, "SPEC: root unit must survive restart");
    assert_eq!(
        s.value(v[1]),
        LBool::True,
        "SPEC: root theory-propagation must survive restart"
    );
    assert_eq!(s.decision_level(), 0);
}

/// SPEC: After a theory lemma forces the asserting literal at level 0
/// (root unit learnt), an immediate restart must NOT lose that root
/// assignment. Reproduces the family of the bug just fixed: a learnt
/// root unit pre-restart still drives later propagation post-restart.
/// Hypothesis: dropping the learnt-unit's root assignment would let a
/// post-restart decision pick the opposite polarity and (after solve)
/// produce a wrong verdict on a downstream UNSAT formula.
#[test]
fn hardprobe_theory_lemma_root_unit_survives_restart_and_drives_unsat() {
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    // Force a 2-decision-level conflict so add_theory_lemma_with_trail
    // takes the assertable-by-backjump branch with assertion_level=0.
    // Decide v[0]=True at level 1, v[1]=True at level 2.
    assert!(s.decide(Lit::pos(v[0])));
    assert!(s.decide(Lit::pos(v[1])));
    // Lemma `(¬v[0])`: a single literal at level 1 is assertable by
    // backjumping to root ⇒ asserting unit v[0]=False at level 0.
    let trail_pre = s
        .add_theory_lemma_with_trail(vec![Lit::neg(v[0])])
        .expect("single-literal lemma is assertable");
    assert_eq!(trail_pre, 0, "backtrack to root before learning the unit");
    assert_eq!(s.value(v[0]), LBool::False, "root unit v[0]=False");
    assert_eq!(s.level[v[0].index()], 0);
    // Now restart and verify the root assignment persists.
    s.perform_restart();
    assert_eq!(s.value(v[0]), LBool::False, "SPEC: post-lemma root unit must survive restart");
    assert_eq!(s.decision_level(), 0);
    // Add a clause `(v[0] ∨ v[2])` whose first literal is False at root;
    // unit-propagating v[2]=True must still happen post-restart.
    assert!(s.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[2])]));
    assert_eq!(
        s.value(v[2]),
        LBool::True,
        "SPEC: post-restart root state must drive forward propagation"
    );
}

/// SPEC: A theory lemma that ends in root-UNSAT (`max_level <= 0`)
/// PERMANENTLY sets the solver's unsat flag. A subsequent `solve()` call
/// — regardless of restart cadence — must return Unsat, NOT Unknown.
/// Hypothesis: a faulty restart-aware reset could clear `unsat` on
/// rewind, letting a later solve call return a spurious Sat or Unknown.
#[test]
fn hardprobe_root_unsat_via_theory_lemma_persists_across_restart_sweep() {
    for &rb in &[1u64, 2, 3, 7, 11, 100] {
        let mut s = Solver::new();
        let v = vars(&mut s, 1);
        // Force v[0]=True at root.
        assert!(s.add_clause(vec![Lit::pos(v[0])]));
        // Theory lemma `(¬v[0])`: only literal is at level 0 ⇒ root UNSAT.
        assert_eq!(s.add_theory_lemma_with_trail(vec![Lit::neg(v[0])]), None);
        assert!(s.is_unsat(), "rb={rb}: theory lemma at root must set unsat");
        s.restart_base = rb;
        s.restart_step = rb;
        // Solve must return Unsat even with restart pressure.
        assert_eq!(
            s.solve(),
            SolveResult::Unsat,
            "rb={rb}: SPEC violation — root-unsat formula returned non-Unsat"
        );
    }
}

/// SPEC: A propagation chain spanning multiple decision levels, learnt
/// during search, must remain valid post-restart. Build a 4-var UNSAT
/// formula whose 1-UIP analysis has two plausible resolution orders
/// (depending on which variable hits the activity heap first). Sweep
/// restart cadence so 1-UIP fires at different positions.
#[test]
fn hardprobe_multi_uip_unsat_across_restart_sweep() {
    // 4-var UNSAT crafted so multiple variables are at the conflict
    // level when analyze() walks the trail. The trail-walk ordering
    // determines which UIP is selected; restart pressure varies the
    // ordering by clearing/reinserting activities.
    let v: Vec<Var> = (0..4).map(make_var).collect();
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit::pos(v[0]), Lit::pos(v[1])],
        vec![Lit::pos(v[0]), Lit::pos(v[2])],
        vec![Lit::pos(v[0]), Lit::pos(v[3])],
        vec![Lit::neg(v[1]), Lit::neg(v[2])],
        vec![Lit::neg(v[1]), Lit::neg(v[3])],
        vec![Lit::neg(v[2]), Lit::neg(v[3])],
        vec![Lit::neg(v[0])],
    ];
    // Decide ¬x0 first ⇒ x1, x2, x3 all True ⇒ binary clauses conflict
    // pairwise. The unit ¬x0 keeps a root-level conflict source alive.
    for &rb in &[1u64, 2, 3, 7, 11, 100] {
        let mut s = build_solver(4, &clauses);
        s.restart_base = rb;
        s.restart_step = rb;
        assert_eq!(
            s.solve(),
            SolveResult::Unsat,
            "rb={rb}: multi-UIP UNSAT must hold under any restart cadence"
        );
        assert!(s.is_unsat());
        assert!(!s.gave_up());
    }
}

/// SPEC: Calling `perform_restart` multiple times in a row at root level
/// is idempotent (every call is a no-op on the trail / value array).
/// Hypothesis: a misuse that bumped state on each restart could corrupt
/// the Luby index past safe bounds; we assert the trail state is stable
/// across N back-to-back restarts at root.
#[test]
fn hardprobe_repeated_root_restart_is_idempotent_on_trail_state() {
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    assert!(s.add_clause(vec![Lit::pos(v[0])]));
    assert!(s.add_clause(vec![Lit::neg(v[1])]));
    let trail_before: Vec<Lit> = s.trail().to_vec();
    let unsat_before = s.is_unsat();
    let dl_before = s.decision_level();
    for _ in 0..32 {
        s.perform_restart();
    }
    assert_eq!(s.decision_level(), dl_before, "SPEC: root restart preserves decision level");
    assert_eq!(s.is_unsat(), unsat_before, "SPEC: root restart preserves UNSAT flag");
    assert_eq!(s.trail(), trail_before.as_slice(), "SPEC: root restart preserves trail");
    // The root units must still be in effect.
    assert_eq!(s.value(v[0]), LBool::True);
    assert_eq!(s.value(v[1]), LBool::False);
    assert_eq!(s.value(v[2]), LBool::Undef);
}

/// SPEC: `should_restart()` returns false until `n_conflicts >=
/// restart_step`. Therefore at zero conflicts and any restart_base, no
/// restart is pending. Verify this invariant directly.
#[test]
fn hardprobe_should_restart_false_at_zero_conflicts() {
    for &rb in &[1u64, 2, 3, 7, 11, 100] {
        let mut s = Solver::new();
        s.restart_base = rb;
        s.restart_step = rb;
        assert_eq!(s.n_conflicts(), 0);
        assert!(
            !s.should_restart(),
            "SPEC: should_restart must be false at 0 conflicts (rb={rb}, restart_step={rb})"
        );
    }
}

/// SPEC: After a restart, the `restart_step` threshold must STRICTLY
/// INCREASE (the next restart must be later than the current
/// `n_conflicts`). Otherwise restart would re-fire immediately and the
/// solver could loop. Sweep rb so we hit several Luby positions.
#[test]
fn hardprobe_restart_step_advances_after_perform_restart() {
    for &rb in &[1u64, 2, 7, 11, 100] {
        let mut s = Solver::new();
        let _v = vars(&mut s, 2);
        s.restart_base = rb;
        s.restart_step = rb;
        // Simulate having reached the restart threshold.
        s.n_conflicts = rb;
        let step_before = s.restart_step;
        let n_before = s.n_conflicts();
        s.perform_restart();
        let step_after = s.restart_step;
        assert!(
            step_after > n_before,
            "SPEC: restart_step must advance strictly past current n_conflicts (rb={rb}: before={step_before}, after={step_after}, n_conflicts={n_before})"
        );
    }
}

/// SPEC: `enqueue_theory` followed by a restart, then a SAT-level
/// propagation that would conflict with the theory-derived root literal,
/// must surface UNSAT — not Unknown or Sat. The theory-justification
/// clause and the root literal must both survive the restart.
#[test]
fn hardprobe_enqueue_theory_root_then_restart_then_conflict_is_unsat() {
    let mut s = Solver::new();
    let v = vars(&mut s, 3);
    // v[0] True at root via unit clause; v[1] enqueued by theory at root
    // with reason [v[0]].
    assert!(s.add_clause(vec![Lit::pos(v[0])]));
    assert!(s.enqueue_theory(Lit::pos(v[1]), vec![Lit::pos(v[0])]));
    assert_eq!(s.value(v[1]), LBool::True);
    // Restart.
    s.perform_restart();
    assert_eq!(s.value(v[1]), LBool::True, "SPEC: root theory-derived literal must survive restart");
    // Add a clause `(¬v[1])` — it conflicts with the root assignment
    // ⇒ UNSAT.
    assert!(!s.add_clause(vec![Lit::neg(v[1])]));
    assert!(s.is_unsat(), "SPEC: post-restart contradiction with theory-derived root literal must be UNSAT");
    // solve() must report Unsat.
    assert_eq!(s.solve(), SolveResult::Unsat);
}

