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
    let (learnt, bt) = s.analyze(conflict).expect("analyze produces a clause");
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
