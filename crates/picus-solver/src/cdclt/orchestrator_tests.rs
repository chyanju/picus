use super::*;
use crate::boolean::{Formula, Literal};
use crate::frontend::encoder::PolyTerm;
use num_bigint::BigUint;

/// `coeff * <var idx> = rhs_const`.
fn eq(coeff_lhs: u64, var_idx: u32, rhs_const: u64) -> Formula {
    Formula::Lit(Literal::Eq(
        vec![PolyTerm {
            coeff: BigUint::from(coeff_lhs),
            vars: vec![(var_idx, 1)],
        }],
        vec![PolyTerm {
            coeff: BigUint::from(rhs_const),
            vars: vec![],
        }],
    ))
}

fn names(ns: &[&str]) -> Vec<String> {
    ns.iter().map(|s| s.to_string()).collect()
}

#[test]
fn solve_trivial_eq() {
    let vn = names(&["x"]);
    let f = eq(1, 0, 5);
    let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("x"), Some(&BigUint::from(5u32)));
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

#[test]
fn solve_contradictory_eqs() {
    let vn = names(&["x"]);
    let f = Formula::And(vec![eq(1, 0, 5), eq(1, 0, 6)]);
    let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)));
}

#[test]
fn solve_or_picks_satisfiable_branch() {
    let vn = names(&["x"]);
    let f = Formula::Or(vec![eq(1, 0, 5), eq(1, 0, 6)]);
    let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            let v = m.get("x").expect("x assigned").clone();
            assert!(v == BigUint::from(5u32) || v == BigUint::from(6u32));
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

#[test]
fn solve_disjunctive_bit_via_cdclt() {
    let vn = names(&["x"]);
    let f = Formula::And(vec![
        Formula::Or(vec![eq(1, 0, 0), eq(1, 0, 1)]),
        eq(1, 0, 7),
    ]);
    let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)));
}

#[test]
fn solve_eq_and_neq() {
    let vn = names(&["x"]);
    let f = Formula::And(vec![eq(1, 0, 5), Formula::Not(Box::new(eq(1, 0, 5)))]);
    let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)));
}

#[test]
fn solve_implies_chain() {
    let vn = names(&["x", "y"]);
    let f = Formula::And(vec![
        eq(1, 0, 0),
        Formula::Or(vec![Formula::Not(Box::new(eq(1, 0, 0))), eq(1, 1, 0)]),
        Formula::Not(Box::new(eq(1, 1, 0))),
    ]);
    let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)));
}

#[test]
fn iter_cap_returns_unknown_on_pathological_input() {
    let _g = crate::config::ConfigGuard::with_override(|c| c.cdclt_iter_cap = 0);
    let vn = names(&["x"]);
    let f = Formula::Or(vec![eq(1, 0, 5), eq(1, 0, 6)]);
    let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unknown));
}

#[test]
fn solve_true_formula_is_sat_with_empty_model() {
    // `Formula::True` constant-folds in Tseitin to Constant(true);
    // `solve_formula` returns Sat with no variable assignments.
    let vn: Vec<String> = vec![];
    let r = solve_formula(
        BigUint::from(101u32),
        &vn,
        &Formula::True,
        &CancelToken::none(),
    );
    match r {
        SolveOutcome::Sat(m) => assert!(m.is_empty()),
        other => panic!("expected Sat(empty), got {:?}", other),
    }
}

#[test]
fn solve_false_formula_is_unsat() {
    // `Formula::False` constant-folds to Constant(false) → Unsat.
    let vn: Vec<String> = vec![];
    let r = solve_formula(
        BigUint::from(101u32),
        &vn,
        &Formula::False,
        &CancelToken::none(),
    );
    assert!(matches!(r, SolveOutcome::Unsat(_)));
}

#[test]
fn solve_returns_unknown_when_token_already_cancelled() {
    // A non-trivial formula reaches the main loop, whose first action
    // is the cancellation check; a pre-cancelled token short-circuits
    // to Unknown before any SAT/theory work.
    let vn = names(&["x"]);
    let f = eq(1, 0, 5);
    let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::cancelled());
    assert!(matches!(r, SolveOutcome::Unknown));
}

#[test]
fn apply_theory_conflict_with_assigned_core_learns_lemma() {
    // Two core vars assigned True at distinct decision levels yield a
    // learnable lemma `(¬a ∨ ¬b)`; `apply_theory_conflict` returns
    // Some(trail_pre) (not give-up, not root-UNSAT) since the lemma is
    // assertable by backjumping.
    let mut sat = Solver::new();
    let a = sat.new_var();
    let b = sat.new_var();
    assert!(sat.decide(Lit::pos(a)));
    assert!(sat.decide(Lit::pos(b)));
    assert!(matches!(sat.value(a), LBool::True));
    assert!(matches!(sat.value(b), LBool::True));
    let result = apply_theory_conflict(&mut sat, &[a, b]);
    assert!(result.is_some(), "an assigned core must produce a lemma");
    assert!(!sat.gave_up());
}

// `coeff * <var idx> != rhs_const` (disequality literal).
fn neq(coeff_lhs: u64, var_idx: u32, rhs_const: u64) -> Formula {
    Formula::Lit(crate::boolean::Literal::Neq(
        vec![PolyTerm {
            coeff: BigUint::from(coeff_lhs),
            vars: vec![(var_idx, 1)],
        }],
        vec![PolyTerm {
            coeff: BigUint::from(rhs_const),
            vars: vec![],
        }],
    ))
}

#[test]
fn theory_propagation_progresses_then_post_check_sat() {
    // GF(7) (small prime → field polys engage so the theory reasons over
    // GF(p)). Unit `x = 3` pins x; the OR clause `(x = 5) ∨ (y = 2)` is not
    // yet satisfied. After x is pinned, FF-theory tier-1 propagation
    // evaluates the off-trail atom `x = 5` to False (3 ≠ 5), enqueueing a
    // theory literal (the `run_theory_propagation` Progressed path). SAT
    // then unit-propagates `y = 2`, and post_check confirms SAT.
    let vn = names(&["x", "y"]);
    let f = Formula::And(vec![
        eq(1, 0, 3),
        Formula::Or(vec![eq(1, 0, 5), eq(1, 1, 2)]),
    ]);
    let r = solve_formula(BigUint::from(7u32), &vn, &f, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("x"), Some(&BigUint::from(3u32)));
            assert_eq!(m.get("y"), Some(&BigUint::from(2u32)));
        }
        other => panic!("expected Sat(x=3,y=2), got {:?}", other),
    }
}

#[test]
fn theory_conflict_drives_post_check_unsat_resync() {
    // GF(7) implication chain that is theory-UNSAT: x = 0, (x = 0 → y = 0),
    // and y ≠ 0. The CDCL(T) loop drives propagation, a SAT-level conflict
    // and learnt clause, and/or a post_check UNSAT with conflict resync —
    // every path lands on UNSAT.
    let vn = names(&["x", "y"]);
    let f = Formula::And(vec![
        eq(1, 0, 0),
        Formula::Or(vec![Formula::Not(Box::new(eq(1, 0, 0))), eq(1, 1, 0)]),
        neq(1, 1, 0),
    ]);
    let r = solve_formula(BigUint::from(7u32), &vn, &f, &CancelToken::none());
    assert!(
        matches!(r, SolveOutcome::Unsat(_)),
        "theory chain must be UNSAT, got {:?}",
        r
    );
}

#[test]
fn disjunction_of_three_with_pin_is_unsat_over_small_prime() {
    // GF(7): `(x=0 ∨ x=1 ∨ x=2)` together with `x=4`. Each disjunct
    // conflicts with the pin under the theory, exercising repeated
    // theory-conflict lemma learning until root-level UNSAT.
    let vn = names(&["x"]);
    let f = Formula::And(vec![
        Formula::Or(vec![eq(1, 0, 0), eq(1, 0, 1), eq(1, 0, 2)]),
        eq(1, 0, 4),
    ]);
    let r = solve_formula(BigUint::from(7u32), &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)), "got {:?}", r);
}

#[test]
fn disjunctive_branch_is_sat_over_small_prime() {
    // GF(7): `(x=5 ∨ x=6)` is SAT; one branch survives the theory check,
    // driving the post_check Sat / collect_model path with a real model.
    let vn = names(&["x"]);
    let f = Formula::Or(vec![eq(1, 0, 5), eq(1, 0, 6)]);
    let r = solve_formula(BigUint::from(7u32), &vn, &f, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            let v = m.get("x").expect("x assigned").clone();
            assert!(v == BigUint::from(5u32) || v == BigUint::from(6u32));
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

#[test]
fn theory_core_undef_var_gives_up_not_panic() {
    // A theory UNSAT core that names a SAT-unassigned variable signals
    // theory/SAT trail divergence. `apply_theory_conflict` must flag
    // give-up (so the loop returns Unknown), never panic or fabricate a
    // verdict from a partial core.
    let mut sat = Solver::new();
    let v = sat.new_var(); // freshly created ⇒ unassigned (Undef)
    assert!(matches!(sat.value(v), LBool::Undef));
    let result = apply_theory_conflict(&mut sat, &[v]);
    assert!(result.is_none(), "a diverged core must not produce a lemma");
    assert!(
        sat.gave_up(),
        "must flag give-up so the caller returns Unknown"
    );
}

#[test]
fn apply_theory_conflict_false_core_var_takes_positive_literal() {
    // A core var asserted False contributes its *positive* literal to
    // the learnt clause (the `LBool::False => Lit::pos(v)` arm). A
    // single-var lemma `(x)` is assertable by backjumping to root, so
    // the call returns Some, not give-up.
    let mut sat = Solver::new();
    let v = sat.new_var();
    assert!(sat.decide(Lit::neg(v))); // level 1: v = False
    assert!(matches!(sat.value(v), LBool::False));
    let result = apply_theory_conflict(&mut sat, &[v]);
    assert!(result.is_some(), "an assigned core must produce a lemma");
    assert!(!sat.gave_up());
    // The asserting unit `(v)` flips v to True after the backjump.
    assert!(matches!(sat.value(v), LBool::True));
}

/// Scriptable [`Theory`] for driving `cdclt_loop` / `run_theory_propagation`
/// branches deterministically. `propagate` and `post_check` replay a queued
/// script; `explain` reasons come from `reasons`. Push/pop are counted so
/// the theory-level resync paths can be asserted.
struct ScriptedTheory {
    props: std::collections::VecDeque<Vec<(Var, bool)>>,
    reasons: HashMap<Var, Vec<(Var, bool)>>,
    checks: std::collections::VecDeque<CheckOutcome>,
    pushes: usize,
    pops: usize,
    notified: Vec<(Var, bool)>,
}

impl ScriptedTheory {
    fn new() -> Self {
        ScriptedTheory {
            props: std::collections::VecDeque::new(),
            reasons: HashMap::new(),
            checks: std::collections::VecDeque::new(),
            pushes: 0,
            pops: 0,
            notified: Vec::new(),
        }
    }
}

impl Theory for ScriptedTheory {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        self.notified.push((atom, polarity));
    }
    fn post_check(&mut self) -> CheckOutcome {
        self.checks.pop_front().unwrap_or(CheckOutcome::Sat)
    }
    fn propagate(&mut self) -> Vec<(Var, bool)> {
        self.props.pop_front().unwrap_or_default()
    }
    fn explain(&self, atom: Var, _polarity: bool) -> Vec<(Var, bool)> {
        self.reasons.get(&atom).cloned().unwrap_or_default()
    }
    fn push(&mut self) {
        self.pushes += 1;
    }
    fn pop(&mut self) {
        self.pops += 1;
    }
    fn collect_model(&self) -> Option<HashMap<String, BigUint>> {
        Some(HashMap::new())
    }
}

#[test]
fn run_theory_propagation_idle_on_empty() {
    // `propagate` returning no facts ⇒ TheoryStep::Idle (early-out).
    let mut sat = Solver::new();
    let mut th = ScriptedTheory::new();
    assert!(matches!(
        run_theory_propagation(&mut sat, &mut th),
        TheoryStep::Idle
    ));
}

#[test]
fn run_theory_propagation_progressed_enqueues_undef_atom() {
    // Reason fact `a` is True; propagated atom `b` is Undef ⇒ the Undef
    // arm enqueues `b` via `enqueue_theory` and reports Progressed.
    let mut sat = Solver::new();
    let a = sat.new_var();
    let b = sat.new_var();
    assert!(sat.decide(Lit::pos(a))); // level 1: a = True
    assert!(sat.propagate().is_none());
    let mut th = ScriptedTheory::new();
    th.props.push_back(vec![(b, true)]);
    th.reasons.insert(b, vec![(a, true)]);
    assert!(matches!(
        run_theory_propagation(&mut sat, &mut th),
        TheoryStep::Progressed
    ));
    assert!(matches!(sat.value(b), LBool::True), "b was enqueued True");
}

#[test]
fn run_theory_propagation_idle_when_sat_already_agrees() {
    // Propagating `(a,true)` while SAT already has `a = True` hits the
    // `LBool::True if polarity` no-op arm; with no other progress the
    // round is Idle. Negative-polarity agreement (`LBool::False if
    // !polarity`) on `c = False` is also a no-op.
    let mut sat = Solver::new();
    let a = sat.new_var();
    let c = sat.new_var();
    assert!(sat.decide(Lit::pos(a))); // a = True
    assert!(sat.decide(Lit::neg(c))); // c = False
    let mut th = ScriptedTheory::new();
    th.props.push_back(vec![(a, true), (c, false)]);
    assert!(matches!(
        run_theory_propagation(&mut sat, &mut th),
        TheoryStep::Idle
    ));
}

#[test]
fn run_theory_propagation_conflict_when_sat_disagrees() {
    // SAT has `c = True` at a higher level than reason `a = True`;
    // propagating `(c,false)` disagrees, building the lemma `(¬c ∨ ¬a)`.
    // Both lits are False but only `c` is at the top level, so the lemma
    // is assertable ⇒ TheoryStep::Conflict(trail_pre).
    let mut sat = Solver::new();
    let a = sat.new_var();
    let c = sat.new_var();
    assert!(sat.decide(Lit::pos(a))); // level 1
    assert!(sat.propagate().is_none());
    assert!(sat.decide(Lit::pos(c))); // level 2
    assert!(sat.propagate().is_none());
    let mut th = ScriptedTheory::new();
    th.props.push_back(vec![(c, false)]);
    th.reasons.insert(c, vec![(a, true)]);
    match run_theory_propagation(&mut sat, &mut th) {
        TheoryStep::Conflict(_) => {}
        other => panic!("expected Conflict, got {:?}", debug_step(&other)),
    }
    assert!(!sat.gave_up());
}

#[test]
fn run_theory_propagation_root_unsat_when_disagreement_at_root() {
    // Reason `a` and conflicting atom `c` both True at root level 0. The
    // disagreement lemma `(¬c ∨ ¬a)` is all-root ⇒ unconditional root
    // UNSAT, no give-up ⇒ TheoryStep::RootUnsat.
    let mut sat = Solver::new();
    let a = sat.new_var();
    let c = sat.new_var();
    assert!(sat.add_clause(vec![Lit::pos(a)])); // a True @0
    assert!(sat.add_clause(vec![Lit::pos(c)])); // c True @0
    let mut th = ScriptedTheory::new();
    th.props.push_back(vec![(c, false)]);
    th.reasons.insert(c, vec![(a, true)]);
    assert!(matches!(
        run_theory_propagation(&mut sat, &mut th),
        TheoryStep::RootUnsat
    ));
    assert!(sat.is_unsat());
    assert!(!sat.gave_up());
}

/// Render a `TheoryStep` for panic messages (it has no `Debug`).
fn debug_step(s: &TheoryStep) -> &'static str {
    match s {
        TheoryStep::Idle => "Idle",
        TheoryStep::Progressed => "Progressed",
        TheoryStep::Conflict(_) => "Conflict",
        TheoryStep::RootUnsat => "RootUnsat",
        TheoryStep::GiveUp => "GiveUp",
    }
}

#[test]
fn sync_theory_after_backtrack_pops_down_to_decision_level() {
    // After SAT drops from level 2 to level 0, the theory must pop both
    // levels (the `while *theory_levels > dl` loop body).
    let mut sat = Solver::new();
    let a = sat.new_var();
    let b = sat.new_var();
    assert!(sat.decide(Lit::pos(a))); // level 1
    assert!(sat.decide(Lit::pos(b))); // level 2
    let mut th = ScriptedTheory::new();
    let mut levels: usize = 2;
    sat.backtrack_to(0);
    sync_theory_after_backtrack(&sat, &mut th, &mut levels);
    assert_eq!(levels, 0);
    assert_eq!(th.pops, 2, "two levels rolled back ⇒ two pops");
}

#[test]
fn sync_theory_after_backtrack_noop_when_levels_match() {
    // theory_levels already at the SAT decision level ⇒ loop body never
    // runs, no pops.
    let sat = Solver::new();
    let mut th = ScriptedTheory::new();
    let mut levels: usize = 0;
    sync_theory_after_backtrack(&sat, &mut th, &mut levels);
    assert_eq!(levels, 0);
    assert_eq!(th.pops, 0);
}

#[test]
fn resync_after_lemma_rewinds_levels_and_notified() {
    // resync_after_lemma pops theory levels to the SAT level and clamps
    // `notified` to min(prior, trail_pre, trail_len). Here trail_pre is
    // larger than trail_len, so trail_len wins.
    let mut sat = Solver::new();
    let a = sat.new_var();
    let b = sat.new_var();
    assert!(sat.decide(Lit::pos(a)));
    assert!(sat.decide(Lit::pos(b)));
    sat.backtrack_to(0); // trail now empty
    let mut th = ScriptedTheory::new();
    let mut levels: usize = 2;
    let mut notified: usize = 5;
    resync_after_lemma(&sat, &mut th, &mut levels, &mut notified, 99);
    assert_eq!(levels, 0);
    assert_eq!(th.pops, 2);
    assert_eq!(notified, sat.trail_len(), "clamped to trail_len (=0)");
}

/// Drive `cdclt_loop` over a hand-built SAT instance with `th`. Mirrors
/// `solve_formula`'s loop call so the loop's own branches are exercised
/// without routing through Tseitin/the FF theory.
fn drive_loop(sat: &mut Solver, th: &mut ScriptedTheory, cancel: &CancelToken) -> SolveOutcome {
    cdclt_loop(sat, th, cancel)
}

#[test]
fn loop_sat_requires_backtracking() {
    // `(x0 ∨ x1) ∧ (x0 ∨ ¬x1)`: deciding x0=False forces x1 both ways →
    // conflict, analyze, backjump, learn unit (x0), re-propagate to SAT.
    // Exercises the propagate-conflict / analyze / backtrack / learn /
    // resync path with an inert theory.
    let mut sat = Solver::new();
    let v: Vec<Var> = (0..2).map(|_| sat.new_var()).collect();
    assert!(sat.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
    assert!(sat.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[1])]));
    let mut th = ScriptedTheory::new();
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "got {:?}", r);
}

#[test]
fn loop_root_unsat_via_sat_conflicts() {
    // Fully UNSAT 2-var instance `(x0∨x1)(x0∨¬x1)(¬x0∨x1)(¬x0∨¬x1)`.
    // The loop drives decisions/conflicts until a conflict lands at
    // decision level 0 ⇒ the `decision_level() == 0` UNSAT return.
    let mut sat = Solver::new();
    let v: Vec<Var> = (0..2).map(|_| sat.new_var()).collect();
    assert!(sat.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
    assert!(sat.add_clause(vec![Lit::pos(v[0]), Lit::neg(v[1])]));
    assert!(sat.add_clause(vec![Lit::neg(v[0]), Lit::pos(v[1])]));
    assert!(sat.add_clause(vec![Lit::neg(v[0]), Lit::neg(v[1])]));
    let mut th = ScriptedTheory::new();
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)), "got {:?}", r);
}

#[test]
fn loop_post_check_sat_collects_model() {
    // One free var; SAT reaches a full assignment, theory post_check
    // returns Sat ⇒ the loop returns Sat(collect_model()). The single
    // decision drives exactly one theory `push` and one `notify_fact`.
    let mut sat = Solver::new();
    let v0 = sat.new_var();
    let mut th = ScriptedTheory::new();
    th.checks.push_back(CheckOutcome::Sat);
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "got {:?}", r);
    assert_eq!(th.pushes, 1, "one decision ⇒ one theory push");
    assert_eq!(th.notified, vec![(v0, true)], "the decided fact is notified");
}

#[test]
fn loop_post_check_unknown_returns_unknown() {
    // Theory post_check at the full assignment returns Unknown ⇒ loop
    // returns Unknown (theory incompleteness branch).
    let mut sat = Solver::new();
    let _v = sat.new_var();
    let mut th = ScriptedTheory::new();
    th.checks.push_back(CheckOutcome::Unknown);
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unknown), "got {:?}", r);
}

#[test]
fn loop_post_check_unsat_core_learns_then_resolves() {
    // Two free vars; at the first full assignment post_check returns an
    // UNSAT core `[v0, v1]` (both True). `apply_theory_conflict` learns
    // `(¬v0 ∨ ¬v1)`, the loop resyncs and continues; the next full
    // assignment is accepted as Sat. Exercises the post_check-Unsat →
    // apply_theory_conflict → resync_after_lemma path.
    let mut sat = Solver::new();
    let v: Vec<Var> = (0..2).map(|_| sat.new_var()).collect();
    let mut th = ScriptedTheory::new();
    th.checks.push_back(CheckOutcome::Unsat {
        core: vec![v[0], v[1]],
    });
    th.checks.push_back(CheckOutcome::Sat);
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "got {:?}", r);
    // The learnt clause `(¬v0 ∨ ¬v1)` must hold in the final model.
    assert!(
        !(matches!(sat.value(v[0]), LBool::True) && matches!(sat.value(v[1]), LBool::True)),
        "learnt clause forbids both True"
    );
}

#[test]
fn loop_post_check_unsat_root_core_is_unsat() {
    // A single free var; post_check returns the unit core `[v0]`. The
    // learnt unit `(¬v0)` flips v0, the next assignment is full and the
    // (replayed) Sat check would accept — so to force the root-UNSAT
    // post-check arm we return Unsat at *every* full assignment: after
    // the unit `(¬v0)` is learnt and re-asserted at root, the next core
    // `[v0]` builds an all-root lemma ⇒ root UNSAT.
    let mut sat = Solver::new();
    let v0 = sat.new_var();
    let mut th = ScriptedTheory::new();
    th.checks.push_back(CheckOutcome::Unsat { core: vec![v0] });
    th.checks.push_back(CheckOutcome::Unsat { core: vec![v0] });
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)), "got {:?}", r);
}

#[test]
fn loop_theory_propagation_progressed_then_sat() {
    // Theory propagates `b=True` (Undef, reason a=True) before the full
    // assignment ⇒ TheoryStep::Progressed `continue`s the loop. The next
    // round reaches a full assignment ⇒ Sat. Covers the loop's
    // `TheoryStep::Progressed => continue` arm.
    let mut sat = Solver::new();
    let a = sat.new_var();
    let b = sat.new_var();
    // Unit `(a)` so a is True at root; b stays free for the theory to fix.
    assert!(sat.add_clause(vec![Lit::pos(a)]));
    let mut th = ScriptedTheory::new();
    th.props.push_back(vec![(b, true)]);
    th.reasons.insert(b, vec![(a, true)]);
    th.checks.push_back(CheckOutcome::Sat);
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "got {:?}", r);
    assert!(matches!(sat.value(b), LBool::True));
}

#[test]
fn loop_theory_propagation_conflict_then_resolves() {
    // The theory propagates a literal that disagrees with SAT, forcing a
    // lemma + backjump (TheoryStep::Conflict → resync → continue), after
    // which the search completes Sat. `a` is decided True at level 1; the
    // theory insists `a=False` with reason `b=True` (b True at root). The
    // resulting lemma `(¬a ∨ ¬b)` is assertable (only `a` at the top
    // level) and forces `a` False, after which the loop reaches Sat.
    let mut sat = Solver::new();
    let a = sat.new_var();
    let b = sat.new_var();
    assert!(sat.add_clause(vec![Lit::pos(b)])); // b True @0
    assert!(sat.propagate().is_none());
    // Decide `a = True` at level 1 before the loop so the theory's
    // first propagation round (`(a,false)`) disagrees immediately.
    assert!(sat.decide(Lit::pos(a)));
    let mut th = ScriptedTheory::new();
    th.props.push_back(vec![(a, false)]);
    th.reasons.insert(a, vec![(b, true)]);
    th.checks.push_back(CheckOutcome::Sat);
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "got {:?}", r);
    // The lemma flips `a` to False.
    assert!(matches!(sat.value(a), LBool::False));
}

#[test]
fn loop_theory_propagation_root_unsat_returns_unsat() {
    // Drive `cdclt_loop` to the `TheoryStep::RootUnsat => SolveOutcome::Unsat`
    // arm. `a` and `c` are both True at root level 0 (unit clauses). On the
    // first loop iteration the SAT propagation finds no conflict, the trail
    // (a, c) is notified, and the scripted theory propagates `(c, false)` with
    // reason `[(a, true)]`. SAT already has `c = True`, so the disagreement
    // builds the all-root lemma `(¬c ∨ ¬a)`; `add_theory_lemma_with_trail`
    // sees `max_level == 0`, flags root UNSAT (not give-up), and the loop
    // returns Unsat.
    let mut sat = Solver::new();
    let a = sat.new_var();
    let c = sat.new_var();
    assert!(sat.add_clause(vec![Lit::pos(a)])); // a True @0
    assert!(sat.add_clause(vec![Lit::pos(c)])); // c True @0
    let mut th = ScriptedTheory::new();
    th.props.push_back(vec![(c, false)]);
    th.reasons.insert(c, vec![(a, true)]);
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)), "got {:?}", r);
    assert!(sat.is_unsat());
    assert!(!sat.gave_up(), "a root disagreement is sound UNSAT, not give-up");
}

#[test]
fn loop_returns_unknown_when_cancelled_before_iteration() {
    // A pre-cancelled token short-circuits the loop's first action.
    let mut sat = Solver::new();
    let _v = sat.new_var();
    let mut th = ScriptedTheory::new();
    let r = drive_loop(&mut sat, &mut th, &CancelToken::cancelled());
    assert!(matches!(r, SolveOutcome::Unknown));
}

#[test]
fn loop_returns_unknown_at_iter_cap() {
    // cap = 0 ⇒ the first `iters > cap` check trips ⇒ Unknown, even with
    // pending work. Drives the iteration-cap branch through `cdclt_loop`.
    let _g = crate::config::ConfigGuard::with_override(|c| c.cdclt_iter_cap = 0);
    let mut sat = Solver::new();
    let _v = sat.new_var();
    let mut th = ScriptedTheory::new();
    let r = drive_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unknown));
}

// =============================================================================
// SPEC-DRIVEN property tests — expected values are derived from math / first
// principles (the SMT semantics of the literal forms `c·x = k` and `c·x ≠ k`
// over GF(p)), NOT from inspecting `solve_formula`'s implementation.
// =============================================================================

/// Evaluate `coeff_lhs · m[var_name] mod prime` and compare to `rhs_const mod prime`.
/// The Eq/Neq literals in this file all have shape `(coeff · x_idx) ?= rhs`.
fn lit_eq_holds_in_model(
    coeff_lhs: u64,
    var_name: &str,
    rhs_const: u64,
    model: &HashMap<String, BigUint>,
    prime: &BigUint,
) -> bool {
    let xval = model
        .get(var_name)
        .cloned()
        .unwrap_or_else(|| BigUint::from(0u32));
    let lhs = (BigUint::from(coeff_lhs) * xval) % prime;
    let rhs = BigUint::from(rhs_const) % prime;
    lhs == rhs
}

/// Property (5) MODEL CHECKING: when `solve_formula` reports Sat on a single
/// equality `c·x = k` over GF(p), the model MUST satisfy `c·m[x] ≡ k (mod p)`.
/// Spec source: SMT-LIB Eq semantics over a finite field. The expected value
/// is dictated by the equation, not by reading source.
#[test]
fn prop_sat_model_satisfies_single_eq_gf7() {
    let vn = names(&["x"]);
    let prime = BigUint::from(7u32);
    let f = eq(3, 0, 5); // 3·x = 5 ⇒ x = 4 (since 3·4 = 12 ≡ 5 mod 7)
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert!(
                lit_eq_holds_in_model(3, "x", 5, &m, &prime),
                "model must satisfy 3·x ≡ 5 (mod 7), got x={:?}",
                m.get("x")
            );
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

/// Property (7) EDGE PRIMES: solve `x = k` over GF(p) for several primes
/// (incl. GF(2), GF(3), GF(5), a moderate prime, and a large BN-style
/// prime). MATH: the unique solution is `k mod p`. The model's `x` MUST
/// equal `k mod p`. Independent of any source assumption about prime size.
#[test]
fn prop_unique_eq_solution_across_edge_primes() {
    let cases: &[(BigUint, u64)] = &[
        (BigUint::from(2u32), 1),
        (BigUint::from(3u32), 2),
        (BigUint::from(5u32), 4),
        (BigUint::from(101u32), 73),
        // BN254 scalar field prime (a real ZK use case).
        (
            BigUint::parse_bytes(
                b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
                10,
            )
            .unwrap(),
            12345,
        ),
    ];
    for (prime, k) in cases {
        let vn = names(&["x"]);
        let f = eq(1, 0, *k);
        let want = BigUint::from(*k) % prime;
        match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
            SolveOutcome::Sat(m) => {
                assert_eq!(
                    m.get("x"),
                    Some(&want),
                    "GF({}): x=k should give x={}",
                    prime,
                    want
                );
            }
            other => panic!("GF({}) k={}: expected Sat, got {:?}", prime, k, other),
        }
    }
}

/// Property (8) DETERMINISM: independent solver runs on the same formula
/// must return the same verdict class (Sat vs Unsat vs Unknown). No hidden
/// global state should make a second call differ. Spec: function purity.
#[test]
fn prop_determinism_two_calls_same_verdict_class() {
    let vn = names(&["x"]);
    let prime = BigUint::from(7u32);
    let f = Formula::Or(vec![eq(1, 0, 3), eq(1, 0, 5)]);
    let r1 = solve_formula(prime.clone(), &vn, &f, &CancelToken::none());
    let r2 = solve_formula(prime, &vn, &f, &CancelToken::none());
    let cls = |r: &SolveOutcome| match r {
        SolveOutcome::Sat(_) => "Sat",
        SolveOutcome::Unsat(_) => "Unsat",
        SolveOutcome::Unknown => "Unknown",
    };
    assert_eq!(cls(&r1), cls(&r2), "verdict class must be deterministic");
}

/// Property (5) MODEL CHECKING for a SAT disjunction: any model returned for
/// `(x=3) ∨ (x=5)` over GF(7) MUST satisfy at least one disjunct under SMT
/// disjunction semantics. Expected from logic, not source.
#[test]
fn prop_or_sat_model_satisfies_some_disjunct() {
    let vn = names(&["x"]);
    let prime = BigUint::from(7u32);
    let f = Formula::Or(vec![eq(1, 0, 3), eq(1, 0, 5)]);
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            let ok = lit_eq_holds_in_model(1, "x", 3, &m, &prime)
                || lit_eq_holds_in_model(1, "x", 5, &m, &prime);
            assert!(ok, "model must satisfy (x=3) or (x=5), got x={:?}", m.get("x"));
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

/// Property (1) IDENTITY / (5) MODEL CHECKING for an AND of `c·x = k` and
/// `c·x ≠ j` with j ≠ k mod p: the conjunction is logically equivalent to
/// the single eq, so any model satisfies both literals. MATH-derived.
#[test]
fn prop_and_eq_neq_consistent_model() {
    let vn = names(&["x"]);
    let prime = BigUint::from(7u32);
    // (1·x = 3) ∧ (1·x ≠ 5). Expected: x = 3.
    let f = Formula::And(vec![eq(1, 0, 3), neq(1, 0, 5)]);
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert!(lit_eq_holds_in_model(1, "x", 3, &m, &prime));
            assert!(!lit_eq_holds_in_model(1, "x", 5, &m, &prime));
        }
        other => panic!("expected Sat(x=3), got {:?}", other),
    }
}

/// Property (5) UNSAT MONOTONICITY: if `F` is UNSAT, then `F ∧ G` is UNSAT
/// for any G. Pin: take the contradictory pair `(x=5) ∧ (x=6)` (already
/// UNSAT over GF(101)) and AND in an arbitrary extra eq on a fresh var;
/// the conjunction remains UNSAT. Spec: classical-logic monotonicity.
#[test]
fn prop_unsat_monotonicity_under_conjunction() {
    let vn = names(&["x", "y"]);
    let prime = BigUint::from(101u32);
    let base = Formula::And(vec![eq(1, 0, 5), eq(1, 0, 6)]);
    let ext = Formula::And(vec![base, eq(1, 1, 7)]);
    assert!(
        matches!(
            solve_formula(prime, &vn, &ext, &CancelToken::none()),
            SolveOutcome::Unsat(_)
        ),
        "UNSAT base ∧ any G must remain UNSAT"
    );
}

/// Property (5) TAUTOLOGY: `(x = k) ∨ ¬(x = k)` is the law of the
/// excluded middle — always SAT over any prime. The model just needs to
/// exist. Spec: tertium non datur, propositional logic.
#[test]
fn prop_excluded_middle_is_sat() {
    let vn = names(&["x"]);
    for p in [2u32, 3, 5, 7, 101] {
        let prime = BigUint::from(p);
        let f = Formula::Or(vec![eq(1, 0, 3), neq(1, 0, 3)]);
        assert!(
            matches!(
                solve_formula(prime, &vn, &f, &CancelToken::none()),
                SolveOutcome::Sat(_)
            ),
            "GF({}): excluded middle must be SAT",
            p
        );
    }
}

/// Property (5) ENUMERATION EXHAUSTIVENESS: the formula `(x = 0) ∨ (x = 1)
/// ∨ ... ∨ (x = p-1)` is a tautology over GF(p) because every element of
/// GF(p) equals one of 0..p-1. MUST be SAT. MATH spec, not source.
#[test]
fn prop_full_enumeration_disjunction_is_sat() {
    let vn = names(&["x"]);
    for p in [2u32, 3, 5, 7] {
        let prime = BigUint::from(p);
        let disj: Vec<Formula> = (0..p as u64).map(|k| eq(1, 0, k)).collect();
        let f = Formula::Or(disj);
        let r = solve_formula(prime.clone(), &vn, &f, &CancelToken::none());
        match r {
            SolveOutcome::Sat(m) => {
                let v = m.get("x").cloned().unwrap_or_else(|| BigUint::from(0u32));
                assert!(v < prime, "GF({}): model value must be canonical", p);
            }
            other => panic!("GF({}): enumeration of all values must be SAT, got {:?}", p, other),
        }
    }
}

/// Property (5) UNSAT by FIELD EXHAUSTION: `(x = 0) ∧ (x ≠ 0) ∧ ... ∧ (x ≠
/// p-1)` would be UNSAT, but the simpler shape `(x = a) ∧ (x ≠ a)` is also
/// UNSAT (a direct contradiction). MATH: a literal and its negation cannot
/// both hold. Spec, not source.
#[test]
fn prop_eq_and_negation_is_unsat_across_primes() {
    let vn = names(&["x"]);
    for p in [3u32, 5, 7, 11, 101] {
        let prime = BigUint::from(p);
        let f = Formula::And(vec![eq(1, 0, 2), neq(1, 0, 2)]);
        assert!(
            matches!(
                solve_formula(prime, &vn, &f, &CancelToken::none()),
                SolveOutcome::Unsat(_)
            ),
            "GF({}): (x=2) ∧ (x≠2) must be UNSAT",
            p
        );
    }
}

/// Property (5) MODEL CHECKING in a multi-variable system:
/// `(x = 3) ∧ (y = 4)` over GF(7) → unique model x=3, y=4 (MATH-derived).
/// The model must contain BOTH bindings with the math values.
#[test]
fn prop_independent_vars_pinned_independently() {
    let vn = names(&["x", "y"]);
    let prime = BigUint::from(7u32);
    let f = Formula::And(vec![eq(1, 0, 3), eq(1, 1, 4)]);
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("x"), Some(&BigUint::from(3u32)));
            assert_eq!(m.get("y"), Some(&BigUint::from(4u32)));
        }
        other => panic!("expected Sat(x=3,y=4), got {:?}", other),
    }
}

/// Property (5) IFF SEMANTICS: `(x = 0) ∨ (x = 1) ∨ (x = 2)` over GF(3)
/// covers every residue, so it's a tautology — same as Formula::True.
/// MATH: GF(p) has exactly p elements. Both must be SAT.
#[test]
fn prop_gf3_full_coverage_equivalent_to_true() {
    let vn = names(&["x"]);
    let prime = BigUint::from(3u32);
    let f_all = Formula::Or(vec![eq(1, 0, 0), eq(1, 0, 1), eq(1, 0, 2)]);
    let r_all = solve_formula(prime.clone(), &vn, &f_all, &CancelToken::none());
    let r_true = solve_formula(prime, &vn, &Formula::True, &CancelToken::none());
    assert!(
        matches!(r_all, SolveOutcome::Sat(_)),
        "(x=0 ∨ x=1 ∨ x=2) over GF(3) must be SAT"
    );
    assert!(
        matches!(r_true, SolveOutcome::Sat(_)),
        "True must be SAT"
    );
}

/// Property (5) MODEL VALIDITY ACROSS DISJUNCTION: any reported SAT model
/// MUST satisfy every conjunct of the active disjunct. Hand-built: an OR
/// of three pairwise-incompatible `(x=k) ∧ (y=k)` conjuncts. MATH: the
/// returned (x, y) must coincide on one of the k values.
#[test]
fn prop_disjunction_of_conjunctions_consistent_model() {
    let vn = names(&["x", "y"]);
    let prime = BigUint::from(7u32);
    let f = Formula::Or(vec![
        Formula::And(vec![eq(1, 0, 1), eq(1, 1, 1)]),
        Formula::And(vec![eq(1, 0, 2), eq(1, 1, 2)]),
        Formula::And(vec![eq(1, 0, 3), eq(1, 1, 3)]),
    ]);
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            let x = m.get("x").cloned().unwrap_or_else(|| BigUint::from(0u32));
            let y = m.get("y").cloned().unwrap_or_else(|| BigUint::from(0u32));
            assert_eq!(x, y, "the active disjunct forces x = y");
            assert!(
                x == BigUint::from(1u32)
                    || x == BigUint::from(2u32)
                    || x == BigUint::from(3u32),
                "x must take one of the disjunct values"
            );
        }
        other => panic!("expected Sat, got {:?}", other),
    }
}

/// Property (5) NESTED NOT IS IDENTITY (NNF spec): `¬¬(x = k)` is
/// logically equivalent to `(x = k)`. A model satisfying one must
/// satisfy the other. MATH/RFC: SMT-LIB semantics of `not`.
#[test]
fn prop_double_negation_eq_is_sat_with_eq_model() {
    let vn = names(&["x"]);
    let prime = BigUint::from(7u32);
    let inner = eq(1, 0, 4);
    let f = Formula::Not(Box::new(Formula::Not(Box::new(inner))));
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert_eq!(
                m.get("x"),
                Some(&BigUint::from(4u32)),
                "¬¬(x=4) forces x=4"
            );
        }
        other => panic!("expected Sat(x=4), got {:?}", other),
    }
}

/// Property (5) DE MORGAN: `¬(A ∧ B)` ≡ `(¬A ∨ ¬B)`. Take A = (x=3) and
/// B = (x=5); both can't hold simultaneously over GF(7), so `¬(A∧B)` is
/// a tautology. MUST be SAT. SMT-LIB classical semantics.
#[test]
fn prop_de_morgan_negation_of_impossible_conjunction_is_sat() {
    let vn = names(&["x"]);
    let prime = BigUint::from(7u32);
    let a = eq(1, 0, 3);
    let b = eq(1, 0, 5);
    let f = Formula::Not(Box::new(Formula::And(vec![a, b])));
    assert!(
        matches!(
            solve_formula(prime, &vn, &f, &CancelToken::none()),
            SolveOutcome::Sat(_)
        ),
        "¬(impossible conjunction) is a tautology — must be SAT"
    );
}

/// Property (5) MODEL CONSISTENCY across `c·x` with non-unit coefficient:
/// over GF(7), `3·x = 1` forces x = inv(3) · 1 = 5 (since 3·5 = 15 ≡ 1
/// mod 7). MATH: Fermat's little theorem inverse. Pin the exact value.
#[test]
fn prop_non_unit_coeff_eq_pins_inverse() {
    let vn = names(&["x"]);
    let prime = BigUint::from(7u32);
    let f = eq(3, 0, 1);
    match solve_formula(prime, &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert_eq!(
                m.get("x"),
                Some(&BigUint::from(5u32)),
                "3·x = 1 in GF(7) forces x = 5"
            );
        }
        other => panic!("expected Sat(x=5), got {:?}", other),
    }
}

// ─────────── HARD-PROBE: SAT restart × theory propagation at orchestrator level ───────────
//
// These tests engineer the CDCL(T) loop into the specific edge cases the
// known restart-drain bug touched. Expected values are SPEC-derived from
// propositional / SMT semantics, never from inspecting the loop control
// flow. Cancellation tests use deterministic CancelToken sources (no
// real timer races).

/// SPEC: A pre-cancelled token forces `cdclt_loop` to Unknown on the
/// FIRST iteration, regardless of any pending theory work. Each scripted
/// shape (Idle / Progressed-trigger / Sat post_check / Unsat post_check /
/// Unknown post_check) is exercised so the cancellation guard is shown
/// to short-circuit BEFORE any scripted theory branch fires.
#[test]
fn hardprobe_cancel_short_circuits_loop_across_theory_scripts() {
    // Idle theory.
    {
        let mut sat = Solver::new();
        let mut th = ScriptedTheory::new();
        let r = cdclt_loop(&mut sat, &mut th, &CancelToken::cancelled());
        assert!(matches!(r, SolveOutcome::Unknown), "Idle: got {r:?}");
    }
    // Progressed-trigger.
    {
        let mut sat = Solver::new();
        let a = sat.new_var();
        let b = sat.new_var();
        let mut th = ScriptedTheory::new();
        th.props.push_back(vec![(b, true)]);
        th.reasons.insert(b, vec![(a, true)]);
        let r = cdclt_loop(&mut sat, &mut th, &CancelToken::cancelled());
        assert!(matches!(r, SolveOutcome::Unknown), "Progressed: got {r:?}");
    }
    // Post_check Sat.
    {
        let mut sat = Solver::new();
        let mut th = ScriptedTheory::new();
        th.checks.push_back(CheckOutcome::Sat);
        let r = cdclt_loop(&mut sat, &mut th, &CancelToken::cancelled());
        assert!(matches!(r, SolveOutcome::Unknown), "PostSat: got {r:?}");
    }
    // Post_check Unsat.
    {
        let mut sat = Solver::new();
        let v = sat.new_var();
        let mut th = ScriptedTheory::new();
        th.checks.push_back(CheckOutcome::Unsat { core: vec![v] });
        let r = cdclt_loop(&mut sat, &mut th, &CancelToken::cancelled());
        assert!(matches!(r, SolveOutcome::Unknown), "PostUnsat: got {r:?}");
    }
    // Post_check Unknown.
    {
        let mut sat = Solver::new();
        let mut th = ScriptedTheory::new();
        th.checks.push_back(CheckOutcome::Unknown);
        let r = cdclt_loop(&mut sat, &mut th, &CancelToken::cancelled());
        assert!(matches!(r, SolveOutcome::Unknown), "PostUnknown: got {r:?}");
    }
}

/// SPEC: A CancelToken cancelled AFTER the first iteration but before
/// any verdict still yields Unknown — never Sat / Unsat. We simulate
/// "mid-loop cancellation" by giving the loop a problem big enough to
/// take ≥ 2 iterations, then pre-cancelling the token. Since the loop
/// rechecks `cancel.is_cancelled()` at every iteration head, this MUST
/// route to Unknown.
#[test]
fn hardprobe_cancel_set_before_loop_invariant_outcome_is_unknown() {
    // A 4-var SAT instance: SAT is reachable but takes a few iterations.
    let mut sat = Solver::new();
    let v: Vec<Var> = (0..4).map(|_| sat.new_var()).collect();
    assert!(sat.add_clause(vec![Lit::pos(v[0]), Lit::pos(v[1])]));
    assert!(sat.add_clause(vec![Lit::neg(v[1]), Lit::pos(v[2])]));
    assert!(sat.add_clause(vec![Lit::neg(v[2]), Lit::pos(v[3])]));
    let mut th = ScriptedTheory::new();
    th.checks.push_back(CheckOutcome::Sat);
    let cancel = CancelToken::cancelled();
    let r = cdclt_loop(&mut sat, &mut th, &cancel);
    assert!(
        matches!(r, SolveOutcome::Unknown),
        "SPEC: pre-cancelled token must yield Unknown, not Sat (got {r:?})"
    );
}

/// SPEC: Theory propagation that derives a literal CONSISTENT with SAT's
/// current root assignment is a no-op (Idle). Multiple consecutive
/// Idle rounds must terminate in a non-pending verdict (Sat via
/// post_check), NOT loop forever. Hypothesis: a malformed
/// progressed/idle distinction could cause infinite Progressed loops.
#[test]
fn hardprobe_repeated_idle_theory_propagation_terminates_sat() {
    let mut sat = Solver::new();
    let a = sat.new_var();
    let c = sat.new_var();
    // a=True at root via a unit clause.
    assert!(sat.add_clause(vec![Lit::pos(a)]));
    // c is free; the theory propagates (a, true) repeatedly (no-op, since
    // a is already True at root). Each round is Idle. After idle, the
    // loop must reach post_check at the full assignment and accept Sat.
    let mut th = ScriptedTheory::new();
    // Several Idle rounds; ScriptedTheory falls back to Vec::new() once
    // queue is empty, which is Idle too — so no infinite re-prop danger.
    for _ in 0..3 {
        th.props.push_back(vec![(a, true)]);
    }
    th.checks.push_back(CheckOutcome::Sat);
    let r = cdclt_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "SPEC: repeated Idle must reach Sat, got {r:?}");
    assert_eq!(sat.value(a), LBool::True);
    // c picked positively (saved phase default).
    assert!(sat.value(c).is_defined());
}

/// SPEC: A theory that asserts UNSAT via a single-var ROOT core at the
/// very first post_check must yield UNSAT (after the unit lemma is
/// learnt and immediately re-asserted at root, the next round's
/// post_check produces a same-var core whose lemma is all-root ⇒
/// permanent UNSAT). This is the "root theory conflict" variant —
/// distinct from `loop_post_check_unsat_root_core_is_unsat` because
/// here we vary the surrounding setup with additional vars to stress
/// the resync.
#[test]
fn hardprobe_root_theory_conflict_with_extra_vars_yields_unsat() {
    let mut sat = Solver::new();
    let v: Vec<Var> = (0..3).map(|_| sat.new_var()).collect();
    let mut th = ScriptedTheory::new();
    // Every post_check returns the same unit core [v[0]]: the lemma
    // learns ¬v[0]; the next full assignment again has v[0] at some
    // polarity, and the same core forms an all-root lemma ⇒ UNSAT.
    for _ in 0..5 {
        th.checks.push_back(CheckOutcome::Unsat { core: vec![v[0]] });
    }
    let r = cdclt_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)), "SPEC: persistent root-core UNSAT, got {r:?}");
    assert!(sat.is_unsat());
    // v[0] must be at root level (0) regardless of which polarity was
    // assigned.
    assert!(sat.value(v[0]).is_defined());
}

/// SPEC: After a theory-propagation conflict resyncs the orchestrator,
/// the next iteration must NOT re-emit the same conflict. We script the
/// theory to propose `(a,false)` once (disagreement → Conflict + lemma);
/// the loop must then continue past the resync and reach Sat. A buggy
/// resync that keeps re-injecting the same theory propagation could
/// loop forever.
#[test]
fn hardprobe_theory_conflict_resync_does_not_redrive_same_propagation() {
    let mut sat = Solver::new();
    let a = sat.new_var();
    let b = sat.new_var();
    // b True at root.
    assert!(sat.add_clause(vec![Lit::pos(b)]));
    assert!(sat.propagate().is_none());
    // Decide a=True at level 1.
    assert!(sat.decide(Lit::pos(a)));
    let mut th = ScriptedTheory::new();
    // First round: disagreement on a.
    th.props.push_back(vec![(a, false)]);
    th.reasons.insert(a, vec![(b, true)]);
    // Subsequent rounds: no theory propagation (Idle from default).
    th.checks.push_back(CheckOutcome::Sat);
    let r = cdclt_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "SPEC: single conflict + resync must reach Sat, got {r:?}");
    // The lemma should have flipped a to False.
    assert_eq!(sat.value(a), LBool::False, "SPEC: lemma (¬a ∨ ¬b) flips a False");
    assert_eq!(sat.value(b), LBool::True);
}

/// SPEC: A `Theory::push` count equals SAT's max decision level reached
/// during a clean run. With one free var and a Sat post_check, the loop
/// makes exactly one decision (level 1) before post_check ⇒ one push.
/// This invariant must hold even when the theory's propagate() returns
/// a benign Idle-equivalent first.
/// Hypothesis: a desynced push/pop accounting between SAT and theory
/// would manifest as an unexpected pushes count.
#[test]
fn hardprobe_theory_push_count_matches_max_decision_level() {
    let mut sat = Solver::new();
    let v0 = sat.new_var();
    let mut th = ScriptedTheory::new();
    // First propagate is an inert (v0, ...) — wait, v0 is undef so a
    // (v0,true) would go through Progressed. Use an Idle empty queue.
    th.checks.push_back(CheckOutcome::Sat);
    let _ = cdclt_loop(&mut sat, &mut th, &CancelToken::none());
    assert_eq!(
        th.pushes, 1,
        "SPEC: max decision level was 1 ⇒ exactly one theory push (got {})",
        th.pushes
    );
    assert!(sat.value(v0).is_defined(), "SPEC: SAT must have decided v0");
}

/// SPEC: At loop termination (Sat / Unsat), the theory's push/pop
/// ledger must net to sat.decision_level(). This is the orchestrator's
/// core invariant ("theory_levels == decision_level"). Drive a clean
/// run that needs no lemma and verify the invariant. Hypothesis:
/// off-by-one or skipped push/pop would manifest as a mismatched net.
#[test]
fn hardprobe_theory_pop_count_matches_decision_level_clean_run() {
    let mut sat = Solver::new();
    let v: Vec<Var> = (0..3).map(|_| sat.new_var()).collect();
    let mut th = ScriptedTheory::new();
    th.checks.push_back(CheckOutcome::Sat);
    let r = cdclt_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "SPEC: loop must terminate Sat, got {r:?}");
    for var in &v {
        assert!(sat.value(*var).is_defined());
    }
    // SPEC: theory ledger net == decision level.
    let net = th.pushes as i64 - th.pops as i64;
    assert_eq!(
        net, sat.decision_level() as i64,
        "SPEC: theory level accounting must mirror SAT (push={}, pop={}, dl={})",
        th.pushes, th.pops, sat.decision_level()
    );
    // Each variable decision pushed one level ⇒ pushes == 3.
    assert_eq!(th.pushes, 3, "SPEC: 3 vars ⇒ 3 decisions ⇒ 3 pushes");
    assert_eq!(th.pops, 0, "SPEC: clean run has no backjumps ⇒ 0 pops");
}

/// SPEC: Restart-base independence at the FF-theory level — same CDCL(T)
/// problem over GF(7) must produce the same verdict whether iter_cap is
/// the default or a large value. This is a coarse restart-cadence proxy
/// at the orchestrator level (we can't tweak restart_base from here, but
/// iter_cap moderates how much work the loop does before bailing).
/// Hypothesis: a verdict regression that depended on a specific iter_cap
/// would be exposed.
#[test]
fn hardprobe_iter_cap_does_not_flip_verdict_on_decidable_instance() {
    let vn = names(&["x", "y"]);
    let prime = BigUint::from(7u32);
    let f = Formula::And(vec![
        eq(1, 0, 3),
        Formula::Or(vec![eq(1, 1, 2), eq(1, 1, 5)]),
    ]);
    // Default iter_cap.
    let r1 = solve_formula(prime.clone(), &vn, &f, &CancelToken::none());
    // Very large iter_cap.
    let r2 = {
        let _g = crate::config::ConfigGuard::with_override(|c| c.cdclt_iter_cap = 1_000_000);
        solve_formula(prime, &vn, &f, &CancelToken::none())
    };
    let cls = |r: &SolveOutcome| match r {
        SolveOutcome::Sat(_) => "Sat",
        SolveOutcome::Unsat(_) => "Unsat",
        SolveOutcome::Unknown => "Unknown",
    };
    assert_eq!(
        cls(&r1),
        cls(&r2),
        "SPEC: verdict must be invariant under iter_cap (default vs 1M; got {r1:?} vs {r2:?})"
    );
}

/// SPEC: A theory that returns Unsat at post_check with a core larger
/// than 1 yields a lemma that flips the search. The lemma must NOT be
/// re-emitted on the next round (since SAT's assignment now satisfies
/// the new clause). Test: 2-var instance, theory says UNSAT for v0=v1=T,
/// next assignment v0=T v1=F should be accepted.
#[test]
fn hardprobe_post_check_unsat_core_drives_alternative_assignment_sat() {
    let mut sat = Solver::new();
    let v: Vec<Var> = (0..2).map(|_| sat.new_var()).collect();
    let mut th = ScriptedTheory::new();
    // Block the (T, T) corner; accept any other corner.
    th.checks.push_back(CheckOutcome::Unsat { core: vec![v[0], v[1]] });
    th.checks.push_back(CheckOutcome::Sat);
    let r = cdclt_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "SPEC: alternative assignment must be Sat, got {r:?}");
    // The learnt clause (¬v[0] ∨ ¬v[1]) forbids (T, T).
    assert!(
        !(sat.value(v[0]) == LBool::True && sat.value(v[1]) == LBool::True),
        "SPEC: learnt clause forbids both True simultaneously"
    );
}

/// SPEC: A CancelToken cancelled mid-flight (between solve calls) must
/// not contaminate a FRESH token in a subsequent call. Hypothesis: a
/// global / static cancellation leak would manifest here.
#[test]
fn hardprobe_cancellation_does_not_leak_across_solve_calls() {
    let vn = names(&["x"]);
    let prime = BigUint::from(7u32);
    let f = eq(1, 0, 5);
    // First call: cancelled token ⇒ Unknown.
    let r1 = solve_formula(prime.clone(), &vn, &f, &CancelToken::cancelled());
    assert!(matches!(r1, SolveOutcome::Unknown), "SPEC: first call Unknown, got {r1:?}");
    // Second call: fresh token ⇒ Sat with x=5.
    let r2 = solve_formula(prime, &vn, &f, &CancelToken::none());
    match r2 {
        SolveOutcome::Sat(m) => assert_eq!(
            m.get("x"),
            Some(&BigUint::from(5u32)),
            "SPEC: fresh token must run the solver to completion"
        ),
        other => panic!("expected Sat(x=5), got {other:?}"),
    }
}

/// SPEC: A SAT-then-Unsat round-trip via the same CDCL(T) plumbing
/// across different primes — verdict class must depend only on the
/// formula's logical content, not on which prime arithmetic engaged.
/// Property: `(x = 0) ∧ (x ≠ 0)` is UNSAT in every prime ≥ 2.
#[test]
fn hardprobe_logical_contradiction_unsat_across_edge_primes() {
    let vn = names(&["x"]);
    let f = Formula::And(vec![eq(1, 0, 0), neq(1, 0, 0)]);
    for p in [2u64, 3, 5, 7, 11, 17, 101, 1009] {
        let r = solve_formula(BigUint::from(p), &vn, &f, &CancelToken::none());
        assert!(
            matches!(r, SolveOutcome::Unsat(_)),
            "SPEC: GF({p}) contradiction (x=0) ∧ (x≠0) must be UNSAT (got {r:?})"
        );
    }
}

/// SPEC: A nested-OR over disjoint equality literals is SAT iff some
/// literal is satisfiable. Over GF(7), `(x=0) ∨ (x=1) ∨ ... ∨ (x=6)` is
/// a tautology of GF(7) coverage. The CDCL(T) loop should reach SAT
/// regardless of restart pressure; we exercise it on multiple primes.
/// Hypothesis: a deep OR-tree could trigger restart at theory boundaries.
#[test]
fn hardprobe_full_coverage_disjunction_sat_across_primes() {
    let vn = names(&["x"]);
    for p in [2u64, 3, 5, 7, 11] {
        let prime = BigUint::from(p);
        let disjuncts: Vec<Formula> = (0..p).map(|k| eq(1, 0, k)).collect();
        let f = Formula::Or(disjuncts);
        let r = solve_formula(prime.clone(), &vn, &f, &CancelToken::none());
        match r {
            SolveOutcome::Sat(m) => {
                let xval = m.get("x").cloned().unwrap_or_else(|| BigUint::from(0u32));
                assert!(xval < prime, "SPEC: GF({p}): model must be canonical (x={xval})");
            }
            other => panic!("GF({p}): full coverage must be SAT, got {other:?}"),
        }
    }
}

/// SPEC: A CDCL(T) instance that needs MANY theory conflicts to refute
/// (a pin v=k AND-ed with a disjunction over k different values
/// excluding k itself) must be UNSAT and not flip to Unknown. Sweep
/// over a few primes to vary the search depth.
#[test]
fn hardprobe_many_theory_conflicts_yields_unsat_across_primes() {
    let vn = names(&["x"]);
    for p in [7u64, 11, 17] {
        let prime = BigUint::from(p);
        // (x = 0) ∧ ((x = 1) ∨ (x = 2) ∨ ... ∨ (x = p-1))
        // ⇒ AND-of-pinned-zero with non-zero disjunction = UNSAT.
        let nonzero: Vec<Formula> = (1..p).map(|k| eq(1, 0, k)).collect();
        let f = Formula::And(vec![eq(1, 0, 0), Formula::Or(nonzero)]);
        let r = solve_formula(prime, &vn, &f, &CancelToken::none());
        assert!(
            matches!(r, SolveOutcome::Unsat(_)),
            "SPEC: GF({p}) pin-zero ∧ non-zero-disj must be UNSAT (got {r:?})"
        );
    }
}

/// SPEC: For a FORMULA with multiple satisfying models, two solver
/// invocations under the same fresh CancelToken should both report Sat
/// (verdict-class determinism), and each model must satisfy the formula
/// under SMT-LIB semantics. Sweep over primes.
#[test]
fn hardprobe_or_eq_sat_models_satisfy_some_disjunct_sweep_primes() {
    let vn = names(&["x"]);
    for p in [5u64, 7, 11, 13, 17] {
        let prime = BigUint::from(p);
        // Disjuncts on small distinct residues 1, 2, 3 — non-trivially
        // SAT in every prime ≥ 5.
        let f = Formula::Or(vec![eq(1, 0, 1), eq(1, 0, 2), eq(1, 0, 3)]);
        let r = solve_formula(prime.clone(), &vn, &f, &CancelToken::none());
        match r {
            SolveOutcome::Sat(m) => {
                let xv = m
                    .get("x")
                    .cloned()
                    .unwrap_or_else(|| BigUint::from(0u32));
                assert!(
                    xv == BigUint::from(1u32)
                        || xv == BigUint::from(2u32)
                        || xv == BigUint::from(3u32),
                    "SPEC: GF({p}) disjunction model must take one of {{1,2,3}}, got {xv}"
                );
            }
            other => panic!("GF({p}): expected Sat, got {other:?}"),
        }
    }
}

/// SPEC: A scripted theory that ALTERNATES propagations on different
/// vars must not desync push/pop accounting between SAT and theory. We
/// drive: round 1 propagate (b=True | reason a=True), then post_check
/// Sat. SAT must reach Sat with the theory's push/pop ledger balanced.
#[test]
fn hardprobe_theory_propagation_then_postcheck_push_pop_ledger_balanced() {
    let mut sat = Solver::new();
    let a = sat.new_var();
    let b = sat.new_var();
    // a True at root via a unit, so b's reason fact is currently True.
    assert!(sat.add_clause(vec![Lit::pos(a)]));
    let mut th = ScriptedTheory::new();
    th.props.push_back(vec![(b, true)]);
    th.reasons.insert(b, vec![(a, true)]);
    th.checks.push_back(CheckOutcome::Sat);
    let r = cdclt_loop(&mut sat, &mut th, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Sat(_)), "SPEC: loop must reach Sat, got {r:?}");
    // After loop end, sat.decision_level() == th.pushes - th.pops.
    let net = th.pushes as i64 - th.pops as i64;
    assert_eq!(
        net, sat.decision_level() as i64,
        "SPEC: push/pop must net to current decision level (push={}, pop={}, dl={})",
        th.pushes, th.pops, sat.decision_level()
    );
}

// =============================================================================
// HARD-PROBE: bitprop × CDCL(T) end-to-end via solve_formula.
//
// Spec recap (math, not source):
//   * k-bit bitsum `b_0 + 2·b_1 + ... + 2^{k-1}·b_{k-1}` with `b_i ∈ {0,1}`
//     represents a unique integer in `[0, 2^k)`.
//   * Bit-constraint literal: `b_i · b_i = b_i`.
//   * Pin form `b_0 + 2·b_1 + ... = v`:
//      - v ∈ [0, 2^k) AND 2^k ≤ p  ⇒  SAT, unique decomposition.
//      - v ∈ [2^k, p) (with 2^k ≤ p) ⇒  UNSAT (overflow).
//      - 2^k > p ⇒ bitprop MUST NOT fabricate UNSAT (mod-p collisions admit
//        real integer solutions; verdict-flipping = R5 H1 / R7 J1 class).
//   * Cancel: pre-cancelled token ⇒ Unknown (never SAT/UNSAT).
//   * Determinism: same formula → same verdict class and same unique model.
// =============================================================================

/// Bit-constraint literal for variable `idx`: `b_idx^2 = b_idx`.
fn bit_constraint(var_idx: u32) -> Formula {
    Formula::Lit(crate::boolean::Literal::Eq(
        vec![PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(var_idx, 2)],
        }],
        vec![PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(var_idx, 1)],
        }],
    ))
}

/// k-bit bitsum pin: `b_0 + 2·b_1 + ... = v`.
fn bitsum_eq_const(bit_idxs: &[u32], v: u64) -> Formula {
    let lhs: Vec<PolyTerm> = bit_idxs
        .iter()
        .enumerate()
        .map(|(i, &b)| PolyTerm {
            coeff: BigUint::from(1u64 << i),
            vars: vec![(b, 1)],
        })
        .collect();
    let rhs = vec![PolyTerm {
        coeff: BigUint::from(v),
        vars: vec![],
    }];
    Formula::Lit(crate::boolean::Literal::Eq(lhs, rhs))
}

/// HARD-PROBE: pin under fitting prime gives unique decomposition.
/// v=5 → (1,0,1) over GF(101).
#[test]
fn hardprobe_bitsum_pinned_value_yields_unique_decomposition() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bitsum_eq_const(&[0, 1, 2], 5),
    ]);
    match solve_formula(prime, &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)), "spec: b0 = 1");
            assert_eq!(m.get("b1"), Some(&BigUint::from(0u32)), "spec: b1 = 0");
            assert_eq!(m.get("b2"), Some(&BigUint::from(1u32)), "spec: b2 = 1");
        }
        other => panic!("bitsum pinned must be SAT, got {:?}", other),
    }
}

/// HARD-PROBE: bitsum overflow under fitting prime: v=10, 3 bits.
#[test]
fn hardprobe_bitsum_overflow_is_unsat_large_prime() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bitsum_eq_const(&[0, 1, 2], 10),
    ]);
    let r = solve_formula(prime, &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)),
        "spec: v=10 > 2^3 with bits, must be UNSAT, got {:?}", r);
}

/// HARD-PROBE: overflow at the BOUNDARY v = 2^k. Smallest UNSAT value.
#[test]
fn hardprobe_bitsum_overflow_at_minimum_out_of_range() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bitsum_eq_const(&[0, 1, 2], 8),
    ]);
    let r = solve_formula(prime, &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)),
        "spec: v=8 = 2^3 is first overflow, must be UNSAT, got {:?}", r);
}

/// HARD-PROBE: GF(7) 3-bit collision case (R5 H1 neighbourhood).
/// 2^3 = 8 > 7 so bitprop's fit guard MUST refuse propagation. Pinning
/// the sum to 0 admits (0,0,0) and (1,1,1) (since 7 ≡ 0); adding b0 = 1
/// keeps only (1,1,1) as a real solution. If bitprop unsoundly pinned
/// every b_i to 0 (the mod-p residue), the verdict would flip to UNSAT.
#[test]
fn hardprobe_gf7_3bit_collision_keeps_real_solution() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(7u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bitsum_eq_const(&[0, 1, 2], 0),
        eq(1, 0, 1),
    ]);
    let r = solve_formula(prime, &vn, &f, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)));
            assert_eq!(m.get("b1"), Some(&BigUint::from(1u32)));
            assert_eq!(m.get("b2"), Some(&BigUint::from(1u32)));
        }
        SolveOutcome::Unsat(_) => panic!(
            "GF(7) collision: (1,1,1) is a real solution; UNSAT is unsound (R5 H1 / R7 J1 class)"
        ),
        SolveOutcome::Unknown => {}
    }
}

/// HARD-PROBE: GF(11) 3-bit exhaustive sweep. 2^3 = 8 ≤ 11 → fits.
/// Spec: v ∈ [0,7] SAT (unique decomposition); v ∈ {8,9,10} UNSAT.
#[test]
fn hardprobe_gf11_3bit_exhaustive() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(11u32);
    for v in 0u64..11 {
        let f = Formula::And(vec![
            bit_constraint(0),
            bit_constraint(1),
            bit_constraint(2),
            bitsum_eq_const(&[0, 1, 2], v),
        ]);
        let r = solve_formula(prime.clone(), &vn, &f, &CancelToken::none());
        if v < 8 {
            match r {
                SolveOutcome::Sat(m) => {
                    let b0 = m.get("b0").cloned().unwrap_or(BigUint::from(0u32));
                    let b1 = m.get("b1").cloned().unwrap_or(BigUint::from(0u32));
                    let b2 = m.get("b2").cloned().unwrap_or(BigUint::from(0u32));
                    for (n, b) in [("b0", &b0), ("b1", &b1), ("b2", &b2)] {
                        assert!(
                            b == &BigUint::from(0u32) || b == &BigUint::from(1u32),
                            "v={} {}: not a bit: {:?}", v, n, b
                        );
                    }
                    assert_eq!(b0, BigUint::from(v & 1), "v={}: b0 spec", v);
                    assert_eq!(b1, BigUint::from((v >> 1) & 1), "v={}: b1 spec", v);
                    assert_eq!(b2, BigUint::from((v >> 2) & 1), "v={}: b2 spec", v);
                }
                other => panic!("v={}: expected Sat, got {:?}", v, other),
            }
        } else {
            assert!(matches!(r, SolveOutcome::Unsat(_)),
                "v={}: spec overflow must be UNSAT, got {:?}", v, r);
        }
    }
}

/// HARD-PROBE: BN254 8-bit bitsum at adversarial pattern 0xA5.
#[test]
fn hardprobe_bn254_8bit_bitsum() {
    let vn = names(&["b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7"]);
    let prime = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    ).unwrap();
    let v = 0xA5u64;
    let mut conjuncts: Vec<Formula> = (0..8u32).map(bit_constraint).collect();
    conjuncts.push(bitsum_eq_const(&(0..8u32).collect::<Vec<_>>(), v));
    let f = Formula::And(conjuncts);
    match solve_formula(prime, &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            for i in 0..8 {
                let bi = (v >> i) & 1;
                let key = format!("b{}", i);
                assert_eq!(
                    m.get(&key),
                    Some(&BigUint::from(bi)),
                    "BN254 v=0x{:x}: bit{} expected {}", v, i, bi
                );
            }
        }
        other => panic!("BN254 bitsum: expected Sat, got {:?}", other),
    }
}

/// HARD-PROBE: NON-power-of-2 coefficients. `b0 + 3·b1 + 5·b2 = 4` →
/// unique solution (1, 1, 0). Bitprop assumes power-of-2 chains; if it
/// mis-attributes this pattern, the verdict can be wrong.
#[test]
fn hardprobe_non_powerof2_coeffs_still_solvable() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let lhs = vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0, 1)] },
        PolyTerm { coeff: BigUint::from(3u32), vars: vec![(1, 1)] },
        PolyTerm { coeff: BigUint::from(5u32), vars: vec![(2, 1)] },
    ];
    let rhs = vec![PolyTerm { coeff: BigUint::from(4u32), vars: vec![] }];
    let bs_eq = Formula::Lit(crate::boolean::Literal::Eq(lhs, rhs));
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bs_eq,
    ]);
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            let b0 = m.get("b0").cloned().unwrap_or(BigUint::from(0u32));
            let b1 = m.get("b1").cloned().unwrap_or(BigUint::from(0u32));
            let b2 = m.get("b2").cloned().unwrap_or(BigUint::from(0u32));
            for (n, v) in [("b0", &b0), ("b1", &b1), ("b2", &b2)] {
                assert!(
                    v == &BigUint::from(0u32) || v == &BigUint::from(1u32),
                    "{}: not a bit: {:?}", n, v
                );
            }
            let sum = (&b0 + BigUint::from(3u32) * &b1 + BigUint::from(5u32) * &b2) % &prime;
            assert_eq!(sum, BigUint::from(4u32), "model violates 1b0+3b1+5b2=4");
            assert_eq!(b0, BigUint::from(1u32), "spec unique: b0=1");
            assert_eq!(b1, BigUint::from(1u32), "spec unique: b1=1");
            assert_eq!(b2, BigUint::from(0u32), "spec unique: b2=0");
        }
        other => panic!("non-pow2 coeffs: expected Sat(1,1,0), got {:?}", other),
    }
}

/// HARD-PROBE: parity-violating bitsum. 2b0+4b1+6b2=3 — LHS even, RHS odd
/// ⇒ UNSAT regardless of bits.
#[test]
fn hardprobe_parity_violation_unsat() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let lhs = vec![
        PolyTerm { coeff: BigUint::from(2u32), vars: vec![(0, 1)] },
        PolyTerm { coeff: BigUint::from(4u32), vars: vec![(1, 1)] },
        PolyTerm { coeff: BigUint::from(6u32), vars: vec![(2, 1)] },
    ];
    let rhs = vec![PolyTerm { coeff: BigUint::from(3u32), vars: vec![] }];
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        Formula::Lit(crate::boolean::Literal::Eq(lhs, rhs)),
    ]);
    let r = solve_formula(prime, &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)),
        "parity-violating bitsum eq must be UNSAT, got {:?}", r);
}

/// HARD-PROBE: pre-cancelled token on a bitsum formula returns Unknown.
#[test]
fn hardprobe_bitsum_pre_cancelled_returns_unknown() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bitsum_eq_const(&[0, 1, 2], 5),
    ]);
    let r = solve_formula(prime, &vn, &f, &CancelToken::cancelled());
    assert!(matches!(r, SolveOutcome::Unknown),
        "pre-cancelled bitsum solve must return Unknown, got {:?}", r);
}

/// HARD-PROBE: bitsum determinism.
#[test]
fn hardprobe_bitsum_determinism_across_runs() {
    let vn = names(&["b0", "b1", "b2", "b3"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bit_constraint(3),
        bitsum_eq_const(&[0, 1, 2, 3], 11),  // (1,1,0,1)
    ]);
    let r1 = solve_formula(prime.clone(), &vn, &f, &CancelToken::none());
    let r2 = solve_formula(prime, &vn, &f, &CancelToken::none());
    match (r1, r2) {
        (SolveOutcome::Sat(m1), SolveOutcome::Sat(m2)) => {
            for n in ["b0", "b1", "b2", "b3"] {
                assert_eq!(m1.get(n), m2.get(n),
                    "non-deterministic model: {} differs", n);
            }
            assert_eq!(m1.get("b0"), Some(&BigUint::from(1u32)));
            assert_eq!(m1.get("b1"), Some(&BigUint::from(1u32)));
            assert_eq!(m1.get("b2"), Some(&BigUint::from(0u32)));
            assert_eq!(m1.get("b3"), Some(&BigUint::from(1u32)));
        }
        (r1, r2) => panic!("non-deterministic verdict: {:?} vs {:?}", r1, r2),
    }
}

/// HARD-PROBE: disjunction of two bitsum pins. CDCL(T) chooses one;
/// model must satisfy that disjunct.
#[test]
fn hardprobe_bitsum_disjunction_is_sat() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        Formula::Or(vec![
            bitsum_eq_const(&[0, 1, 2], 5),
            bitsum_eq_const(&[0, 1, 2], 2),
        ]),
    ]);
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            let b0 = m.get("b0").cloned().unwrap_or(BigUint::from(0u32));
            let b1 = m.get("b1").cloned().unwrap_or(BigUint::from(0u32));
            let b2 = m.get("b2").cloned().unwrap_or(BigUint::from(0u32));
            let sum = (&b0 + BigUint::from(2u32) * &b1 + BigUint::from(4u32) * &b2) % &prime;
            assert!(
                sum == BigUint::from(5u32) || sum == BigUint::from(2u32),
                "model must satisfy one disjunct, sum = {:?}", sum
            );
        }
        other => panic!("bitsum disjunction must be SAT, got {:?}", other),
    }
}

/// HARD-PROBE: two overlapping bitsums force unique model.
/// b0+2b1+4b2=5 ∧ b0+2b1=1 → b0=1, b1=0, b2=1.
#[test]
fn hardprobe_two_overlapping_bitsums_force_unique_model() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bitsum_eq_const(&[0, 1, 2], 5),
        bitsum_eq_const(&[0, 1], 1),
    ]);
    match solve_formula(prime, &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)), "overlapping: b0=1");
            assert_eq!(m.get("b1"), Some(&BigUint::from(0u32)), "overlapping: b1=0");
            assert_eq!(m.get("b2"), Some(&BigUint::from(1u32)), "overlapping: b2=1");
        }
        other => panic!("expected Sat unique decomposition, got {:?}", other),
    }
}

/// HARD-PROBE: same bitsum, two distinct pins → contradiction → UNSAT.
#[test]
fn hardprobe_same_bitsum_two_distinct_pins_unsat() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bit_constraint(2),
        bitsum_eq_const(&[0, 1, 2], 5),
        bitsum_eq_const(&[0, 1, 2], 2),
    ]);
    let r = solve_formula(prime, &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)),
        "two distinct pins on same sum must be UNSAT, got {:?}", r);
}

/// HARD-PROBE: bitsum WITHOUT bit constraints. b_i free → many models.
/// Must NOT spuriously UNSAT.
#[test]
fn hardprobe_bitsum_without_bit_constraints_is_sat() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(101u32);
    let f = bitsum_eq_const(&[0, 1, 2], 5);
    match solve_formula(prime.clone(), &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            let b0 = m.get("b0").cloned().unwrap_or(BigUint::from(0u32));
            let b1 = m.get("b1").cloned().unwrap_or(BigUint::from(0u32));
            let b2 = m.get("b2").cloned().unwrap_or(BigUint::from(0u32));
            let sum = (&b0 + BigUint::from(2u32) * &b1 + BigUint::from(4u32) * &b2) % &prime;
            assert_eq!(sum, BigUint::from(5u32), "model violates bitsum eq");
        }
        other => panic!("bitsum w/o bit constraints: expected Sat, got {:?}", other),
    }
}

/// HARD-PROBE: GF(5) 2-bit. v=3 → (1,1).
#[test]
fn hardprobe_gf5_2bit_bitsum_unique() {
    let vn = names(&["b0", "b1"]);
    let prime = BigUint::from(5u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bit_constraint(1),
        bitsum_eq_const(&[0, 1], 3),
    ]);
    match solve_formula(prime, &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)));
            assert_eq!(m.get("b1"), Some(&BigUint::from(1u32)));
        }
        other => panic!("GF(5) 2-bit v=3: expected Sat(1,1), got {:?}", other),
    }
}

/// HARD-PROBE: GF(3) 1-bit. v=1 → b0=1. Tiniest case.
#[test]
fn hardprobe_gf3_1bit_bitsum_unique() {
    let vn = names(&["b0"]);
    let prime = BigUint::from(3u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        bitsum_eq_const(&[0], 1),
    ]);
    match solve_formula(prime, &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)));
        }
        other => panic!("GF(3) 1-bit v=1: expected Sat(b0=1), got {:?}", other),
    }
}

/// HARD-PROBE: edge-prime sweep with a fitting bitsum.
#[test]
fn hardprobe_bitsum_v3_across_fitting_primes() {
    for prime_val in [5u32, 7, 11, 13, 17, 101, 257, 1009] {
        let vn = names(&["b0", "b1"]);
        let prime = BigUint::from(prime_val);
        let f = Formula::And(vec![
            bit_constraint(0),
            bit_constraint(1),
            bitsum_eq_const(&[0, 1], 3),
        ]);
        let r = solve_formula(prime, &vn, &f, &CancelToken::none());
        match r {
            SolveOutcome::Sat(m) => {
                assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)),
                    "p={}: b0 = 1", prime_val);
                assert_eq!(m.get("b1"), Some(&BigUint::from(1u32)),
                    "p={}: b1 = 1", prime_val);
            }
            other => panic!("p={}: expected Sat(1,1), got {:?}", prime_val, other),
        }
    }
}

/// HARD-PROBE: bit ∧ ≠0 ∧ ≠1 over GF(101) → UNSAT.
#[test]
fn hardprobe_bit_constraint_with_two_diseqs_unsat() {
    let vn = names(&["b0"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        neq(1, 0, 0),
        neq(1, 0, 1),
    ]);
    let r = solve_formula(prime, &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)),
        "bit ∧ ≠0 ∧ ≠1 must be UNSAT, got {:?}", r);
}

/// HARD-PROBE: bit ∧ ≠0 ∧ ≠1 over GF(5) — small-prime field-polys engage.
#[test]
fn hardprobe_bit_constraint_with_two_diseqs_gf5_unsat() {
    let vn = names(&["b0"]);
    let prime = BigUint::from(5u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        neq(1, 0, 0),
        neq(1, 0, 1),
    ]);
    let r = solve_formula(prime, &vn, &f, &CancelToken::none());
    assert!(matches!(r, SolveOutcome::Unsat(_)),
        "GF(5) bit ∧ ≠0 ∧ ≠1 must be UNSAT, got {:?}", r);
}

/// HARD-PROBE: bit ∧ ≠0 forces b=1.
#[test]
fn hardprobe_bit_and_neq_zero_pins_to_one() {
    let vn = names(&["b0"]);
    let prime = BigUint::from(101u32);
    let f = Formula::And(vec![
        bit_constraint(0),
        neq(1, 0, 0),
    ]);
    match solve_formula(prime, &vn, &f, &CancelToken::none()) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)),
                "bit ∧ ≠0 forces b=1");
        }
        other => panic!("expected Sat(b=1), got {:?}", other),
    }
}

/// HARD-PROBE: GF(7) 3-bit, ALL 7 fitting pin values must be SAT.
/// 2^3 = 8 > 7, so bitprop's fit guard MUST refuse propagation, and the
/// theory must find the (unique) bit assignment that satisfies each.
/// Any UNSAT here is verdict-flipping unsoundness (R5 H1 class).
#[test]
fn hardprobe_gf7_3bit_all_pins_must_be_sat() {
    let vn = names(&["b0", "b1", "b2"]);
    let prime = BigUint::from(7u32);
    for v in 0u64..7 {
        let f = Formula::And(vec![
            bit_constraint(0),
            bit_constraint(1),
            bit_constraint(2),
            bitsum_eq_const(&[0, 1, 2], v),
        ]);
        let r = solve_formula(prime.clone(), &vn, &f, &CancelToken::none());
        match r {
            SolveOutcome::Sat(m) => {
                let b0 = m.get("b0").cloned().unwrap_or(BigUint::from(0u32));
                let b1 = m.get("b1").cloned().unwrap_or(BigUint::from(0u32));
                let b2 = m.get("b2").cloned().unwrap_or(BigUint::from(0u32));
                for (n, b) in [("b0", &b0), ("b1", &b1), ("b2", &b2)] {
                    assert!(
                        b == &BigUint::from(0u32) || b == &BigUint::from(1u32),
                        "GF(7) v={}: {} not a bit: {:?}", v, n, b
                    );
                }
                let sum = (&b0 + BigUint::from(2u32) * &b1 + BigUint::from(4u32) * &b2) % &prime;
                assert_eq!(sum, BigUint::from(v),
                    "GF(7) v={}: model sums to {:?}, not v", v, sum);
            }
            SolveOutcome::Unsat(_) => panic!(
                "GF(7) v={}: real solution exists; UNSAT is unsound (R5 H1 class)", v
            ),
            SolveOutcome::Unknown => {}
        }
    }
}
