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
