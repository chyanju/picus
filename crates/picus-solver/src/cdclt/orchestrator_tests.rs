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
