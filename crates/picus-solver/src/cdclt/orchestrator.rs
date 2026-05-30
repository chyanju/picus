//! CDCL(T) main loop.
//!
//! Drives [`sat::Solver`] step by step, notifying the theory plug-in
//! of each newly-committed literal and consulting it at full
//! assignment. Theory conflicts become learnt clauses via
//! [`sat::Solver::add_theory_lemma_with_trail`].

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::boolean::Formula;
use crate::core::SolveOutcome;
use crate::sat::{LBool, Lit, Solver, Var};
use crate::timeout::CancelToken;

use super::atoms::AtomTable;
use super::cnf::{tseitin, TseitinResult};
use super::ff_theory::FfTheory;
use super::multi_prime::FfTheoryRouter;
use super::theory::{CheckOutcome, Theory};

/// Solve a `Formula` over GF(`prime`) via CDCL(T) with the FF theory.
/// `var_names` is the producing builder's variable frame (used by
/// the SAT-side atom table to reverse-resolve `PolyTerm` indices to
/// names for `AtomKey` canonicalisation). `Sat(model)` carries the
/// FF variable assignments; `Unknown` is returned on cancellation,
/// theory `Unknown`, or iteration cap.
pub fn solve_formula(
    prime: BigUint,
    var_names: &[String],
    formula: &Formula,
    cancel: &CancelToken,
) -> SolveOutcome {
    let mut sat = Solver::new();
    let mut atoms = AtomTable::new(prime);
    let top = match tseitin(formula, var_names, &mut atoms, &mut sat) {
        TseitinResult::Constant(true) => return SolveOutcome::Sat(HashMap::new()),
        TseitinResult::Constant(false) => return SolveOutcome::Unsat(Vec::new()),
        TseitinResult::Lit(l) => l,
    };
    if !sat.add_clause(vec![top]) {
        return SolveOutcome::Unsat(Vec::new());
    }
    if sat.is_unsat() {
        return SolveOutcome::Unsat(Vec::new());
    }

    if picus_core::config::with(|c| c.cdclt_multi_prime_router) {
        // Capability-only path: route every non-aux atom through a
        // single-slot `FfTheoryRouter`. Path-equivalent to `FfTheory`
        // on single-prime input, with the router's per-slot dispatch
        // exercised against the production corpus before any
        // multi-prime parser lift can ride on it.
        let mut router = FfTheoryRouter::new(vec![atoms], cancel);
        let n_slots = router.slot_atoms_mut(0).n_atom_slots();
        for i in 0..n_slots {
            let v = Var(i as u32);
            if router.slot_atoms_mut(0).atom(v).is_some() {
                router.assign_var(v, 0);
            }
        }
        return cdclt_loop(&mut sat, &mut router, cancel);
    }
    let mut theory = FfTheory::new(&atoms, cancel);
    cdclt_loop(&mut sat, &mut theory, cancel)
}

/// Max CDCL(T) main-loop iterations before [`cdclt_loop`] returns
/// `Unknown`. Configured via [`crate::config::RuntimeConfig::cdclt_iter_cap`].
pub fn iter_cap() -> u64 {
    crate::config::with(|c| c.cdclt_iter_cap)
}

fn cdclt_loop<T: Theory>(
    sat: &mut Solver,
    theory: &mut T,
    cancel: &CancelToken,
) -> SolveOutcome {
    let mut notified: usize = 0;
    let mut theory_levels: usize = 0;
    let cap = iter_cap();
    let mut iters: u64 = 0;

    loop {
        if cancel.is_cancelled() {
            return SolveOutcome::Unknown;
        }
        iters += 1;
        if iters > cap {
            return SolveOutcome::Unknown;
        }

        if let Some(conflict) = sat.propagate() {
            if sat.decision_level() == 0 {
                return SolveOutcome::Unsat(Vec::new());
            }
            let (learnt, bt) = match sat.analyze(conflict) {
                Some(lb) => lb,
                None => return SolveOutcome::Unknown,
            };
            sat.backtrack_to(bt);
            // Snapshot trail length before `learn_clause` so the next
            // notify pass starts at the position the asserting literal
            // is about to occupy.
            let trail_pre_lemma = sat.trail_len();
            sat.learn_clause(learnt);
            if sat.should_restart() {
                sat.perform_restart();
            }
            resync_after_lemma(sat, theory, &mut theory_levels, &mut notified, trail_pre_lemma);
            continue;
        }

        sync_theory_after_propagate(sat, theory, &mut theory_levels);
        let trail = sat.trail();
        while notified < trail.len() {
            let lit = trail[notified];
            theory.notify_fact(lit.var(), lit.is_positive());
            notified += 1;
        }

        match run_theory_propagation(sat, theory) {
            TheoryStep::Progressed => continue,
            TheoryStep::Conflict(trail_pre_lemma) => {
                resync_after_lemma(sat, theory, &mut theory_levels, &mut notified, trail_pre_lemma);
                continue;
            }
            TheoryStep::RootUnsat => return SolveOutcome::Unsat(Vec::new()),
            TheoryStep::GiveUp => return SolveOutcome::Unknown,
            TheoryStep::Idle => {}
        }

        if sat.all_assigned() {
            match theory.post_check() {
                CheckOutcome::Sat => {
                    // The model returned by the theory's final
                    // `post_check` already covers every named
                    // variable: Bool vars are encoded as FF elements
                    // in {0, 1} in the polynomial namespace, so they
                    // come through the GB SAT point alongside the FF
                    // vars. SAT-only aux vars (Tseitin literals) are
                    // intentionally not surfaced.
                    let model = theory.collect_model().unwrap_or_default();
                    return SolveOutcome::Sat(model);
                }
                CheckOutcome::Unsat { core } => {
                    let trail_pre_lemma = apply_theory_conflict(sat, &core);
                    let trail_pre_lemma = match trail_pre_lemma {
                        Some(n) => n,
                        None if sat.gave_up() => return SolveOutcome::Unknown,
                        None => return SolveOutcome::Unsat(Vec::new()),
                    };
                    resync_after_lemma(sat, theory, &mut theory_levels, &mut notified, trail_pre_lemma);
                    continue;
                }
                CheckOutcome::Unknown => return SolveOutcome::Unknown,
            }
        }

        let next = sat.pick_decision().expect("not all assigned ⇒ Undef var exists");
        let ok = sat.decide(next);
        debug_assert!(ok);
    }
}

enum TheoryStep {
    /// No new derivation fired this round.
    Idle,
    /// At least one new literal was enqueued.
    Progressed,
    /// Lemma learnt and SAT backtracked; caller must sync theory.
    /// The wrapped value is the trail length right before the lemma's
    /// asserting literal was enqueued (see `add_theory_lemma_with_trail`).
    Conflict(usize),
    /// Lemma forced root-level UNSAT.
    RootUnsat,
    /// Theory-conflict resolution bailed; solve is Unknown (not UNSAT).
    GiveUp,
}

/// One round of theory propagation. Each derived `(atom, polarity)`
/// becomes a no-op (SAT agrees), an `enqueue_theory` (SAT Undef), or a
/// theory lemma (SAT disagrees).
fn run_theory_propagation<T: Theory>(sat: &mut Solver, theory: &mut T) -> TheoryStep {
    let props = theory.propagate();
    if props.is_empty() {
        return TheoryStep::Idle;
    }
    let mut progressed = false;
    for (atom_var, polarity) in props {
        let prop_lit = if polarity {
            Lit::pos(atom_var)
        } else {
            Lit::neg(atom_var)
        };
        match sat.value(atom_var) {
            LBool::Undef => {
                let reason_facts = theory.explain(atom_var, polarity);
                let reason_lits: Vec<Lit> = reason_facts
                    .iter()
                    .map(|&(v, p)| if p { Lit::pos(v) } else { Lit::neg(v) })
                    .collect();
                if sat.enqueue_theory(prop_lit, reason_lits) {
                    progressed = true;
                }
            }
            LBool::True if polarity => {}
            LBool::False if !polarity => {}
            _ => {
                let reason_facts = theory.explain(atom_var, polarity);
                let mut lemma: Vec<Lit> = Vec::with_capacity(reason_facts.len() + 1);
                lemma.push(prop_lit);
                for (fav, fpol) in reason_facts {
                    let fl = if fpol { Lit::pos(fav) } else { Lit::neg(fav) };
                    lemma.push(-fl);
                }
                match sat.add_theory_lemma_with_trail(lemma) {
                    Some(trail_pre) => return TheoryStep::Conflict(trail_pre),
                    None if sat.gave_up() => return TheoryStep::GiveUp,
                    None => return TheoryStep::RootUnsat,
                }
            }
        }
    }
    if progressed {
        TheoryStep::Progressed
    } else {
        TheoryStep::Idle
    }
}

/// Turn an atom-core into a SAT lemma and apply it. On success returns
/// `Some(trail_len_before_asserting)` (the position the lemma's
/// asserting literal sits at after the internal backtrack). Returns
/// `None` if the lemma forces root-level UNSAT. An Undef core var
/// indicates the theory's push/pop state diverged from SAT's.
fn apply_theory_conflict(sat: &mut Solver, core: &[Var]) -> Option<usize> {
    let mut lits: Vec<Lit> = Vec::with_capacity(core.len());
    for &v in core {
        match sat.value(v) {
            LBool::True => lits.push(Lit::neg(v)),
            LBool::False => lits.push(Lit::pos(v)),
            LBool::Undef => {
                // A theory core literal that is unassigned in SAT means the
                // theory's fact trail diverged from SAT's assignment (a
                // push/pop accounting violation). Building a conflict clause
                // from a partial core, or reporting UNSAT, would be unsound;
                // bail to Unknown instead of panicking on a valid input.
                log::warn!(
                    "theory core var {:?} is Undef (theory/SAT trail divergence); giving up to Unknown",
                    v
                );
                sat.mark_give_up();
                return None;
            }
        }
    }
    sat.add_theory_lemma_with_trail(lits)
}

fn sync_theory_after_propagate<T: Theory>(
    sat: &Solver,
    theory: &mut T,
    theory_levels: &mut usize,
) {
    let dl = sat.decision_level() as usize;
    // The main loop makes at most one decision per iteration and syncs every
    // iteration, so `dl` rises by at most 1 per call: the loop pushes a single
    // level whose `facts.len()` snapshot (see `Theory::push`) belongs to
    // exactly that decision level. If decisions were ever batched, multiple
    // pushes here would snapshot the same `facts.len()` and a later single
    // `pop()` would discard several levels' facts at once, desyncing the theory
    // trail from SAT. Enforce the invariant so such a change fails loudly.
    debug_assert!(
        dl <= *theory_levels + 1,
        "theory push assumes <=1 new decision level per sync (dl={dl}, theory_levels={})",
        *theory_levels
    );
    while *theory_levels < dl {
        theory.push();
        *theory_levels += 1;
    }
}

fn sync_theory_after_backtrack<T: Theory>(
    sat: &Solver,
    theory: &mut T,
    theory_levels: &mut usize,
) {
    let dl = sat.decision_level() as usize;
    while *theory_levels > dl {
        theory.pop();
        *theory_levels -= 1;
    }
}

/// Resync after a lemma forced a backjump: rewind the theory trail to the
/// new decision level and rewind `notified` so the next pass re-notifies
/// from the position the asserting literal now occupies. The three lemma
/// sites (propagation conflict, theory-propagation disagreement, post-check
/// UNSAT) must use the identical rewind formula, so it lives here once.
fn resync_after_lemma<T: Theory>(
    sat: &Solver,
    theory: &mut T,
    theory_levels: &mut usize,
    notified: &mut usize,
    trail_pre_lemma: usize,
) {
    sync_theory_after_backtrack(sat, theory, theory_levels);
    *notified = (*notified).min(trail_pre_lemma).min(sat.trail_len());
}

#[cfg(test)]
#[path = "orchestrator_tests.rs"]
mod tests;
