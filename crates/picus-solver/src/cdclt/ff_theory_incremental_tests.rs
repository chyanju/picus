use super::*;

use std::collections::BTreeMap;

use num_bigint::BigUint;

use crate::cdclt::atoms::{AtomTable, InternResult};
use crate::cdclt::theory::{CheckOutcome, Theory};
use crate::frontend::encoder::PolyTerm;
use crate::sat::Solver;
use crate::timeout::CancelToken;

fn ensure_var(vn: &mut Vec<String>, name: &str) -> u32 {
    if let Some(i) = vn.iter().position(|n| n == name) {
        return i as u32;
    }
    vn.push(name.to_string());
    (vn.len() - 1) as u32
}

fn t(vn: &mut Vec<String>, coeff: u64, vars: &[&str]) -> PolyTerm {
    let mut counts: BTreeMap<u32, u16> = BTreeMap::new();
    for n in vars {
        let idx = ensure_var(vn, n);
        *counts.entry(idx).or_insert(0) += 1;
    }
    PolyTerm {
        coeff: BigUint::from(coeff),
        vars: counts.into_iter().collect(),
    }
}

fn intern_eq_var(
    tbl: &mut AtomTable,
    sat: &mut Solver,
    vn: &mut Vec<String>,
    var: &str,
    c: u64,
) -> crate::sat::Var {
    let lhs = vec![t(vn, 1, &[var])];
    let rhs = vec![t(vn, c, &[])];
    match tbl.intern_eq(&lhs, &rhs, vn, sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    }
}

#[test]
fn audit_inc_root_conflict_unsat_via_trivial_basis() {
    // Over GF(7): assert (x = 3) ∧ (x = 4). Together they imply 0 = -1,
    // so the IncrementalGB basis reduces to {1} and post_check returns
    // Unsat with both facts in the core.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let v4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 4);
    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.notify_fact(v3, true);
    th.notify_fact(v4, true);
    match th.post_check() {
        CheckOutcome::Unsat { core } => {
            assert!(core.contains(&v3) && core.contains(&v4), "core must include both atoms");
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
    assert!(th.collect_model().is_none(), "no model on UNSAT");
}

#[test]
fn audit_inc_single_eq_is_sat_small_prime() {
    // Over GF(7): a single (x = 3). Basis is non-trivial → SAT (the
    // field-poly injection ensures GF(7)-membership; model extraction
    // deferred — we only assert the verdict shape).
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.notify_fact(v, true);
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("expected SAT, got {:?}", other),
    }
}

#[test]
fn audit_inc_push_pop_restores_basis() {
    // Assert (x=3), push, assert (x=4) → UNSAT, pop, post_check should be
    // SAT again because the contradiction was popped out.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let v4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 4);

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.notify_fact(v3, true);
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("pre-push SAT expected, got {:?}", other),
    }
    th.push();
    th.notify_fact(v4, true);
    match th.post_check() {
        CheckOutcome::Unsat { .. } => {}
        other => panic!("expected UNSAT after second assert, got {:?}", other),
    }
    th.pop();
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("post-pop SAT expected, got {:?}", other),
    }
}

#[test]
fn bug_inc_pop_restores_slot_claims_gf5() {
    // Over GF(5), 2 is a non-residue (squares = {0, 1, 4}), so x^2 = 2 is
    // UNSAT. The sequence push; (x = 0); pop; push; (x^2 = 2) must
    // re-inject the field polynomial x^5 - x for the reclaimed slot;
    // otherwise post_check sees only {x^2 - 2}, judges the basis
    // non-trivial, and (with add_field_polys=true for prime <= 1000)
    // returns Sat for an UNSAT input.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(5u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v_x_eq_0 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 0);
    let lhs = vec![t(&mut vn, 1, &["x", "x"])];
    let rhs = vec![t(&mut vn, 2, &[])];
    let v_x2_eq_2 = match atoms.intern_eq(&lhs, &rhs, &mut vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    };

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.push();
    th.notify_fact(v_x_eq_0, true);
    th.pop();
    th.push();
    th.notify_fact(v_x2_eq_2, true);
    match th.post_check() {
        CheckOutcome::Sat => panic!(
            "x^2 = 2 over GF(5) is UNSAT; post_check returned Sat — slot claim leaked past pop"
        ),
        CheckOutcome::Unsat { .. } | CheckOutcome::Unknown => {}
    }
}

#[test]
fn bug_inc_notify_fact_slot_budget_exhausted_returns_unknown() {
    // max_vars=1 with an atom that mentions two distinct vars forces
    // slot-budget exhaustion in build_atom_polys. notify_fact must NOT
    // push the half-encoded fact onto the trail; post_check must return
    // Unknown (not Sat) because the trail no longer reflects the algebraic
    // state in the IGB.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    // Atom: x + y = 0 (two distinct variable names).
    let lhs = vec![t(&mut vn, 1, &["x"]), t(&mut vn, 1, &["y"])];
    let rhs = vec![t(&mut vn, 0, &[])];
    let atom_var = match atoms.intern_eq(&lhs, &rhs, &mut vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    };

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 1);
    th.notify_fact(atom_var, true);
    match th.post_check() {
        CheckOutcome::Unknown => {}
        other => panic!("expected Unknown under slot-budget exhaustion, got {:?}", other),
    }
}

#[test]
fn bug_inc_notify_fact_unknown_atom_returns_unknown() {
    // Atom var not registered in AtomTable: build_atom_polys returns
    // None, notify_fact sets the degraded flag, post_check returns
    // Unknown rather than the Sat-on-empty-trail short-circuit.
    let cancel = CancelToken::none();
    let atoms = AtomTable::new(BigUint::from(7u32));
    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 16);
    // Var(999) is not in the AtomTable.
    th.notify_fact(crate::sat::Var(999), true);
    match th.post_check() {
        CheckOutcome::Unknown => {}
        other => panic!("expected Unknown for unregistered atom, got {:?}", other),
    }
}

#[test]
fn audit_inc_deep_dfs_amortizes_gb() {
    // Drive a deep push/notify chain over GF(7) and verify the
    // IncrementalGB amortises across decisions. After N push+notify
    // levels followed by N pops + a final post_check, the total
    // useful-reduction count is bounded by the *unique* atoms ever
    // pushed plus their field polynomials; a per-check rebuild would
    // re-process every active pair from scratch at every post_check
    // call (we issue one per level), producing reduction counts
    // proportional to N^2. The bound is therefore a lower bound on
    // amortisation savings — `useful_reductions < 8 * N` is generous
    // enough to be insensitive to interreduce-period changes yet
    // tight enough to flag a regression to non-incremental behaviour.
    let _guard = picus_core::config::ConfigGuard::with_override(|c| {
        c.gb_stats_enabled = true;
    });
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let mut atom_vars: Vec<crate::sat::Var> = Vec::new();
    let n: usize = 5;
    for i in 0..n {
        let var = format!("x{}", i);
        atom_vars.push(intern_eq_var(&mut atoms, &mut sat, &mut vn, &var, i as u64));
    }

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    for &av in &atom_vars {
        th.push();
        th.notify_fact(av, true);
        let _ = th.post_check();
    }
    for _ in 0..n {
        th.pop();
    }
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("post-all-pop empty trail must be Sat, got {:?}", other),
    }

    let stats = th.engine_stats();
    let budget = 8 * (n as u64);
    assert!(
        stats.reductions_useful < budget,
        "expected useful reductions amortised below {} (got {}); a per-check rebuild would scale as N^2",
        budget,
        stats.reductions_useful
    );
}

#[test]
fn audit_inc_small_prime_sat_returns_nonempty_model() {
    // Over GF(7) with `(x = 3) ∧ (y = 5)`, the incremental basis is
    // non-trivial after both notifies; the model-extraction bridge
    // must surface the user-facing bindings `{x: 3, y: 5}` instead of
    // an empty placeholder map.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v_x = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let v_y = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 5);

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.notify_fact(v_x, true);
    th.notify_fact(v_y, true);

    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("expected Sat, got {:?}", other),
    }
    let m = th.collect_model().expect("Sat must produce a model");
    assert_eq!(m.get("x"), Some(&BigUint::from(3u32)));
    assert_eq!(m.get("y"), Some(&BigUint::from(5u32)));
    assert!(
        !m.keys().any(|k| k.starts_with("__slot_") || k.starts_with("__w_")),
        "model must not surface internal placeholder names: {:?}",
        m.keys().collect::<Vec<_>>()
    );
}

#[test]
fn audit_inc_large_prime_pinned_eq_extracts_model_via_bridge() {
    // BN254 scalar prime, single linear assignment `x = 12345`. The
    // model-extraction bridge runs `find_zero_cancel` against a
    // user-namespaced facade ring; the only basis element after
    // notify is `x - 12345`, which `try_extract_full_assignment`
    // resolves directly. Verdict: Sat with `{x: 12345}`. Was
    // previously Unknown (large prime + non-trivial basis ⇒ Unknown
    // hardcoded) before the bridge landed.
    let cancel = CancelToken::none();
    let prime = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap();
    let mut atoms = AtomTable::new(prime.clone());
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v_x = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 12345);

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 16);
    th.notify_fact(v_x, true);
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("large-prime pinned-eq: expected Sat after bridge, got {:?}", other),
    }
    let m = th.collect_model().expect("Sat must produce a model");
    assert_eq!(m.get("x"), Some(&BigUint::from(12345u32)));
}

#[test]
fn audit_inc_propagate_pins_single_var_eq() {
    // Tier-1 propagation: (x = 3) on the trail pins x ↦ 3. A separate
    // multi-variable atom `(x + y = 5)` whose other variable y is
    // unpinned receives no tier-1 propagation (constant evaluation
    // requires every variable pinned), but the tier-2 path solves
    // `1·y + 3 − 5 = 0` ⇒ y = 2 over GF(7) and dispatches polarity
    // against every registered single-variable equality on y:
    // `(y = 5)` becomes False because the derived value is 2, not 5.
    // This is the port of `FfTheory`'s tier1+tier2 propagation
    // against the incremental theory's identical substrate.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v_x_eq_3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let v_y_eq_5 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 5);
    // (x + y = 5) atom.
    let lhs = vec![
        crate::frontend::encoder::PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(ensure_var(&mut vn, "x"), 1u16)],
        },
        crate::frontend::encoder::PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(ensure_var(&mut vn, "y"), 1u16)],
        },
    ];
    let rhs = vec![crate::frontend::encoder::PolyTerm {
        coeff: BigUint::from(5u32),
        vars: Vec::new(),
    }];
    let v_xy_eq_5 = match atoms.intern_eq(&lhs, &rhs, &mut vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    };

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 16);
    th.notify_fact(v_x_eq_3, true);
    th.notify_fact(v_xy_eq_5, true);
    let derived: Vec<_> = th.propagate();
    // Tier-2 derives `(y = 5) ↦ False` from x=3 ∧ x+y=5 (which gives
    // y=2, contradicting the y=5 atom).
    assert!(
        derived.iter().any(|&(v, pol)| v == v_y_eq_5 && !pol),
        "tier-2 must propagate (y = 5) ↦ False, derived: {:?}",
        derived
    );
}

#[test]
fn audit_inc_empty_trail_is_sat() {
    let cancel = CancelToken::none();
    let atoms = AtomTable::new(BigUint::from(7u32));
    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 16);
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("empty trail SAT expected, got {:?}", other),
    }
    let m = th.collect_model().expect("empty model present");
    assert!(m.is_empty());
}
