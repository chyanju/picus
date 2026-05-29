use super::*;
use num_bigint::BigUint;

fn ring(n_vars: usize) -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(101u32));
    let names: Vec<String> = (0..n_vars).map(|i| format!("x{}", i)).collect();
    PolyRing::new(f, names, MonomialOrder::DegRevLex)
}

fn const_p(ring: &Arc<PolyRing>, v: u64) -> DensePoly {
    DensePoly::constant(ring.field.from_u64(v), ring)
}

#[test]
fn gb_unit_ideal() {
    let r = ring(2);
    // {1} generates the whole ring.
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(vec![const_p(&r, 1)], &r, &cfg).unwrap();
    assert_eq!(gb.basis.len(), 1);
    assert!(gb.basis[0].is_constant());
}

#[test]
fn incremental_push_pop() {
    let r = ring(2);
    let f = &r.field;
    let p1 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0]), f.from_i64(-1)),
        ],
        &r,
    );
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let mut igb = IncrementalGB::new(r.clone(), cfg);
    igb.add_generators(vec![p1]).unwrap();
    let basis_pre = igb.basis().len();
    igb.push();
    // Add a strong constraint that makes the system inconsistent: x = 2 AND x^2 = 1
    let xeq2 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![1, 0]), f.from_u64(1)),
            (Monomial::from_exponents(vec![0, 0]), f.from_i64(-2)),
        ],
        &r,
    );
    let trivial = igb.add_generators(vec![xeq2]).unwrap();
    // x=2 + x^2=1  => 4=1 => 3=0 in GF(101) => not trivial. Use x=2 + x^2-2:
    // x^2 - 2 - (x - 2)(x + 2) = -2 + 4 = 2 mod ideal but already x=2 implies x^2 = 4.
    // Actually with x^2 = 1 and x = 2: 4 = 1 (false in chars 101). So GB = {1}.
    assert!(trivial);
    igb.pop();
    // After pop, we should be back to the previous state.
    assert_eq!(igb.basis().len(), basis_pre);
    assert!(!igb.is_trivial());
}

#[test]
fn incremental_pop_restores_rewritten_bodies() {
    // A pre-push element whose body is *rewritten* (not merely deactivated)
    // by `tail_reduce_active` using a post-push element must be rolled back
    // on pop. Here p0 = x0^2 + x2; after pushing and adding x2, the
    // post-push x2 cancels p0's x2 term, rewriting p0's body to x0^2. pop
    // must restore p0 = x0^2 + x2 — so p0 reduces to zero against the popped
    // basis again. With a flags-only pop the popped basis is {x0^2} and p0
    // reduces to x2 != 0.
    let r = ring(3);
    let f = &r.field;
    let p0 = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0, 0]), f.from_u64(1)), // x0^2
            (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(1)), // x2
        ],
        &r,
    );
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let mut igb = IncrementalGB::new(r.clone(), cfg);
    igb.add_generators(vec![p0.clone()]).unwrap();
    let len_pre = igb.basis().len();
    assert!(igb.reduce(&p0).is_zero(), "p0 should lie in the ideal pre-push");

    igb.push();
    let x2 = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(1))], // x2
        &r,
    );
    igb.add_generators(vec![x2]).unwrap();
    igb.pop();

    assert_eq!(igb.basis().len(), len_pre);
    assert!(
        igb.reduce(&p0).is_zero(),
        "pop did not restore the rewritten body: x0^2 + x2 no longer reduces to zero"
    );
}

fn mk_pair(lcm_exps: Vec<u16>, age: u64, is_coprime: bool, ring: &PolyRing) -> SPair {
    let lcm = Monomial::from_exponents(lcm_exps);
    let lcm_divmask = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    SPair {
        i: 0,
        j: 0,
        sugar: lcm_deg,
        lcm,
        lcm_divmask,
        lcm_deg,
        age,
        generation: 0,
        is_coprime,
    }
}

#[test]
fn gm_insert_smaller_lcm_dominates_larger() {
    // (x*y) dominates (x*y*z) since x*y | x*y*z.
    let r = ring(3);
    let mut list: Vec<SPair> = Vec::new();
    gm_insert(&mut list, mk_pair(vec![1, 1, 0], 1, false, &r));
    // Inserting (x*y*z) — should be dominated and dropped.
    gm_insert(&mut list, mk_pair(vec![1, 1, 1], 2, false, &r));
    assert_eq!(list.len(), 1);
    assert_eq!(list[0].lcm.exponents(), &[1, 1, 0]);
}

#[test]
fn gm_insert_larger_lcm_evicted_by_smaller() {
    // Insert (x*y*z) first, then (x*y) — the smaller dominates and evicts.
    let r = ring(3);
    let mut list: Vec<SPair> = Vec::new();
    gm_insert(&mut list, mk_pair(vec![1, 1, 1], 1, false, &r));
    gm_insert(&mut list, mk_pair(vec![1, 1, 0], 2, false, &r));
    assert_eq!(list.len(), 1);
    assert_eq!(list[0].lcm.exponents(), &[1, 1, 0]);
}

#[test]
fn gm_insert_unrelated_lcms_both_kept() {
    // (x*y) and (y*z) are incomparable — both should remain.
    let r = ring(3);
    let mut list: Vec<SPair> = Vec::new();
    gm_insert(&mut list, mk_pair(vec![1, 1, 0], 1, false, &r));
    gm_insert(&mut list, mk_pair(vec![0, 1, 1], 2, false, &r));
    assert_eq!(list.len(), 2);
}

#[test]
fn gm_insert_equal_lcm_prefers_coprime() {
    // Equal LCMs: existing non-coprime, P coprime → existing replaced by P.
    let r = ring(3);
    let mut list: Vec<SPair> = Vec::new();
    gm_insert(&mut list, mk_pair(vec![1, 1, 0], 1, false, &r));
    gm_insert(&mut list, mk_pair(vec![1, 1, 0], 2, true, &r));
    assert_eq!(list.len(), 1);
    // The coprime pair (age=2) should now occupy the slot.
    assert_eq!(list[0].age, 2);
    assert!(list[0].is_coprime);
}

#[test]
fn gm_insert_equal_lcm_keeps_existing_otherwise() {
    // Equal LCMs but coprime conditions don't trigger replacement → P dropped.
    let r = ring(3);
    let mut list: Vec<SPair> = Vec::new();
    gm_insert(&mut list, mk_pair(vec![1, 1, 0], 1, true, &r));
    gm_insert(&mut list, mk_pair(vec![1, 1, 0], 2, false, &r));
    assert_eq!(list.len(), 1);
    assert_eq!(list[0].age, 1);
}

fn mk_basis_elem(lt_exps: Vec<u16>, ring: &PolyRing) -> BasisElement {
    let lt = Monomial::from_exponents(lt_exps);
    let lt_divmask = ring.divmask.compute(&lt);
    BasisElement {
        poly: DensePoly::zero(),
        lt,
        lt_divmask,
        active: true,
        sugar: 0,
        use_count: 0,
    }
}

fn mk_pair_ij(
    i: usize,
    j: usize,
    basis: &[BasisElement],
    ring: &PolyRing,
    age: u64,
) -> SPair {
    let lcm = basis[i].lt.lcm(&basis[j].lt);
    let lcm_divmask = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    SPair {
        i,
        j,
        sugar: lcm_deg,
        lcm,
        lcm_divmask,
        lcm_deg,
        age,
        generation: 0,
        is_coprime: basis[i].lt.is_coprime(&basis[j].lt),
    }
}

#[test]
fn b_criterion_kills_when_all_three_conditions_hold() {
    // basis = [x^2, y^2]; pair (0,1) has lcm = x^2*y^2.
    // new_lt = x*y. Conditions:
    //   1. x*y | x^2*y^2: yes.
    //   2. lcm(y^2, x*y) = x*y^2 ≠ x^2*y^2: holds.
    //   3. lcm(x^2, x*y) = x^2*y ≠ x^2*y^2: holds.
    // → killed.
    let r = ring(3);
    let basis = vec![
        mk_basis_elem(vec![2, 0, 0], &r),
        mk_basis_elem(vec![0, 2, 0], &r),
    ];
    let mut pairs = vec![mk_pair_ij(0, 1, &basis, &r, 1)];
    let new_lt = Monomial::from_exponents(vec![1, 1, 0]);
    let new_lt_dm = r.divmask.compute(&new_lt);
    b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
    assert!(pairs.is_empty(), "pair should have been killed");
}

#[test]
fn b_criterion_keeps_when_new_lt_does_not_divide_lcm() {
    // basis = [x^2, y^2]; lcm = x^2*y^2; new_lt = z (no shared variable).
    // Condition 1 fails: z does not divide x^2*y^2 → keep.
    let r = ring(3);
    let basis = vec![
        mk_basis_elem(vec![2, 0, 0], &r),
        mk_basis_elem(vec![0, 2, 0], &r),
    ];
    let mut pairs = vec![mk_pair_ij(0, 1, &basis, &r, 1)];
    let new_lt = Monomial::from_exponents(vec![0, 0, 1]);
    let new_lt_dm = r.divmask.compute(&new_lt);
    b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
    assert_eq!(pairs.len(), 1, "pair should be kept (cond 1 fails)");
}

#[test]
fn b_criterion_keeps_when_lcm_lt_j_new_equals_lcm() {
    // basis = [x, y]; lcm = x*y; new_lt = x.
    //   1. x | x*y: yes.
    //   2. lcm(LT_j, new_lt) = lcm(y, x) = x*y = pair.lcm → cond 2 fails.
    // → keep.
    let r = ring(3);
    let basis = vec![
        mk_basis_elem(vec![1, 0, 0], &r),
        mk_basis_elem(vec![0, 1, 0], &r),
    ];
    let mut pairs = vec![mk_pair_ij(0, 1, &basis, &r, 1)];
    let new_lt = Monomial::from_exponents(vec![1, 0, 0]);
    let new_lt_dm = r.divmask.compute(&new_lt);
    b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
    assert_eq!(pairs.len(), 1, "pair should be kept (cond 2 fails)");
}

#[test]
fn b_criterion_keeps_when_lcm_lt_i_new_equals_lcm() {
    // basis = [x, y]; lcm = x*y; new_lt = y.
    //   1. y | x*y: yes.
    //   2. lcm(LT_j, new_lt) = lcm(y, y) = y ≠ x*y → cond 2 holds.
    //   3. lcm(LT_i, new_lt) = lcm(x, y) = x*y → cond 3 fails.
    // → keep.
    let r = ring(3);
    let basis = vec![
        mk_basis_elem(vec![1, 0, 0], &r),
        mk_basis_elem(vec![0, 1, 0], &r),
    ];
    let mut pairs = vec![mk_pair_ij(0, 1, &basis, &r, 1)];
    let new_lt = Monomial::from_exponents(vec![0, 1, 0]);
    let new_lt_dm = r.divmask.compute(&new_lt);
    b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
    assert_eq!(pairs.len(), 1, "pair should be kept (cond 3 fails)");
}

#[test]
fn b_criterion_empty_queue_is_noop() {
    let r = ring(3);
    let basis: Vec<BasisElement> = Vec::new();
    let mut pairs: Vec<SPair> = Vec::new();
    let new_lt = Monomial::from_exponents(vec![1, 1, 0]);
    let new_lt_dm = r.divmask.compute(&new_lt);
    b_criterion_kill(&mut pairs, &new_lt, new_lt_dm, &basis);
    assert!(pairs.is_empty());
}

// ────────── public entry points: incremental + interreduce ──────────

fn poly(ring: &Arc<PolyRing>, terms: &[(Vec<u16>, i64)]) -> DensePoly {
    let t: Vec<(Monomial, _)> = terms
        .iter()
        .map(|(e, c)| (Monomial::from_exponents(e.clone()), ring.field.from_i64(*c)))
        .collect();
    DensePoly::from_terms(t, ring)
}

#[test]
fn groebner_basis_incremental_collapses_when_new_gen_divides_existing() {
    // Existing GB = {x0^2 - 1}; add x0 - 1. Since x0^2-1 = (x0-1)(x0+1),
    // the ideal (x0^2-1, x0-1) = (x0-1) ⇒ GB = {x0 - 1}.
    let r = ring(1);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let existing = groebner_basis(vec![poly(&r, &[(vec![2], 1), (vec![0], -1)])], &r, &cfg)
        .unwrap();
    let extended = groebner_basis_incremental(
        existing,
        vec![poly(&r, &[(vec![1], 1), (vec![0], -1)])],
        &r,
        &cfg,
    )
    .unwrap();
    assert_eq!(extended.basis.len(), 1);
    // The single generator is degree-1 (the linear x0 - 1, made monic).
    assert_eq!(extended.basis[0].leading_monomial(&r).unwrap().total_degree(), 1);
}

#[test]
fn interreduce_tail_reduces_with_live_cancel_token() {
    // basis = {x0 + x1, x1}. Tail-reducing x0+x1 by x1 yields x0, so the
    // inter-reduced basis is {x0, x1}. Passing a live (never-firing) token
    // drives the `Some(cancel)` arm of interreduce_with_cancel.
    let r = ring(2);
    let basis = vec![
        poly(&r, &[(vec![1, 0], 1), (vec![0, 1], 1)]), // x0 + x1
        poly(&r, &[(vec![0, 1], 1)]),                  // x1
    ];
    let cancel = crate::timeout::CancelToken::none();
    let reduced = interreduce_with_cancel(basis, &r, Some(&cancel));
    assert_eq!(reduced.len(), 2);
    // Every leading monomial is a single variable to the first power.
    for p in &reduced {
        assert_eq!(p.leading_monomial(&r).unwrap().total_degree(), 1);
    }
}

#[test]
fn interreduce_returns_early_on_pre_cancelled_token() {
    // A pre-cancelled token makes the tail-reduction loop break immediately;
    // the (de-duplicated, monic) basis is still returned as a valid generator
    // set. With two coprime-LT generators no pruning happens, so both survive.
    let r = ring(2);
    let basis = vec![
        poly(&r, &[(vec![1, 0], 1), (vec![0, 1], 1)]), // x0 + x1
        poly(&r, &[(vec![0, 1], 1)]),                  // x1
    ];
    let cancel = crate::timeout::CancelToken::cancelled();
    let reduced = interreduce_with_cancel(basis, &r, Some(&cancel));
    // Both elements are retained (monic); the tail reduction was skipped.
    assert_eq!(reduced.len(), 2);
}

// ────────── F4 path (use_f4 = true) ──────────

#[test]
fn f4_path_matches_per_pair_on_consistent_system() {
    // x0*x1 - 1, x0 - 2 over GF(101): SAT, zero-dimensional. Both engines
    // must agree on the (nontrivial) basis size and triviality.
    let r = ring(2);
    let gens = || vec![
        poly(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]), // x0·x1 - 1
        poly(&r, &[(vec![1, 0], 1), (vec![0, 0], -2)]), // x0 - 2
    ];
    let per_pair = BuchbergerConfig { order: r.order, use_f4: false, ..Default::default() };
    let f4 = BuchbergerConfig { order: r.order, use_f4: true, ..Default::default() };
    let gb_pp = groebner_basis(gens(), &r, &per_pair).unwrap();
    let gb_f4 = groebner_basis(gens(), &r, &f4).unwrap();
    assert!(!gb_pp.basis.iter().any(|p| p.is_constant()));
    assert!(!gb_f4.basis.iter().any(|p| p.is_constant()));
    assert_eq!(gb_pp.basis.len(), gb_f4.basis.len());
}

#[test]
fn f4_path_detects_inconsistent_system() {
    // x0 - 1 and x0 - 2 over GF(101): S-poly reduces to a nonzero constant.
    // The F4 batch must surface the constant and mark the basis trivial.
    let r = ring(1);
    let f4 = BuchbergerConfig { order: r.order, use_f4: true, ..Default::default() };
    let gb = groebner_basis(
        vec![
            poly(&r, &[(vec![1], 1), (vec![0], -1)]),
            poly(&r, &[(vec![1], 1), (vec![0], -2)]),
        ],
        &r,
        &f4,
    )
    .unwrap();
    assert!(gb.basis.iter().any(|p| p.is_constant()),
        "inconsistent system must yield a constant (whole-ring) basis");
}

#[test]
fn f4_path_with_stats_enabled_is_consistent_with_default() {
    // Drives the F4 stats eprintln block; verdict must be unchanged.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let r = ring(2);
    let f4 = BuchbergerConfig { order: r.order, use_f4: true, ..Default::default() };
    let gb = groebner_basis(
        vec![
            poly(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]), // x0·x1 - 1
            poly(&r, &[(vec![1, 0], 1), (vec![0, 0], -2)]), // x0 - 2
        ],
        &r,
        &f4,
    )
    .unwrap();
    assert!(!gb.basis.is_empty());
}

#[test]
fn per_pair_run_cancelled_at_loop_top_with_stats_returns_timeout() {
    // A pre-cancelled token + pending S-pairs: the per-pair run loop hits
    // check_cancel at the top of the first iteration and returns an error.
    // Stats on so the cancellation eprintln branch executes too.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let r = ring(2);
    let cfg = BuchbergerConfig {
        order: r.order,
        use_f4: false,
        cancel_token: Some(crate::timeout::CancelToken::cancelled()),
        ..Default::default()
    };
    // Two generators with non-coprime leading terms ⇒ at least one S-pair.
    let res = groebner_basis(
        vec![
            poly(&r, &[(vec![2, 0], 1), (vec![0, 0], -1)]), // x0^2 - 1
            poly(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]), // x0·x1 - 1
        ],
        &r,
        &cfg,
    );
    assert!(res.is_err(), "pre-cancelled run must return an engine error");
}

#[test]
fn per_pair_run_with_stats_completes_and_emits_telemetry() {
    // Non-F4 run that processes S-pairs to completion with gb_stats on,
    // driving the end-of-run telemetry eprintln. The basis must be the
    // same nontrivial GB the default run produces.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let r = ring(2);
    let cfg = BuchbergerConfig { order: r.order, use_f4: false, ..Default::default() };
    let gb = groebner_basis(
        vec![
            poly(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]), // x0·x1 - 1
            poly(&r, &[(vec![1, 0], 1), (vec![0, 0], -2)]), // x0 - 2
        ],
        &r,
        &cfg,
    )
    .unwrap();
    assert!(!gb.basis.is_empty());
    assert!(!gb.basis.iter().any(|p| p.is_constant()));
}

#[test]
fn per_pair_run_cancelled_mid_run_with_pending_pairs_and_stats() {
    // Drive the per-pair `run` directly with a state whose `open` queue
    // is already populated (built by an uncancelled `add_generators`),
    // then cancel and call `run` with gb-stats on. The loop pops the
    // first pair, the top-of-loop `check_cancel` fires, and the
    // CANCELLED stats block runs before the error is returned.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let r = ring(2);
    let cfg = BuchbergerConfig { order: r.order, use_f4: false, ..Default::default() };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    let mut obs = NoObserver;
    // Non-coprime leading terms (x0^2, x0·x1) ⇒ at least one S-pair.
    state
        .add_generators(
            vec![
                poly(&r, &[(vec![2, 0], 1), (vec![0, 0], -1)]), // x0^2 - 1
                poly(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]), // x0·x1 - 1
            ],
            &mut obs,
        )
        .unwrap();
    let pending_before = state.open.len();
    assert!(pending_before >= 1, "expected pending S-pairs before cancel");
    state.cfg.cancel_token = Some(crate::timeout::CancelToken::cancelled());
    let res = state.run(&mut obs);
    assert!(res.is_err(), "cancelled run must return an engine error");
    // No new basis element was integrated (the first pair was popped but
    // the cancel check fired before its S-poly was reduced).
    assert_eq!(state.basis.len(), 2, "run bailed before adding any generator");
}

// ────────── tail_reduce_active: zero-reduction deactivation + empty-others continue ──────────

#[test]
fn tail_reduce_active_deactivates_element_reduced_to_zero() {
    // Push two identical active elements (both = x0, monic). With ≥ 2
    // active members the reduction loop runs: x0 reduces to zero against
    // the other x0 (the first iteration), so its slot is deactivated on
    // write-back; the second iteration finds its only other entry now
    // zero, so `others` is empty and that index is skipped. The surviving
    // element stays active.
    let r = ring(1);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    let x0 = poly(&r, &[(vec![1], 1)]); // x0
    let lt = x0.leading_monomial(&r).unwrap();
    let lt_divmask = r.divmask.compute(&lt);
    for _ in 0..2 {
        state.basis.push(BasisElement {
            poly: x0.clone(),
            lt: lt.clone(),
            lt_divmask,
            active: true,
            sugar: lt.total_degree(),
            use_count: 0,
        });
    }
    let log = state.tail_reduce_active(false);
    assert!(log.is_empty(), "untracked tail reduction returns no reducer log");
    // Exactly one of the two duplicates remains active.
    assert_eq!(state.basis.iter().filter(|e| e.active).count(), 1);
    assert!(!state.basis[0].active, "first duplicate reduced to zero ⇒ deactivated");
    assert!(state.basis[1].active);
}

// ────────── observer trait defaults (NoObserver) ──────────

#[test]
fn no_observer_default_hooks() {
    // The blanket `BuchbergerObserver for NoObserver` uses the trait
    // default methods: `wants_inter_reduce_deps` is false, and the
    // mutating hooks are no-ops that must not panic.
    let mut obs = NoObserver;
    assert!(!obs.wants_inter_reduce_deps());
    let r = ring(2);
    let p = poly(&r, &[(vec![1, 0], 1)]); // x0
    obs.on_initial_reducers(&[0, 1]);
    obs.on_initial_basis(0, &p);
    obs.on_pair_reducers(&[0]);
    obs.on_new_poly(1, &p, (0, 0));
    obs.on_inter_reduce(0, &[1, 2]);
}

// ────────── interreduce: nonzero tail-reduced make-monic branch ──────────

#[test]
fn interreduce_makes_nonzero_tail_result_monic() {
    // basis = {2·x0 + 2·x1, x1} over GF(101). After dropping zeros and
    // making monic, 2·x0+2·x1 → x0 + x1. Tail-reducing x0+x1 by x1 yields
    // the nonzero x0, exercising the `red.make_monic(ring)` arm. Both
    // surviving elements end up monic and degree-1.
    let r = ring(2);
    let basis = vec![
        poly(&r, &[(vec![1, 0], 2), (vec![0, 1], 2)]), // 2·x0 + 2·x1
        poly(&r, &[(vec![0, 1], 1)]),                  // x1
    ];
    let reduced = interreduce(basis, &r);
    assert_eq!(reduced.len(), 2);
    for p in &reduced {
        assert_eq!(p.leading_monomial(&r).unwrap().total_degree(), 1);
        assert!(r.field.is_one(p.leading_coefficient().unwrap()),
            "every inter-reduced element must be monic");
    }
}

// ────────── BuchbergerState internals ──────────

/// Seed a fresh `BuchbergerState` with `n` distinct single-variable
/// generators x0..x_{n-1}. They are mutually coprime, so none deactivates
/// another and all `n` stay active. `ring` must have >= n variables.
fn seeded_state(ring: &Arc<PolyRing>, n: usize) -> BuchbergerState {
    let cfg = BuchbergerConfig { order: ring.order, ..Default::default() };
    let mut state = BuchbergerState::new(ring.clone(), cfg);
    let gens: Vec<DensePoly> = (0..n).map(|i| DensePoly::variable(i, ring)).collect();
    state.seed_with_reduced_basis(gens);
    state
}

#[test]
fn seed_with_reduced_basis_skips_zero_polys() {
    // A zero poly is silently dropped (continue at the is_zero guard);
    // the nonzero x0^2 is seeded. Resulting basis length is 1.
    let r = ring(1);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    let xsq = poly(&r, &[(vec![2], 1)]); // x0^2
    state.seed_with_reduced_basis(vec![DensePoly::zero(), xsq]);
    assert_eq!(state.basis.len(), 1);
    assert_eq!(state.basis[0].lt.exponents(), &[2]);
    assert!(state.basis[0].active);
}

#[test]
fn add_generators_sorts_by_use_count_at_threshold() {
    // With 32 active basis elements the `active_idxs.len() >= 32` branch
    // sorts the divisor scan by use_count descending before reducing the
    // new generator. Seed 32 single vars, then add a fresh 33rd var: the
    // sort fires and the new (coprime, irreducible) generator is appended.
    let r = ring(33);
    let mut state = seeded_state(&r, USE_COUNT_SORT_THRESHOLD);
    assert_eq!(state.basis.iter().filter(|e| e.active).count(),
        USE_COUNT_SORT_THRESHOLD);
    let mut obs = NoObserver;
    let new_gen = DensePoly::variable(32, &r); // x32, coprime to x0..x31
    state.add_generators(vec![new_gen], &mut obs).unwrap();
    // The fresh variable survives reduction and is added.
    assert_eq!(state.basis.iter().filter(|e| e.active).count(),
        USE_COUNT_SORT_THRESHOLD + 1);
    assert_eq!(state.basis.last().unwrap().lt.exponents()[32], 1);
}

#[test]
fn tail_reduce_active_returns_early_on_precancelled_token() {
    // Two active elements pass the `< 2` guard and enter the reduction
    // loop; a pre-cancelled token makes the first iteration return the
    // (empty) log immediately without rewriting any body.
    let r = ring(2);
    let mut state = seeded_state(&r, 2);
    state.cfg.cancel_token = Some(crate::timeout::CancelToken::cancelled());
    let log = state.tail_reduce_active(false);
    assert!(log.is_empty(), "pre-cancelled tail reduction yields no reducer log");
    // Bodies untouched: both single-var generators remain.
    assert_eq!(state.basis.len(), 2);
}

#[test]
fn tail_reduce_active_tracked_records_reducers() {
    // basis = {x0 + x1, x1}. Tracked tail reduction reduces x0+x1 by x1
    // (x1 divides the x1 tail term) → x0, recording reducer basis index 1
    // for affected basis index 0. x1 is irreducible by x0, so it logs
    // nothing. Expected log = [(0, [1])].
    let r = ring(2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    state.seed_with_reduced_basis(vec![
        poly(&r, &[(vec![1, 0], 1), (vec![0, 1], 1)]), // x0 + x1
        poly(&r, &[(vec![0, 1], 1)]),                  // x1
    ]);
    let log = state.tail_reduce_active(true);
    assert_eq!(log.len(), 1);
    assert_eq!(log[0].0, 0, "affected element is basis index 0 (x0 + x1)");
    assert_eq!(log[0].1, vec![1], "reducer is basis index 1 (x1)");
    // The rewritten body is now x0 (the x1 tail was cancelled), still monic.
    assert_eq!(state.basis[0].poly.leading_monomial(&r).unwrap().exponents(), &[1, 0]);
    assert_eq!(state.basis[0].poly.num_terms(), 1);
}

#[test]
fn reduce_spoly_against_active_cached_index_path() {
    // With reducer_index_cache on and an active basis of 64 (==
    // ReducerIndex::SORT_THRESHOLD), reduce_spoly_against_active builds and
    // caches a ReducerIndex on the first call and reuses it on the second.
    // Reducing x0 + x1 against {x0..x63} fully cancels to zero both times.
    let _g = crate::config::ConfigGuard::with_override(|c| c.reducer_index_cache = true);
    let r = ring(ReducerIndex::SORT_THRESHOLD);
    let mut state = seeded_state(&r, ReducerIndex::SORT_THRESHOLD);
    let s_poly = poly(&r, &{
        let mut e0 = vec![0u16; ReducerIndex::SORT_THRESHOLD];
        e0[0] = 1;
        let mut e1 = vec![0u16; ReducerIndex::SORT_THRESHOLD];
        e1[1] = 1;
        vec![(e0, 1), (e1, 1)] // x0 + x1
    });

    let (nf1, idxs1, _uc1) = state.reduce_spoly_against_active(&s_poly);
    assert!(nf1.is_zero(), "x0 + x1 reduces to zero against {{x0..x63}}");
    assert_eq!(idxs1.len(), ReducerIndex::SORT_THRESHOLD);
    assert!(state.red_index.is_some(), "first call populates the reducer-index cache");

    let (nf2, idxs2, _uc2) = state.reduce_spoly_against_active(&s_poly);
    assert!(nf2.is_zero(), "cached-index reduction agrees with the first call");
    assert_eq!(idxs2, idxs1, "active set unchanged ⇒ same index list (cache reused)");
}

#[test]
fn process_pair_geobucket_sorts_by_use_count_at_threshold() {
    // 32 active single-var elements drives the use_count sort branch in
    // process_pair_geobucket. The pair (0,1) has coprime leading terms
    // (x0, x1), so its S-poly reduces to zero: the method returns Ok and
    // leaves the basis unchanged (no new generator pushed).
    let r = ring(33);
    let mut state = seeded_state(&r, USE_COUNT_SORT_THRESHOLD);
    let len_before = state.basis.len();
    let pair = mk_pair_ij(0, 1, &state.basis, &r, 1);
    let mut obs = NoObserver;
    state.process_pair_geobucket(pair, &mut obs).unwrap();
    assert_eq!(state.basis.len(), len_before,
        "coprime S-poly reduces to zero ⇒ no new basis element");
}

#[test]
fn process_pair_geobucket_with_live_cancel_token_reduces() {
    // A live (never-firing) cancel token drives the `Some(c)` reduction
    // arm and the post-reduction `is_cancelled()` check (which is false).
    // The non-coprime pair on {x0^2, x0·x1} has S-poly that reduces to
    // zero against the basis, returning Ok without growing the basis.
    let r = ring(2);
    let cfg = BuchbergerConfig {
        order: r.order,
        cancel_token: Some(crate::timeout::CancelToken::none()),
        ..Default::default()
    };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    state.seed_with_reduced_basis(vec![
        poly(&r, &[(vec![2, 0], 1)]),       // x0^2
        poly(&r, &[(vec![1, 1], 1)]),       // x0·x1
    ]);
    let len_before = state.basis.len();
    let pair = mk_pair_ij(0, 1, &state.basis, &r, 1);
    let mut obs = NoObserver;
    let res = state.process_pair_geobucket(pair, &mut obs);
    assert!(res.is_ok());
    // S-poly of x0^2 and x0·x1: lcm = x0^2·x1, spoly = x1·x0^2 - x0·(x0·x1)
    //  = 0 ⇒ no new element.
    assert_eq!(state.basis.len(), len_before);
}

#[test]
fn process_pair_geobucket_precancelled_token_returns_timeout() {
    // A pre-cancelled token: the small S-poly reduction completes (the
    // in-loop cancel check is throttled and never fires on a tiny input),
    // but the explicit post-reduction `c.is_cancelled()` check returns the
    // Timeout error.
    let r = ring(2);
    let cfg = BuchbergerConfig {
        order: r.order,
        cancel_token: Some(crate::timeout::CancelToken::cancelled()),
        ..Default::default()
    };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    state.seed_with_reduced_basis(vec![
        poly(&r, &[(vec![2, 0], 1), (vec![0, 0], -1)]), // x0^2 - 1
        poly(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]), // x0·x1 - 1
    ]);
    let pair = mk_pair_ij(0, 1, &state.basis, &r, 1);
    let mut obs = NoObserver;
    let res = state.process_pair_geobucket(pair, &mut obs);
    assert!(matches!(res, Err(crate::EngineError::Timeout)),
        "pre-cancelled token must surface a Timeout error");
}

// ────────── run_f4: generation filtering ──────────

#[test]
fn run_f4_matrix_path_constant_output_continues_when_not_aborting() {
    // Drive run_f4's matrix path (batch ≥ F4_MIN_BATCH = 12) to a constant
    // F4 output and verify the `poly.is_constant()` integration arm with
    // abort_on_trivial = false: the constant is pushed, `trivial` is set,
    // and the loop `continue`s to drain the (now empty) queue.
    //
    // basis = {x0 - 1, x0 - 2}. The pair (0, 1) has lcm = x0; its S-poly is
    // (x0 - 1) - (x0 - 2) = 1 (a nonzero constant). Twelve identical copies
    // of this pair all share sugar = 1, so run_f4 batches all twelve, takes
    // the matrix path, and F4 emits a single constant generator.
    let r = ring(2);
    let cfg = BuchbergerConfig {
        order: r.order,
        use_f4: true,
        abort_on_trivial: false,
        ..Default::default()
    };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    state.seed_with_reduced_basis(vec![
        poly(&r, &[(vec![1, 0], 1), (vec![0, 0], -1)]), // x0 - 1
        poly(&r, &[(vec![1, 0], 1), (vec![0, 0], -2)]), // x0 - 2
    ]);
    // Pre-existing seeding may have generated its own pair; replace the
    // queue with twelve identical (0,1) pairs so the matrix path fires.
    state.open = (0..F4_MIN_BATCH as u64)
        .map(|age| mk_pair_ij(0, 1, &state.basis, &r, age))
        .collect();
    let mut obs = NoObserver;
    state.run_f4(&mut obs).unwrap();
    // The constant entered the basis and the trivial flag is set; because
    // abort_on_trivial is false, run_f4 ran the queue to completion.
    assert!(state.trivial, "constant F4 output must mark the basis trivial");
    assert!(state.basis.iter().any(|e| e.poly.is_constant()),
        "the whole-ring constant must be present in the basis");
    assert!(state.open.is_empty(), "run_f4 must drain the queue");
}

#[test]
fn run_f4_matrix_path_constant_output_aborts_when_requested() {
    // Same matrix-path constant output as the previous test, but with
    // abort_on_trivial = true: after pushing the constant and setting
    // `trivial`, run_f4 returns immediately (the early-return arm).
    let r = ring(2);
    let cfg = BuchbergerConfig {
        order: r.order,
        use_f4: true,
        abort_on_trivial: true,
        ..Default::default()
    };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    state.seed_with_reduced_basis(vec![
        poly(&r, &[(vec![1, 0], 1), (vec![0, 0], -1)]), // x0 - 1
        poly(&r, &[(vec![1, 0], 1), (vec![0, 0], -2)]), // x0 - 2
    ]);
    state.open = (0..F4_MIN_BATCH as u64)
        .map(|age| mk_pair_ij(0, 1, &state.basis, &r, age))
        .collect();
    let mut obs = NoObserver;
    state.run_f4(&mut obs).unwrap();
    assert!(state.trivial, "constant F4 output must mark the basis trivial");
    assert!(state.basis.iter().any(|e| e.poly.is_constant()),
        "the whole-ring constant must be present in the basis");
}

#[test]
fn run_f4_skips_earlier_generation_pairs() {
    // A pending pair tagged with an earlier generation than the state's
    // current generation is dropped (generation filter), leaving the only
    // sugar batch empty so run_f4 continues to the next loop turn and then
    // exits cleanly. The pair's parents are never dereferenced because the
    // generation check precedes build_spoly.
    let r = ring(3);
    let cfg = BuchbergerConfig { order: r.order, use_f4: true, ..Default::default() };
    let mut state = BuchbergerState::new(r.clone(), cfg);
    state.generation = 1;
    // mk_pair builds an SPair at generation 0 (< state.generation = 1).
    state.open = vec![mk_pair(vec![1, 1, 0], 1, false, &r)];
    let mut obs = NoObserver;
    state.run_f4(&mut obs).unwrap();
    // The stale pair was consumed and dropped; nothing was added.
    assert!(state.open.is_empty());
    assert!(state.basis.is_empty());
}

// ══════════════════════════════════════════════════════════════════════════
// SPEC-DRIVEN PROPERTY TESTS
// Each test enforces a *mathematical* property of Buchberger output that is
// independent of the algorithm's internal control flow. A failure here is a
// bug, not a behaviour drift.
//
// References:
//   * Cox, Little, O'Shea, "Ideals, Varieties, and Algorithms",
//     §2.7 (Buchberger characterisation) and §2.8 (Buchberger's criterion).
//   * Becker, Weispfenning, "Gröbner Bases", §5.2 (reduced GB uniqueness).
// ══════════════════════════════════════════════════════════════════════════

/// Build a ring over GF(prime) with `n_vars` variables x0..x_{n-1} in
/// DegRevLex order. Mirrors the file-local `ring(n)` helper but parameterises
/// the prime so the same property can be exercised over GF(2), GF(3),
/// GF(5), GF(7), GF(13), etc.
fn ring_p(prime: u64, n_vars: usize) -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(prime));
    let names: Vec<String> = (0..n_vars).map(|i| format!("x{}", i)).collect();
    PolyRing::new(f, names, MonomialOrder::DegRevLex)
}

fn poly_in(ring: &Arc<PolyRing>, terms: &[(Vec<u16>, i64)]) -> DensePoly {
    let t: Vec<(Monomial, _)> = terms
        .iter()
        .map(|(e, c)| (Monomial::from_exponents(e.clone()), ring.field.from_i64(*c)))
        .collect();
    DensePoly::from_terms(t, ring)
}

// ─── Class 4: ideal membership round-trip ─────────────────────────────────
// Spec (Buchberger characterisation): B is a Gröbner basis of an ideal I iff
// every f ∈ I has normal form 0 modulo B. In particular, every original
// generator g ∈ G reduces to zero against B.

#[test]
fn prop_every_input_generator_reduces_to_zero_against_gb_gf101() {
    let r = ring_p(101, 3);
    let gens = vec![
        poly_in(&r, &[(vec![2, 0, 0], 1), (vec![0, 1, 0], -1)]), // x0^2 - x1
        poly_in(&r, &[(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)]), // x0*x1 - x2
        poly_in(&r, &[(vec![0, 2, 0], 1), (vec![1, 0, 0], -1)]), // x1^2 - x0
    ];
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(gens.clone(), &r, &cfg).unwrap();
    let refs: Vec<&DensePoly> = gb.basis.iter().collect();
    for g in &gens {
        let nf = g.reduce_by_refs(&refs, &r);
        assert!(
            nf.is_zero(),
            "spec: every original generator must reduce to 0 mod GB"
        );
    }
}

#[test]
fn prop_every_input_generator_reduces_to_zero_against_gb_gf7() {
    // Same property over a small prime (GF(7)).
    let r = ring_p(7, 2);
    let gens = vec![
        poly_in(&r, &[(vec![2, 0], 1), (vec![0, 0], -3)]),       // x0^2 - 3
        poly_in(&r, &[(vec![0, 2], 1), (vec![0, 0], -2)]),       // x1^2 - 2
        poly_in(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]),       // x0*x1 - 1
    ];
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(gens.clone(), &r, &cfg).unwrap();
    let refs: Vec<&DensePoly> = gb.basis.iter().collect();
    for g in &gens {
        let nf = g.reduce_by_refs(&refs, &r);
        assert!(nf.is_zero(), "spec: input generator g must reduce to 0 mod GB over GF(7)");
    }
}

#[test]
fn prop_every_input_generator_reduces_to_zero_against_gb_gf13() {
    let r = ring_p(13, 3);
    let gens = vec![
        poly_in(&r, &[(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)]), // x0*x1 - x2
        poly_in(&r, &[(vec![2, 0, 0], 1), (vec![0, 0, 0], -5)]), // x0^2 - 5
        poly_in(&r, &[(vec![0, 2, 0], 1), (vec![0, 0, 0], -8)]), // x1^2 - 8
    ];
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(gens.clone(), &r, &cfg).unwrap();
    let refs: Vec<&DensePoly> = gb.basis.iter().collect();
    for g in &gens {
        let nf = g.reduce_by_refs(&refs, &r);
        assert!(nf.is_zero(), "spec: input generator g must reduce to 0 mod GB over GF(13)");
    }
}

// ─── Class 4: GB is a (reduced) minimal basis — no LT divides another ─────
// Spec: a *reduced* Gröbner basis has the property that for any two distinct
// elements f, g ∈ B, LT(f) does not divide LT(g). picus's Buchberger output
// is finalised through `interreduce` which enforces this; verify it.

#[test]
fn prop_gb_basis_has_no_lt_dividing_another_lt_gf101() {
    let r = ring_p(101, 3);
    let gens = vec![
        poly_in(&r, &[(vec![2, 0, 0], 1), (vec![0, 1, 0], -1)]),
        poly_in(&r, &[(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)]),
        poly_in(&r, &[(vec![0, 2, 0], 1), (vec![1, 0, 0], -1)]),
    ];
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(gens, &r, &cfg).unwrap();
    let lts: Vec<Monomial> = gb
        .basis
        .iter()
        .map(|p| p.leading_monomial(&r).unwrap())
        .collect();
    for i in 0..lts.len() {
        for j in 0..lts.len() {
            if i == j { continue; }
            assert!(
                !lts[i].divides(&lts[j]),
                "spec: in a reduced GB, LT(b_i) must not divide LT(b_j) for i != j"
            );
        }
    }
}

#[test]
fn prop_gb_basis_has_no_lt_dividing_another_lt_gf7() {
    let r = ring_p(7, 2);
    let gens = vec![
        poly_in(&r, &[(vec![2, 0], 1), (vec![0, 1], -1)]),
        poly_in(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]),
        poly_in(&r, &[(vec![0, 2], 1), (vec![1, 0], -1)]),
    ];
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(gens, &r, &cfg).unwrap();
    let lts: Vec<Monomial> = gb
        .basis
        .iter()
        .map(|p| p.leading_monomial(&r).unwrap())
        .collect();
    for i in 0..lts.len() {
        for j in 0..lts.len() {
            if i == j { continue; }
            assert!(
                !lts[i].divides(&lts[j]),
                "spec: in a reduced GB over GF(7), LT(b_i) must not divide LT(b_j)"
            );
        }
    }
}

// ─── Class 4: every element of a reduced GB is monic ──────────────────────
// Spec: the reduced GB has every leading coefficient equal to 1.

#[test]
fn prop_gb_elements_are_monic_gf101() {
    let r = ring_p(101, 2);
    let gens = vec![
        poly_in(&r, &[(vec![2, 0], 5), (vec![0, 1], 3)]),        // 5·x0^2 + 3·x1
        poly_in(&r, &[(vec![1, 1], 7), (vec![0, 0], -2)]),       // 7·x0*x1 - 2
    ];
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(gens, &r, &cfg).unwrap();
    for p in &gb.basis {
        let lc = p.leading_coefficient().unwrap();
        assert!(
            r.field.is_one(lc),
            "spec: every reduced GB element must be monic (lc == 1)"
        );
    }
}

#[test]
fn prop_gb_elements_are_monic_gf13() {
    let r = ring_p(13, 3);
    let gens = vec![
        poly_in(&r, &[(vec![1, 1, 0], 4), (vec![0, 0, 1], -1)]),
        poly_in(&r, &[(vec![2, 0, 0], 7), (vec![0, 0, 0], -5)]),
    ];
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(gens, &r, &cfg).unwrap();
    for p in &gb.basis {
        let lc = p.leading_coefficient().unwrap();
        assert!(r.field.is_one(lc), "spec: every reduced GB element must be monic over GF(13)");
    }
}

// ─── Class 4: empty / zero-only input → empty GB ──────────────────────────
// Spec: I = (0) ⇒ the reduced GB is empty. Also Buchberger(G ∪ {0}) =
// Buchberger(G) since 0 contributes nothing to the ideal.

#[test]
fn prop_empty_input_yields_empty_gb() {
    let r = ring_p(101, 2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(vec![], &r, &cfg).unwrap();
    assert!(gb.basis.is_empty(), "spec: GB of the zero ideal is empty");
}

#[test]
fn prop_all_zero_input_yields_empty_gb() {
    let r = ring_p(7, 2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(
        vec![DensePoly::zero(), DensePoly::zero(), DensePoly::zero()],
        &r,
        &cfg,
    )
    .unwrap();
    assert!(gb.basis.is_empty(), "spec: GB((0,0,0)) = GB((0)) = ∅");
}

// ─── Class 4: GB(G ∪ {0}) equivalent to GB(G) ────────────────────────────
// Spec: adjoining zero polynomials to G does not change the ideal, so the
// reduced GB is identical (same set of polynomials). We compare via the
// stronger property that the two bases generate the same ideal, checked by
// mutual reduction: every element of B1 reduces to 0 against B2 and vice
// versa.

#[test]
fn prop_gb_invariant_under_adjoining_zero_generators_gf101() {
    let r = ring_p(101, 2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let g = vec![
        poly_in(&r, &[(vec![2, 0], 1), (vec![0, 0], -1)]),
        poly_in(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]),
    ];
    let g_with_zero = {
        let mut v = g.clone();
        v.insert(0, DensePoly::zero());
        v.push(DensePoly::zero());
        v
    };
    let b1 = groebner_basis(g, &r, &cfg).unwrap();
    let b2 = groebner_basis(g_with_zero, &r, &cfg).unwrap();
    let r1: Vec<&DensePoly> = b1.basis.iter().collect();
    let r2: Vec<&DensePoly> = b2.basis.iter().collect();
    for p in &b1.basis {
        assert!(p.reduce_by_refs(&r2, &r).is_zero(),
            "spec: b ∈ GB(G) must lie in ideal generated by GB(G ∪ {{0}})");
    }
    for p in &b2.basis {
        assert!(p.reduce_by_refs(&r1, &r).is_zero(),
            "spec: b ∈ GB(G ∪ {{0}}) must lie in ideal generated by GB(G)");
    }
}

// ─── Class 4: inconsistent system → trivial GB ────────────────────────────
// Spec: if 1 ∈ I (e.g. {x - 1, x - 2} ⇒ -1 ∈ I), then GB = {1}.

#[test]
fn prop_inconsistent_linear_system_yields_constant_gb_gf101() {
    let r = ring_p(101, 1);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(
        vec![
            poly_in(&r, &[(vec![1], 1), (vec![0], -1)]), // x - 1
            poly_in(&r, &[(vec![1], 1), (vec![0], -2)]), // x - 2
        ],
        &r,
        &cfg,
    )
    .unwrap();
    assert!(gb.basis.iter().any(|p| p.is_constant()),
        "spec: inconsistent system ⇒ 1 ∈ ideal ⇒ trivial GB");
}

#[test]
fn prop_inconsistent_linear_system_yields_constant_gb_gf7() {
    let r = ring_p(7, 1);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(
        vec![
            poly_in(&r, &[(vec![1], 1), (vec![0], -3)]), // x - 3
            poly_in(&r, &[(vec![1], 1), (vec![0], -5)]), // x - 5  (3 ≠ 5 mod 7)
        ],
        &r,
        &cfg,
    )
    .unwrap();
    assert!(gb.basis.iter().any(|p| p.is_constant()),
        "spec: inconsistent linear system over GF(7) ⇒ trivial GB");
}

// ─── Class 4: nonzero constant in input forces trivial GB ─────────────────
// Spec: a nonzero constant ∈ I forces I = (1) and the reduced GB is {1}.

#[test]
fn prop_nonzero_constant_in_input_forces_trivial_gb_gf101() {
    let r = ring_p(101, 2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(
        vec![
            poly_in(&r, &[(vec![1, 0], 1)]),       // x0
            poly_in(&r, &[(vec![0, 0], 7)]),       // 7
        ],
        &r,
        &cfg,
    )
    .unwrap();
    assert_eq!(gb.basis.len(), 1, "spec: GB containing a unit collapses to {{1}}");
    assert!(gb.basis[0].is_constant());
    let lc = gb.basis[0].leading_coefficient().unwrap();
    assert!(r.field.is_one(lc), "spec: the constant generator must be normalised to 1");
}

// ─── Class 3: interreduce idempotence ─────────────────────────────────────
// Spec: interreduce(interreduce(B)) == interreduce(B) (same multiset of
// polynomials), because a reduced basis is already inter-reduced and monic.

fn poly_eq(a: &DensePoly, b: &DensePoly, ring: &PolyRing) -> bool {
    // a == b iff a - b reduces to 0 with no divisors (i.e. is the zero poly).
    a.sub(b, ring).is_zero()
}

fn bases_equal_as_sets(a: &[DensePoly], b: &[DensePoly], ring: &PolyRing) -> bool {
    if a.len() != b.len() { return false; }
    // O(n²) set equality keyed by polynomial identity (sub == 0).
    let mut used = vec![false; b.len()];
    for p in a {
        let mut hit = None;
        for (j, q) in b.iter().enumerate() {
            if !used[j] && poly_eq(p, q, ring) {
                hit = Some(j);
                break;
            }
        }
        match hit {
            Some(j) => used[j] = true,
            None => return false,
        }
    }
    true
}

#[test]
fn prop_interreduce_is_idempotent_gf101() {
    let r = ring_p(101, 3);
    let basis = vec![
        poly_in(&r, &[(vec![2, 0, 0], 3), (vec![0, 1, 0], -1)]),
        poly_in(&r, &[(vec![1, 1, 0], 2), (vec![0, 0, 1], -1)]),
        poly_in(&r, &[(vec![0, 2, 0], 5), (vec![1, 0, 0], -1)]),
    ];
    let once = interreduce(basis.clone(), &r);
    let twice = interreduce(once.clone(), &r);
    assert!(bases_equal_as_sets(&once, &twice, &r),
        "spec: interreduce ∘ interreduce == interreduce (idempotent)");
}

#[test]
fn prop_interreduce_is_idempotent_gf7() {
    let r = ring_p(7, 2);
    let basis = vec![
        poly_in(&r, &[(vec![2, 0], 1), (vec![0, 1], 1)]),
        poly_in(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]),
        poly_in(&r, &[(vec![0, 1], 1)]),
    ];
    let once = interreduce(basis.clone(), &r);
    let twice = interreduce(once.clone(), &r);
    assert!(bases_equal_as_sets(&once, &twice, &r),
        "spec: interreduce is idempotent over GF(7)");
}

// ─── Class 4: every interreduce output element is monic ───────────────────
// Spec: interreduce's contract makes every surviving element monic.

#[test]
fn prop_interreduce_output_is_monic_gf101() {
    let r = ring_p(101, 2);
    let basis = vec![
        poly_in(&r, &[(vec![2, 0], 4), (vec![0, 1], 5)]),
        poly_in(&r, &[(vec![1, 1], 7), (vec![0, 0], -3)]),
    ];
    let out = interreduce(basis, &r);
    for p in &out {
        let lc = p.leading_coefficient().unwrap();
        assert!(r.field.is_one(lc),
            "spec: interreduce makes every surviving polynomial monic");
    }
}

// ─── Class 4: interreduce output has no LT dividing another LT ────────────
// Spec: as the post-condition of interreduce, leading monomials are pairwise
// non-divisibility-related.

#[test]
fn prop_interreduce_output_has_unique_lt_relations_gf101() {
    let r = ring_p(101, 3);
    let basis = vec![
        poly_in(&r, &[(vec![2, 0, 0], 1)]),
        poly_in(&r, &[(vec![1, 1, 0], 1)]),
        poly_in(&r, &[(vec![0, 2, 0], 1)]),
        poly_in(&r, &[(vec![0, 0, 1], 1)]),
    ];
    let out = interreduce(basis, &r);
    let lts: Vec<Monomial> =
        out.iter().map(|p| p.leading_monomial(&r).unwrap()).collect();
    for i in 0..lts.len() {
        for j in 0..lts.len() {
            if i == j { continue; }
            assert!(
                !lts[i].divides(&lts[j]),
                "spec: post-interreduce, LT_i must not divide LT_j (i≠j)"
            );
        }
    }
}

// ─── Class 4: GB on already-GB input preserves the ideal ─────────────────
// Spec: GB(GB(G)) generates the same ideal as GB(G). Checked via mutual
// reducibility (each side reduces to 0 against the other).

#[test]
fn prop_gb_of_gb_generates_same_ideal_gf101() {
    let r = ring_p(101, 2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let g = vec![
        poly_in(&r, &[(vec![2, 0], 1), (vec![0, 0], -1)]),
        poly_in(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]),
    ];
    let b1 = groebner_basis(g, &r, &cfg).unwrap();
    let b2 = groebner_basis(b1.basis.clone(), &r, &cfg).unwrap();
    let r1: Vec<&DensePoly> = b1.basis.iter().collect();
    let r2: Vec<&DensePoly> = b2.basis.iter().collect();
    for p in &b1.basis {
        assert!(p.reduce_by_refs(&r2, &r).is_zero(),
            "spec: b ∈ GB(G) reduces to 0 against GB(GB(G))");
    }
    for p in &b2.basis {
        assert!(p.reduce_by_refs(&r1, &r).is_zero(),
            "spec: b ∈ GB(GB(G)) reduces to 0 against GB(G)");
    }
}

// ─── Class 4: GB(G) and GB(G ∪ G) generate the same ideal ─────────────────
// Spec: duplicating generators does not change the ideal.

#[test]
fn prop_gb_invariant_under_duplication_gf101() {
    let r = ring_p(101, 2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let g = vec![
        poly_in(&r, &[(vec![2, 0], 1), (vec![0, 1], -1)]),
        poly_in(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)]),
    ];
    let g_dup = {
        let mut v = g.clone();
        v.extend(g.clone());
        v
    };
    let b1 = groebner_basis(g, &r, &cfg).unwrap();
    let b2 = groebner_basis(g_dup, &r, &cfg).unwrap();
    let r1: Vec<&DensePoly> = b1.basis.iter().collect();
    let r2: Vec<&DensePoly> = b2.basis.iter().collect();
    for p in &b1.basis {
        assert!(p.reduce_by_refs(&r2, &r).is_zero(),
            "spec: GB(G) ⊆ ideal(GB(G∪G))");
    }
    for p in &b2.basis {
        assert!(p.reduce_by_refs(&r1, &r).is_zero(),
            "spec: GB(G∪G) ⊆ ideal(GB(G))");
    }
}

// ─── Class 8: determinism ─────────────────────────────────────────────────
// Spec: groebner_basis is a pure function of (generators, ring, config).
// Running it twice on the same input must produce the same basis (same
// number of polynomials and the same set of polynomials).

#[test]
fn prop_groebner_basis_is_deterministic_gf101() {
    let r = ring_p(101, 3);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let g = || vec![
        poly_in(&r, &[(vec![2, 0, 0], 1), (vec![0, 1, 0], -1)]),
        poly_in(&r, &[(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)]),
        poly_in(&r, &[(vec![0, 2, 0], 1), (vec![1, 0, 0], -1)]),
    ];
    let b1 = groebner_basis(g(), &r, &cfg).unwrap();
    let b2 = groebner_basis(g(), &r, &cfg).unwrap();
    assert_eq!(b1.basis.len(), b2.basis.len(), "spec: deterministic GB size");
    assert!(bases_equal_as_sets(&b1.basis, &b2.basis, &r),
        "spec: deterministic GB content (same multiset of polynomials)");
}

#[test]
fn prop_groebner_basis_is_deterministic_gf7() {
    let r = ring_p(7, 2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let g = || vec![
        poly_in(&r, &[(vec![2, 0], 1), (vec![0, 0], -3)]),
        poly_in(&r, &[(vec![0, 2], 1), (vec![0, 0], -2)]),
    ];
    let b1 = groebner_basis(g(), &r, &cfg).unwrap();
    let b2 = groebner_basis(g(), &r, &cfg).unwrap();
    assert!(bases_equal_as_sets(&b1.basis, &b2.basis, &r),
        "spec: deterministic GB content over GF(7)");
}

// ─── Class 9: per-pair engine and F4 engine compute equivalent ideals ────
// Spec: the per-pair Buchberger path and the F4-lite path are two
// implementations of Buchberger's algorithm on the same ideal — their
// output bases must generate the same ideal (mutual reducibility to 0).

#[test]
fn prop_per_pair_and_f4_engines_compute_same_ideal_gf101() {
    let r = ring_p(101, 3);
    let g = || vec![
        poly_in(&r, &[(vec![2, 0, 0], 1), (vec![0, 1, 0], -1)]),
        poly_in(&r, &[(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)]),
        poly_in(&r, &[(vec![0, 2, 0], 1), (vec![1, 0, 0], -1)]),
    ];
    let pp = BuchbergerConfig { order: r.order, use_f4: false, ..Default::default() };
    let f4 = BuchbergerConfig { order: r.order, use_f4: true, ..Default::default() };
    let bp = groebner_basis(g(), &r, &pp).unwrap();
    let bf = groebner_basis(g(), &r, &f4).unwrap();
    let rp: Vec<&DensePoly> = bp.basis.iter().collect();
    let rf: Vec<&DensePoly> = bf.basis.iter().collect();
    for p in &bp.basis {
        assert!(p.reduce_by_refs(&rf, &r).is_zero(),
            "spec: per-pair element must lie in F4 ideal (same ideal)");
    }
    for p in &bf.basis {
        assert!(p.reduce_by_refs(&rp, &r).is_zero(),
            "spec: F4 element must lie in per-pair ideal (same ideal)");
    }
}

// ─── Class 4: groebner_basis_incremental == groebner_basis on union ──────
// Spec: groebner_basis_incremental(GB(G1), G2) generates the same ideal as
// groebner_basis(G1 ∪ G2). We compare via mutual reducibility.

#[test]
fn prop_incremental_gb_matches_full_gb_on_union_gf101() {
    let r = ring_p(101, 2);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let g1 = vec![poly_in(&r, &[(vec![2, 0], 1), (vec![0, 0], -1)])];
    let g2 = vec![poly_in(&r, &[(vec![1, 1], 1), (vec![0, 0], -1)])];
    let b_full = groebner_basis(
        g1.iter().chain(g2.iter()).cloned().collect(),
        &r,
        &cfg,
    )
    .unwrap();
    let b_step1 = groebner_basis(g1, &r, &cfg).unwrap();
    let b_inc = groebner_basis_incremental(b_step1, g2, &r, &cfg).unwrap();
    let rf: Vec<&DensePoly> = b_full.basis.iter().collect();
    let ri: Vec<&DensePoly> = b_inc.basis.iter().collect();
    for p in &b_full.basis {
        assert!(p.reduce_by_refs(&ri, &r).is_zero(),
            "spec: incremental GB ⊇ full GB ideal");
    }
    for p in &b_inc.basis {
        assert!(p.reduce_by_refs(&rf, &r).is_zero(),
            "spec: full GB ⊇ incremental GB ideal");
    }
}

// ─── Class 7: edge primes & shapes ───────────────────────────────────────
// Spec: a single linear monic generator `x - c` is already a Gröbner basis
// of its principal ideal. Buchberger on {x - c} returns a 1-element basis
// (and its sole element reduces every input to 0 — checked above by the
// generic round-trip but reinforced here under tiny rings).

#[test]
fn prop_single_linear_gen_is_already_a_gb_gf2() {
    let r = ring_p(2, 1);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    // x - 1 over GF(2) ≡ x + 1.
    let gb = groebner_basis(
        vec![poly_in(&r, &[(vec![1], 1), (vec![0], -1)])],
        &r,
        &cfg,
    )
    .unwrap();
    assert_eq!(gb.basis.len(), 1, "spec: GB of a principal linear ideal has one element");
    assert!(r.field.is_one(gb.basis[0].leading_coefficient().unwrap()),
        "spec: that element is monic");
}

#[test]
fn prop_single_linear_gen_is_already_a_gb_gf3() {
    let r = ring_p(3, 1);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(
        vec![poly_in(&r, &[(vec![1], 2), (vec![0], -1)])], // 2x - 1
        &r,
        &cfg,
    )
    .unwrap();
    assert_eq!(gb.basis.len(), 1);
    assert!(r.field.is_one(gb.basis[0].leading_coefficient().unwrap()));
}

#[test]
fn prop_single_linear_gen_is_already_a_gb_gf5() {
    let r = ring_p(5, 1);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(
        vec![poly_in(&r, &[(vec![1], 3), (vec![0], -2)])],
        &r,
        &cfg,
    )
    .unwrap();
    assert_eq!(gb.basis.len(), 1);
    assert!(r.field.is_one(gb.basis[0].leading_coefficient().unwrap()));
}

// ─── Class 4 + 7: zero-variable ring ─────────────────────────────────────
// Spec: in a 0-variable polynomial ring k[ ] = k, every nonzero element is a
// unit ⇒ a single nonzero constant generates the whole ring and GB = {1}.

#[test]
fn prop_zero_var_ring_nonzero_constant_yields_unit_ideal_gf7() {
    let r = ring_p(7, 0);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(
        vec![DensePoly::constant(r.field.from_u64(3), &r)], // 3 ≠ 0 mod 7
        &r,
        &cfg,
    )
    .unwrap();
    assert_eq!(gb.basis.len(), 1);
    assert!(gb.basis[0].is_constant());
    assert!(r.field.is_one(gb.basis[0].leading_coefficient().unwrap()),
        "spec: a nonzero constant in k[] generates (1)");
}

// ─── Class 4: ideal-membership consistency on a different prime + shape ──
// Spec stress: triangular system over GF(5). Every input must reduce to 0
// against the GB.

#[test]
fn prop_round_trip_triangular_system_gf5() {
    let r = ring_p(5, 3);
    let gens = vec![
        poly_in(&r, &[(vec![1, 0, 0], 1), (vec![0, 0, 0], -2)]), // x0 - 2
        poly_in(&r, &[(vec![0, 1, 0], 1), (vec![0, 0, 0], -3)]), // x1 - 3
        poly_in(&r, &[(vec![0, 0, 1], 1), (vec![0, 0, 0], -4)]), // x2 - 4
    ];
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gb = groebner_basis(gens.clone(), &r, &cfg).unwrap();
    let refs: Vec<&DensePoly> = gb.basis.iter().collect();
    for g in &gens {
        assert!(g.reduce_by_refs(&refs, &r).is_zero(),
            "spec: triangular linear inputs must reduce to 0 against GB");
    }
    // The triangular linear ideal has 3 generators in its reduced GB.
    assert_eq!(gb.basis.len(), 3, "spec: 3 linearly independent linear gens ⇒ |GB| = 3");
}

// ─── Class 4: interreduce of a constant-containing basis is {1} ──────────
// Spec (from §interreduce docstring math): "If any constant is present,
// the ideal is the whole ring" ⇒ output is the singleton normalised
// constant 1. This is a math identity (any nonzero c is a unit), not a
// source-read.

#[test]
fn prop_interreduce_collapses_basis_with_constant_to_singleton_one_gf101() {
    let r = ring_p(101, 2);
    let basis = vec![
        poly_in(&r, &[(vec![1, 0], 1)]),     // x0
        poly_in(&r, &[(vec![0, 1], 1)]),     // x1
        poly_in(&r, &[(vec![0, 0], 7)]),     // constant 7
    ];
    let out = interreduce(basis, &r);
    assert_eq!(out.len(), 1, "spec: a basis containing a unit collapses to {{1}}");
    assert!(out[0].is_constant());
    assert!(r.field.is_one(out[0].leading_coefficient().unwrap()),
        "spec: the surviving constant is normalised to 1");
}

// ─── Class 4: interreduce drops zero polynomials ─────────────────────────
// Spec: zero is in every ideal, contributes nothing as a generator, and
// `interreduce` documents `basis.retain(|p| !p.is_zero())`. As a *math*
// claim this is: B and B \ {0} generate the same ideal, so the reduced
// representation must not include 0.

#[test]
fn prop_interreduce_drops_zero_polynomials_gf101() {
    let r = ring_p(101, 2);
    let basis = vec![
        DensePoly::zero(),
        poly_in(&r, &[(vec![1, 0], 1)]),     // x0
        DensePoly::zero(),
        poly_in(&r, &[(vec![0, 1], 1)]),     // x1
        DensePoly::zero(),
    ];
    let out = interreduce(basis, &r);
    for p in &out {
        assert!(!p.is_zero(), "spec: interreduce output contains no zero polys");
    }
    // x0 and x1 have coprime leading monomials ⇒ neither divides the other ⇒
    // both survive; the ideal (x0, x1) ⊊ k[x0, x1].
    assert_eq!(out.len(), 2);
}

// ─── Class 4: monomial-LT-only divisibility pruning in interreduce ───────
// Spec: in a reduced basis, equal leading monomials cannot both occur (one
// would divide the other). interreduce's contract de-duplicates equal-LT
// elements.

#[test]
fn prop_interreduce_deduplicates_equal_lts_gf101() {
    let r = ring_p(101, 2);
    // Two copies of x0 — same LT, same poly.
    let basis = vec![
        poly_in(&r, &[(vec![1, 0], 1)]),
        poly_in(&r, &[(vec![1, 0], 1)]),
    ];
    let out = interreduce(basis, &r);
    assert_eq!(out.len(), 1,
        "spec: equal-LT duplicates collapse to a single element in a reduced basis");
}

// ─── Class 4: Buchberger characterisation across primes (combined check) ─
// Spec combiner — for a non-trivial polynomial system, the full GB
// characterisation holds: (a) every generator reduces to 0, AND (b) no LT
// divides another, AND (c) every element is monic. Probing across multiple
// edge primes.

fn assert_gb_characterisation(
    label: &str,
    prime: u64,
    gens_fn: &dyn Fn(&Arc<PolyRing>) -> Vec<DensePoly>,
) {
    let r = ring_p(prime, 3);
    let cfg = BuchbergerConfig { order: r.order, ..Default::default() };
    let gens = gens_fn(&r);
    let gb = groebner_basis(gens.clone(), &r, &cfg).unwrap();
    let refs: Vec<&DensePoly> = gb.basis.iter().collect();
    for g in &gens {
        assert!(g.reduce_by_refs(&refs, &r).is_zero(),
            "{}: input gen must reduce to 0", label);
    }
    let lts: Vec<Monomial> =
        gb.basis.iter().map(|p| p.leading_monomial(&r).unwrap()).collect();
    for i in 0..lts.len() {
        for j in 0..lts.len() {
            if i == j { continue; }
            assert!(!lts[i].divides(&lts[j]),
                "{}: LT_i must not divide LT_j (i≠j)", label);
        }
    }
    for p in &gb.basis {
        assert!(r.field.is_one(p.leading_coefficient().unwrap()),
            "{}: every reduced GB element is monic", label);
    }
}

#[test]
fn prop_gb_characterisation_across_primes() {
    let mk = |r: &Arc<PolyRing>| vec![
        poly_in(r, &[(vec![2, 0, 0], 1), (vec![0, 1, 0], -1)]),
        poly_in(r, &[(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)]),
        poly_in(r, &[(vec![0, 2, 0], 1), (vec![1, 0, 0], -1)]),
    ];
    assert_gb_characterisation("GF(7)",   7,   &mk);
    assert_gb_characterisation("GF(13)",  13,  &mk);
    assert_gb_characterisation("GF(101)", 101, &mk);
    assert_gb_characterisation("GF(257)", 257, &mk);
}
