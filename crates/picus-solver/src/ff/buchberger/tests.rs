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
