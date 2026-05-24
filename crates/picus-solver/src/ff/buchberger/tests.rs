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
