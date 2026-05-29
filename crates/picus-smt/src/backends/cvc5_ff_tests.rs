use num_bigint::BigUint;

/// Regression for the cvc5 finite-field split-solver soundness bug
/// (cvc5 PR #12457: present in 1.2.0–1.3.3, fixed in 1.3.4). The
/// bitsum overflow check in `BitProp::getBitEqualities` did not
/// require the bitsum's elements to be `{0,1}`, so `2*_0 + _1 = 4`
/// over BN254 — plainly SAT (e.g. `_0=2, _1=0`) — was wrongly
/// reported UNSAT. This drives cvc5 directly and asserts SAT, so it
/// fails if the vendored cvc5 is ever downgraded below the fix.
#[test]
fn bug_cvc5_ff_split_bitsum_overflow_is_sat() {
    let p = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap();
    let p_str = p.to_string();
    let neg2 = (&p - 2u32).to_string();
    let neg1 = (&p - 1u32).to_string();

    let tm = cvc5_ff::TermManager::new();
    let mut solver = cvc5_ff::Solver::new(&tm);
    solver.set_logic("QF_FF");
    let ff = tm.mk_ff_sort(&p_str, 10);
    let x0 = tm.mk_const(ff.clone(), "_0");
    let x1 = tm.mk_const(ff.clone(), "_1");
    let c_neg2 = tm.mk_ff_elem(&neg2, ff.clone(), 10);
    let c_neg1 = tm.mk_ff_elem(&neg1, ff.clone(), 10);
    let c4 = tm.mk_ff_elem("4", ff.clone(), 10);
    let zero = tm.mk_ff_elem("0", ff.clone(), 10);
    // (-2)*_0 + (-1)*_1 + 4 = 0   (i.e. 2*_0 + _1 = 4)
    let t0 = tm.mk_term(cvc5_ff::Kind::FiniteFieldMult, &[c_neg2, x0]);
    let t1 = tm.mk_term(cvc5_ff::Kind::FiniteFieldMult, &[c_neg1, x1]);
    let sum = tm.mk_term(cvc5_ff::Kind::FiniteFieldAdd, &[t0, t1, c4]);
    let eq = tm.mk_term(cvc5_ff::Kind::Equal, &[sum, zero]);
    solver.assert_formula(eq);

    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "cvc5 must return SAT for 2*_0 + _1 = 4 over BN254 (FF split-solver \
             bug, cvc5 PR #12457); got non-SAT — vendored cvc5 regressed below 1.3.4"
    );
}
