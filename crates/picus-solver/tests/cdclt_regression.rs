//! CDCL(T) vs DNF cross-validation suite.
//!
//! Each test parses an SMT-LIB v2 QF_FF source, runs both
//! `cdclt::solve_formula` and `boolean::solve_boolean_query_dnf` on
//! it, and asserts the two paths return the same verdict and that
//! the verdict matches the test's expected value.
//!
//! Inputs: hand-written Boolean QF_FF patterns + ports of
//! `cvc5/test/regress/cli/regress0/ff` cases compatible with the
//! `smt2::parse_boolean` accepted subset.

use num_bigint::BigUint;
use picus_solver::boolean::solve_boolean_query_dnf;
use picus_solver::cdclt::solve_formula;
use picus_solver::core::SolveOutcome;
use picus_solver::smt2::parse_boolean;
use picus_core::timeout::CancelToken;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn verdict(o: &SolveOutcome) -> Verdict {
    match o {
        SolveOutcome::Sat(_) => Verdict::Sat,
        SolveOutcome::Unsat(_) => Verdict::Unsat,
        SolveOutcome::Unknown => Verdict::Unknown,
    }
}

/// Returns (cdclt_verdict, dnf_verdict). Asserts both paths return
/// the same verdict; panics with a diagnostic if they disagree.
fn cross_validate(name: &str, src: &str, expected: Verdict) -> (Verdict, Verdict) {
    let q = parse_boolean(src).unwrap_or_else(|e| panic!("[{}] parse: {:?}", name, e));
    let cdclt = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    let dnf = solve_boolean_query_dnf(&q, &CancelToken::none());
    let cv = verdict(&cdclt);
    let dv = verdict(&dnf);
    assert_eq!(cv, dv, "[{}] CDCL(T)={:?} DNF={:?}", name, cdclt, dnf);
    assert_eq!(cv, expected, "[{}] expected {:?}, got {:?}", name, expected, cv);
    (cv, dv)
}

// ─────────────────── Hand-crafted Boolean patterns ─────────────────────────

/// `(or (= x 0) (= x 1))`: `rewrite_disjunctive_bit` collapses to
/// `x*x = x`; SAT (x ∈ {0, 1}).
#[test]
fn or_eq_eq_sat_disjunctive_bit_fold() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff0 F)) (= x (as ff1 F))))
"#;
    cross_validate("or_eq_eq_sat_disjunctive_bit_fold", src, Verdict::Sat);
}

/// `(or (= x 5) (= x 6))` SAT — the disjunctive-bit pass does NOT
/// match this (`0`/`1` only); CDCL(T) handles two disjuncts directly.
#[test]
fn or_eq_eq_sat_non_bit_constants() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff5 F)) (= x (as ff6 F))))
"#;
    cross_validate("or_eq_eq_sat_non_bit_constants", src, Verdict::Sat);
}

/// `(or (= x 5) (= x 6)) ∧ (= x 7)` UNSAT — the asserted equality
/// rules out both disjuncts.
#[test]
fn or_eq_eq_unsat_by_extra_eq() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff5 F)) (= x (as ff6 F))))
(assert (= x (as ff7 F)))
"#;
    cross_validate("or_eq_eq_unsat_by_extra_eq", src, Verdict::Unsat);
}

/// Cartesian DNF growth: `and(or(a,b), or(c,d), or(e,f))` — 2³ = 8
/// disjuncts in DNF. SAT because all six branches are independently
/// satisfiable in distinct variables.
#[test]
fn nested_three_ors_sat_dnf_blowup_8() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(assert (or (= b (as ff2 F)) (= b (as ff3 F))))
(assert (or (= c (as ff4 F)) (= c (as ff5 F))))
"#;
    cross_validate("nested_three_ors_sat_dnf_blowup_8", src, Verdict::Sat);
}

/// 5-fold DNF blowup: `and` of 5 `or`s of `=`. 2⁵ = 32 disjuncts in
/// DNF; CDCL(T) discovers a model without enumeration. SAT.
#[test]
fn nested_five_ors_sat_dnf_blowup_32() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(declare-fun d () F)
(declare-fun e () F)
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(assert (or (= b (as ff0 F)) (= b (as ff1 F))))
(assert (or (= c (as ff0 F)) (= c (as ff1 F))))
(assert (or (= d (as ff0 F)) (= d (as ff1 F))))
(assert (or (= e (as ff0 F)) (= e (as ff1 F))))
"#;
    cross_validate("nested_five_ors_sat_dnf_blowup_32", src, Verdict::Sat);
}

/// 5-fold DNF, every disjunct independently UNSAT against an extra
/// constraint pin. `and(or(a=0,a=1), ..., a=7)` UNSAT.
#[test]
fn five_ors_unsat_via_extra_eq() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(assert (or (= b (as ff0 F)) (= b (as ff1 F))))
(assert (or (= c (as ff0 F)) (= c (as ff1 F))))
(assert (= a (as ff7 F)))
"#;
    cross_validate("five_ors_unsat_via_extra_eq", src, Verdict::Unsat);
}

/// `(or (= x 0) (= y 1))`: different variables, no `rewrite_disjunctive_bit`
/// match. SAT.
#[test]
fn disjunctive_bit_different_vars_not_matched() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (or (= x (as ff0 F)) (= y (as ff1 F))))
(assert (= (ff.add x x) (as ff1 F)))
"#;
    cross_validate("disjunctive_bit_different_vars_not_matched", src, Verdict::Sat);
}

/// `(=> (= x 0) (= y 0))` ∧ `(= x 0)` ∧ `(not (= y 0))` UNSAT — a
/// minimal implies-chain conflict.
#[test]
fn implies_chain_unsat_minimal() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff0 F)))
(assert (=> (= x (as ff0 F)) (= y (as ff0 F))))
(assert (not (= y (as ff0 F))))
"#;
    cross_validate("implies_chain_unsat_minimal", src, Verdict::Unsat);
}

/// Disjunctive Boolean structure that requires conflict learning to
/// escape DNF enumeration: `and(or(a,b), or(¬a,c), or(¬b,c), ¬c)` is
/// UNSAT (think of it as the contrapositive of `(a∨b) → c, ¬c`). DNF
/// expands to 8 conjuncts, all individually UNSAT.
#[test]
fn boolean_unsat_via_conflict_chain() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(assert (or (= a (as ff1 F)) (= b (as ff1 F))))
(assert (or (not (= a (as ff1 F))) (= c (as ff1 F))))
(assert (or (not (= b (as ff1 F))) (= c (as ff1 F))))
(assert (not (= c (as ff1 F))))
"#;
    cross_validate("boolean_unsat_via_conflict_chain", src, Verdict::Unsat);
}

/// 7-fold DNF blowup with one branch UNSAT-by-theory. `a` must equal
/// some bit value (7 binary disjunctions), AND `a*a = a` (forces
/// {0,1}), AND `a = 2` makes it UNSAT.
#[test]
fn seven_ors_unsat_theory_conflict() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(declare-fun d () F)
(declare-fun e () F)
(declare-fun f () F)
(declare-fun g () F)
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(assert (or (= b (as ff0 F)) (= b (as ff1 F))))
(assert (or (= c (as ff0 F)) (= c (as ff1 F))))
(assert (or (= d (as ff0 F)) (= d (as ff1 F))))
(assert (or (= e (as ff0 F)) (= e (as ff1 F))))
(assert (or (= f (as ff0 F)) (= f (as ff1 F))))
(assert (or (= g (as ff0 F)) (= g (as ff1 F))))
(assert (= a (as ff2 F)))
"#;
    cross_validate("seven_ors_unsat_theory_conflict", src, Verdict::Unsat);
}

/// Assertion-level `ite` cycles through both branches at the SAT level.
/// `(ite (= c 1) (= x 0) (= x 1))` with `c=1` → x=0; with `c=0` → x=1.
#[test]
fn assertion_level_ite_sat() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun c () F)
(declare-fun x () F)
(assert (ite (= c (as ff1 F)) (= x (as ff0 F)) (= x (as ff1 F))))
"#;
    cross_validate("assertion_level_ite_sat", src, Verdict::Sat);
}

/// `ite` UNSAT: `c=1` ∧ ite(c=1, x=0, x=1) ∧ x=5 ⇒ UNSAT.
#[test]
fn assertion_level_ite_unsat() {
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun c () F)
(declare-fun x () F)
(assert (= c (as ff1 F)))
(assert (ite (= c (as ff1 F)) (= x (as ff0 F)) (= x (as ff1 F))))
(assert (= x (as ff5 F)))
"#;
    cross_validate("assertion_level_ite_unsat", src, Verdict::Unsat);
}

// ─────────────── Ports of cvc5 regress0/ff tests (Boolean-light) ───────────

/// Port of `regress0/ff/negneg.smt2`: `¬(¬(¬x) = x)` over GF(17) is
/// UNSAT (double negation is the identity in any field).
#[test]
fn cvc5_negneg_unsat() {
    let src = r#"
(define-sort F () (_ FiniteField 17))
(declare-fun x () F)
(assert (not (= (ff.neg (ff.neg x)) x)))
"#;
    cross_validate("cvc5_negneg_unsat", src, Verdict::Unsat);
}

/// Port of `regress0/ff/univar_conjunction_sat.smt2`: x*x = x and
/// x ≠ 1 and x ≠ 2 over GF(17); x = 0 satisfies. SAT.
#[test]
fn cvc5_univar_conjunction_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 17))
(assert (= (ff.mul x x) x))
(assert (not (= x #f1m17)))
(assert (not (= x #f2m17)))
"#;
    cross_validate("cvc5_univar_conjunction_sat", src, Verdict::Sat);
}

/// Port of `regress0/ff/univar_conjunction_unsat.smt2`: x*x = x and
/// x ≠ 1 and x ≠ 0 over GF(17); UNSAT.
#[test]
fn cvc5_univar_conjunction_unsat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 17))
(assert (= (ff.mul x x) x))
(assert (not (= x #f1m17)))
(assert (not (= x #f0m17)))
"#;
    cross_validate("cvc5_univar_conjunction_unsat", src, Verdict::Unsat);
}

/// Port of `regress0/ff/elim_disjunctive_bit_constraints.smt2`: the
/// disjunctive-bit pass must NOT collapse `(or (= x 0) (= y 1))`
/// because the OR branches constrain different variables.
#[test]
fn cvc5_elim_disjunctive_bit_constraints() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 3))
(declare-fun y () (_ FiniteField 3))
(assert (or (= x #f0m3) (= y #f1m3)))
(assert (= (ff.add x x) #f1m3))
"#;
    cross_validate("cvc5_elim_disjunctive_bit_constraints", src, Verdict::Sat);
}

/// Port of `regress0/ff/issue10937.smt2` (MAC linearity bug). UNSAT.
#[test]
fn cvc5_issue10937_unsat() {
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 7))
(declare-const mac1 F)
(declare-const mac2 F)
(declare-const m1 F)
(declare-const m2 F)
(declare-const k1 F)
(declare-const k2 F)
(declare-const d F)
(assert (= mac1 (ff.add k1 (ff.mul d m1))))
(assert (= mac2 (ff.add k2 (ff.mul d m2))))
(assert (not (= (ff.add mac1 mac2)
                (ff.add k1 k2 (ff.mul d (ff.add m1 m2))))))
"#;
    cross_validate("cvc5_issue10937_unsat", src, Verdict::Unsat);
}

// ─── cvc5 ports requiring Bool decl / term-level ite / xor / define-fun ───

/// Port of `regress0/ff/simple.smt2` / `bool_nary_or_sound.smt2`: the
/// Boolean OR is encoded as the FF sum of bit-valued ites being
/// non-zero; the assertion negates the equivalence between the two
/// formulations and the result is UNSAT.
#[test]
fn cvc5_bool_nary_or_sound_unsat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun __ff () (_ FiniteField 5))
(assert (not (=
  (or a b c)
  (not (= (ff.add
    (ite a #f1m5 #f0m5)
    (ite b #f1m5 #f0m5)
    (ite c #f1m5 #f0m5)
  ) #f0m5))
)))
"#;
    cross_validate_agreement("cvc5_bool_nary_or_sound_unsat", src);
}

/// Port of `regress0/ff/ff_is_zero_sound.smt2`: the standard is-zero
/// trick `(m*x + (p-1) + is_zero = 0) ∧ (is_zero*x = 0)` implies
/// `is_zero ∈ {0, 1}` and `is_zero = 1 ⇔ x = 0`. UNSAT to negate.
#[test]
fn cvc5_ff_is_zero_sound_unsat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 17))
(declare-fun m () (_ FiniteField 17))
(declare-fun is_zero () (_ FiniteField 17))
(assert (not (=>
  (and (= #f0m17 (ff.add (ff.mul m x) #f16m17 is_zero))
       (= #f0m17 (ff.mul is_zero x)))
  (and (or (= #f0m17 is_zero) (= #f1m17 is_zero))
       (= (= #f1m17 is_zero) (= x #f0m17)))
)))
"#;
    cross_validate_agreement("cvc5_ff_is_zero_sound_unsat", src);
}

/// Port of `regress0/ff/ff_is_zero_unsound.smt2`: same shape as the
/// sound case but `is_zero*m = 0` (instead of `is_zero*x = 0`). The
/// (broken) constraint set does NOT imply the conclusion, so the
/// negation is SAT.
#[test]
fn cvc5_ff_is_zero_unsound_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 17))
(declare-fun m () (_ FiniteField 17))
(declare-fun is_zero () (_ FiniteField 17))
(assert (not (=>
  (and (= #f0m17 (ff.add (ff.mul m x) #f16m17 is_zero))
       (= #f0m17 (ff.mul is_zero m)))
  (and (or (= #f0m17 is_zero) (= #f1m17 is_zero))
       (= (= #f1m17 is_zero) (= x #f0m17)))
)))
"#;
    cross_validate_agreement("cvc5_ff_is_zero_unsound_sat", src);
}

/// Term-level ite with FF branches inside a top-level equality. SAT
/// when c can be set to pick the branch that matches the RHS.
#[test]
fn cvc5_ite_term_level_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun c () Bool)
(declare-fun x () (_ FiniteField 101))
(assert (= (ite c x #f0m101) #f5m101))
(check-sat)
"#;
    cross_validate_agreement("cvc5_ite_term_level_sat", src);
}

/// `define-fun` macro inlined inside `(assert ...)`.
#[test]
fn cvc5_define_fun_double_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 13))
(define-fun double ((y (_ FiniteField 13))) (_ FiniteField 13) (ff.add y y))
(assert (= (double x) #f4m13))
"#;
    cross_validate_agreement("cvc5_define_fun_double_sat", src);
}

/// n-ary `=` chain forcing `x = y = z = constant`.
#[test]
fn cvc5_nary_equality_chain_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(declare-fun y () (_ FiniteField 7))
(declare-fun z () (_ FiniteField 7))
(assert (= x y z #f3m7))
"#;
    cross_validate_agreement("cvc5_nary_equality_chain_sat", src);
}

/// `distinct` over three FF variables; SAT if the field is large enough.
#[test]
fn cvc5_distinct_three_ff_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 11))
(declare-fun y () (_ FiniteField 11))
(declare-fun z () (_ FiniteField 11))
(assert (distinct x y z))
"#;
    cross_validate_agreement("cvc5_distinct_three_ff_sat", src);
}

/// `xor` over two Bool variables; SAT by setting one True one False.
#[test]
fn cvc5_xor_two_bools_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun __ff () (_ FiniteField 3))
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (xor a b))
"#;
    cross_validate_agreement("cvc5_xor_two_bools_sat", src);
}

/// `xor` of an even number of forced-True Bool vars: UNSAT.
#[test]
fn cvc5_xor_four_true_unsat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun __ff () (_ FiniteField 3))
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert a) (assert b) (assert c) (assert d)
(assert (xor a b c d))
"#;
    cross_validate_agreement("cvc5_xor_four_true_unsat", src);
}

// ─── Further cvc5 ports unlocked by `ff-N` constants and `ff.bitsum` ───

/// Port of `regress0/ff/as.smt2`: `(= ff0 (ff.add ff1 (ff.neg ff1)))`,
/// SAT trivially.
#[test]
fn cvc5_as_sat() {
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 17))
(assert (= (as ff0 F) (ff.add (as ff1 F) (ff.neg (as ff1 F)))))
"#;
    cross_validate_agreement("cvc5_as_sat", src);
}

/// Port of `regress0/ff/field_poly.smt2`: `(a - 0)(a - 1)(a - 2) = 1`
/// over GF(3); by Lagrange / Fermat the LHS is always 0, contradicting
/// `= 1` ⇒ UNSAT.
#[test]
fn cvc5_field_poly_unsat() {
    let src = r#"
(set-logic QF_FF)
(define-sort F3 () (_ FiniteField 3))
(declare-fun a () F3)
(assert (= (ff.mul
    (ff.add a (ff.neg (as ff0 F3)))
    (ff.add a (ff.neg (as ff1 F3)))
    (ff.add a (ff.neg (as ff2 F3)))
    ) (as ff1 F3)))
"#;
    cross_validate_agreement("cvc5_field_poly_unsat", src);
}

/// Port of `regress0/ff/issue11107.smt2`: Bool variables `pre`/`suf`
/// each defined by iff with FF equalities; assert both true. SAT.
#[test]
fn cvc5_issue11107_sat() {
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 7))
(declare-fun a () F)
(declare-fun c () F)
(declare-fun pre () Bool)
(declare-fun suf () Bool)
(assert (= pre (= c (ff.add a (as ff1 F)))))
(assert (= suf (= (ff.mul (as ff6 F) a) (ff.add (ff.mul (as ff6 F) c) (as ff1 F)))))
(assert (and pre suf))
"#;
    cross_validate_agreement("cvc5_issue11107_sat", src);
}

/// Port of `regress0/ff/issue12627.smt2`: `(a * b = b * a)` over GF(3),
/// SAT (commutativity is trivial in any field).
#[test]
fn cvc5_issue12627_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-const a (_ FiniteField 3))
(declare-const b (_ FiniteField 3))
(assert (= (ff.mul a b) (ff.mul b a)))
"#;
    cross_validate_agreement("cvc5_issue12627_sat", src);
}

/// Port of `regress0/ff/issue11969.smt2`: `v = v² + (−1)` over GF(3)
/// has solutions v=1 and v=2; SAT.
#[test]
fn cvc5_issue11969_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-const v (_ FiniteField 3))
(assert (= v (ff.bitsum (ff.mul v v) (as ff-1 (_ FiniteField 3)))))
"#;
    cross_validate_agreement("cvc5_issue11969_sat", src);
}

/// Port of `regress0/ff/bitsum_eval.smt2`: a battery of `ff.bitsum`
/// constant evaluations; all assertions hold ⇒ SAT.
#[test]
fn cvc5_bitsum_eval_sat() {
    let src = r#"
(set-logic QF_FF)
(assert (= (ff.bitsum #f0m3 #f0m3 #f0m3) #f0m3))
(assert (= (ff.bitsum #f1m3 #f0m3 #f0m3) #f1m3))
(assert (= (ff.bitsum #f0m3 #f1m3 #f0m3) #f2m3))
(assert (= (ff.bitsum #f0m3 #f0m3 #f1m3) #f1m3))
(assert (= (ff.bitsum #f0m3 #f1m3 #f1m3) #f0m3))
(assert (= (ff.bitsum #f1m3 #f2m3 #f0m3) #f2m3))
"#;
    cross_validate_agreement("cvc5_bitsum_eval_sat", src);
}

/// Port of `regress0/ff/rewriter.smt2`: many constant-folding sub-cases
/// inside a single OR; each sub-clause is independently False under the
/// FF semantics ⇒ disjunction is False ⇒ assertion False ⇒ UNSAT.
#[test]
fn cvc5_rewriter_unsat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 5))
(assert (or
  (= #f2m5 #f1m5)
  (not (= #f1m5 #f1m5))
  (not (= (ff.neg #f1m5) #f4m5))
  (not (= (ff.add #f0m5 #f1m5 #f2m5 #f3m5) #f1m5))
  (not (= (ff.add #f0m5 (ff.neg x) x) #f0m5))
  (not (= (ff.add #f0m5 (ff.mul #f4m5 x) x) #f0m5))
  (= (ff.mul #f0m5 #f1m5 #f2m5 #f3m5) #f1m5)
  (= (ff.mul #f0m5 #f1m5 x #f3m5) #f1m5)
  (not (= (ff.mul #f1m5 #f2m5 #f3m5) #f1m5))
  (not (= (ff.mul x #f3m5) (ff.add x x x)))
  (not (= (ff.mul x x #f3m5) (ff.add (ff.mul x x) (ff.mul #f2m5 x x))))
))
"#;
    cross_validate_agreement("cvc5_rewriter_unsat", src);
}

/// Port of `regress0/ff/ff_xor_sound.smt2`: 4 bit inputs `f_i` summing
/// to `sum`, plus a 3-bit decomposition `d_i` of `sum`. Premise + bit
/// constraints imply `d0 ≠ 0 ⇔ xor(f_i ≠ 0)`; the negation is UNSAT.
#[test]
fn cvc5_ff_xor_sound_unsat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun f0 () (_ FiniteField 11))
(declare-fun f1 () (_ FiniteField 11))
(declare-fun f2 () (_ FiniteField 11))
(declare-fun f3 () (_ FiniteField 11))
(declare-fun sum () (_ FiniteField 11))
(declare-fun d0 () (_ FiniteField 11))
(declare-fun d1 () (_ FiniteField 11))
(declare-fun d2 () (_ FiniteField 11))
(define-fun f_to_b ((f (_ FiniteField 11))) Bool (not (= f #f0m11)))
(define-fun is_bit ((f (_ FiniteField 11))) Bool (or (= f #f0m11) (= f #f1m11)))
(assert (not (=>
  (and (is_bit f0)
       (is_bit f1)
       (is_bit f2)
       (is_bit f3)
       (= (ff.add f0 f1 f2 f3) sum)
       (= (ff.add d0 (ff.mul #f2m11 d1) (ff.mul #f4m11 d2)) sum)
       (is_bit d0)
       (is_bit d1)
       (is_bit d2))
  (= (f_to_b d0) (xor (f_to_b f0) (f_to_b f1) (f_to_b f2) (f_to_b f3)))
)))
"#;
    cross_validate_agreement("cvc5_ff_xor_sound_unsat", src);
}

/// Port of `regress0/ff/bool_nary_or_unsound.smt2`: a *broken* encoding
/// of n-ary OR via FF bit decomposition over GF(5) — the field is too
/// small to safely sum 5 bits, so the equivalence fails ⇒ SAT.
#[test]
fn cvc5_bool_nary_or_unsound_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun __ff () (_ FiniteField 5))
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(assert (not (=
  (or a b c d e)
  (not (= (ff.add
    (ite a #f1m5 #f0m5)
    (ite b #f1m5 #f0m5)
    (ite c #f1m5 #f0m5)
    (ite d #f1m5 #f0m5)
    (ite e #f1m5 #f0m5)
  ) #f0m5))
)))
"#;
    cross_validate_agreement("cvc5_bool_nary_or_unsound_sat", src);
}

/// Port of `regress0/ff/simple.smt2`: Bool/FF bridging via term-level
/// ite — `(or a b c) ⇔ (sum of bool-as-FF ≠ 0)`. UNSAT (the equivalence
/// holds for GF(5) when the sum can't overflow with only 3 bits).
#[test]
fn cvc5_simple_unsat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (not (=
  (or a b c)
  (not (= (ff.add
    (ite a #f1m5 #f0m5)
    (ite b #f1m5 #f0m5)
    (ite c #f1m5 #f0m5)
  ) #f0m5
  ))
)))
"#;
    cross_validate_agreement("cvc5_simple_unsat", src);
}

/// Port of `regress0/ff/xor_unsound_missing.smt2`: same xor compilation
/// strategy as `ff_xor_sound`, but with `is_bit d2` removed from the
/// premise — without that constraint the encoding is unsound, so the
/// negation is SAT.
#[test]
fn cvc5_xor_unsound_missing_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun f0 () (_ FiniteField 11))
(declare-fun f1 () (_ FiniteField 11))
(declare-fun f2 () (_ FiniteField 11))
(declare-fun f3 () (_ FiniteField 11))
(declare-fun sum () (_ FiniteField 11))
(declare-fun d0 () (_ FiniteField 11))
(declare-fun d1 () (_ FiniteField 11))
(declare-fun d2 () (_ FiniteField 11))
(define-fun f_to_b ((f (_ FiniteField 11))) Bool (not (= f #f0m11)))
(define-fun is_bit ((f (_ FiniteField 11))) Bool (or (= f #f0m11) (= f #f1m11)))
(assert (not (=>
  (and (is_bit f0)
       (is_bit f1)
       (is_bit f2)
       (is_bit f3)
       (= (ff.add f0 f1 f2 f3) sum)
       (= (ff.add d0 (ff.mul #f2m11 d1) (ff.mul #f4m11 d2)) sum)
       (is_bit d0)
       (is_bit d1))
  (= (f_to_b d0) (xor (f_to_b f0) (f_to_b f1) (f_to_b f2) (f_to_b f3)))
)))
"#;
    cross_validate_agreement("cvc5_xor_unsound_missing_sat", src);
}

/// Port of `regress0/ff/ff_xor_unsound.smt2`: same xor encoding as
/// `ff_xor_sound` but over GF(5) — the 4-bit sum can overflow the
/// 3-bit decomposition, so the equivalence fails ⇒ SAT.
#[test]
fn cvc5_ff_xor_unsound_sat() {
    let src = r#"
(set-logic QF_FF)
(declare-fun f0 () (_ FiniteField 5))
(declare-fun f1 () (_ FiniteField 5))
(declare-fun f2 () (_ FiniteField 5))
(declare-fun f3 () (_ FiniteField 5))
(declare-fun sum () (_ FiniteField 5))
(declare-fun d0 () (_ FiniteField 5))
(declare-fun d1 () (_ FiniteField 5))
(declare-fun d2 () (_ FiniteField 5))
(define-fun f_to_b ((f (_ FiniteField 5))) Bool (not (= f #f0m5)))
(define-fun is_bit ((f (_ FiniteField 5))) Bool (or (= f #f0m5) (= f #f1m5)))
(assert (not (=>
  (and (is_bit f0)
       (is_bit f1)
       (is_bit f2)
       (is_bit f3)
       (= (ff.add f0 f1 f2 f3) sum)
       (= (ff.add d0 (ff.mul #f2m5 d1) (ff.mul #f4m5 d2)) sum)
       (is_bit d0)
       (is_bit d1)
       (is_bit d2))
  (= (f_to_b d0) (xor (f_to_b f0) (f_to_b f1) (f_to_b f2) (f_to_b f3)))
)))
"#;
    cross_validate_agreement("cvc5_ff_xor_unsound_sat", src);
}

// ──────────────── Programmatic shape matrix (parameter sweeps) ─────────────

use picus_solver::bench_fixtures::{
    and_of_ors_sat as build_and_of_ors_sat, and_of_ors_unsat as build_and_of_ors_unsat,
    bit_sum as build_bit_sum, conjunction as build_conjunction, disj_bit as build_disj_bit_n,
    implies_chain_unsat as build_implies_chain_unsat, or_of_ands as build_or_of_ands,
    single_or as build_single_or, HEADER_P101,
};

fn build_nested_not_and(n: usize) -> String {
    // `(not (and (= a_0 ff0) … (= a_{n-1} ff0)))`: SAT (any a_i ≠ 0).
    let mut s = String::from(HEADER_P101);
    for i in 0..n {
        s.push_str(&format!("(declare-fun a{} () F)\n", i));
    }
    s.push_str("(assert (not (and");
    for i in 0..n {
        s.push_str(&format!(" (= a{} (as ff0 F))", i));
    }
    s.push_str(")))\n");
    s
}

fn build_ite_chain(depth: usize, target: u64) -> String {
    // depth-d nested ite at the assertion level:
    //   (ite (= c_0 1) (= y 0) (ite (= c_1 1) (= y 1) (ite ... (= y depth))))
    // plus a final `(= y target)` constraint. SAT when one of the
    // ite-induced equalities matches `target`.
    let mut s = String::from(HEADER_P101);
    s.push_str("(declare-fun y () F)\n");
    for i in 0..depth {
        s.push_str(&format!("(declare-fun c{} () F)\n", i));
    }
    let mut ite = format!("(= y (as ff{} F))", depth.min(100));
    for i in (0..depth).rev() {
        ite = format!(
            "(ite (= c{} (as ff1 F)) (= y (as ff{} F)) {})",
            i,
            i.min(100),
            ite
        );
    }
    s.push_str(&format!("(assert {})\n", ite));
    s.push_str(&format!("(assert (= y (as ff{} F)))\n", target));
    s
}

// Matrix tests use small sweep ranges to keep `cargo test` fast.
// Larger sizes are exercised by the `cdclt_bench` Criterion suite
// where multi-second iterations are acceptable.

#[test]
fn matrix_conjunction() {
    for n in [1usize, 3, 6] {
        cross_validate(
            &format!("conjunction_n={}", n),
            &build_conjunction(n),
            Verdict::Sat,
        );
    }
}

#[test]
fn matrix_single_or_sat() {
    for k in [2usize, 4, 8] {
        cross_validate(
            &format!("single_or_k={}", k),
            &build_single_or(k),
            Verdict::Sat,
        );
    }
}

#[test]
fn matrix_disj_bit_sat() {
    for n in [1usize, 4, 8] {
        cross_validate(
            &format!("disj_bit_n={}", n),
            &build_disj_bit_n(n),
            Verdict::Sat,
        );
    }
}

#[test]
fn matrix_and_of_ors_sat() {
    for n in [3usize, 5, 7] {
        cross_validate(
            &format!("and_of_ors_sat_n={}_dnf={}", n, 1usize << n),
            &build_and_of_ors_sat(n),
            Verdict::Sat,
        );
    }
}

#[test]
fn matrix_and_of_ors_unsat() {
    for n in [3usize, 5, 7] {
        cross_validate(
            &format!("and_of_ors_unsat_n={}_dnf={}", n, 1usize << n),
            &build_and_of_ors_unsat(n),
            Verdict::Unsat,
        );
    }
}

#[test]
fn matrix_implies_chain_unsat() {
    for depth in [1usize, 3, 6] {
        cross_validate(
            &format!("implies_chain_unsat_depth={}", depth),
            &build_implies_chain_unsat(depth),
            Verdict::Unsat,
        );
    }
}

#[test]
fn matrix_bit_sum_sat() {
    for &(n, target) in &[(3usize, 0u64), (3, 2), (4, 2), (4, 4), (6, 3)] {
        cross_validate(
            &format!("bit_sum_sat_n={}_t={}", n, target),
            &build_bit_sum(n, target),
            Verdict::Sat,
        );
    }
}

#[test]
fn matrix_bit_sum_unsat() {
    for &(n, target) in &[(3usize, 4u64), (3, 50), (4, 5), (4, 50), (6, 7)] {
        cross_validate(
            &format!("bit_sum_unsat_n={}_t={}", n, target),
            &build_bit_sum(n, target),
            Verdict::Unsat,
        );
    }
}

#[test]
fn matrix_or_of_ands_sat() {
    for n in [1usize, 2, 4] {
        cross_validate(
            &format!("or_of_ands_sat_n={}", n),
            &build_or_of_ands(n),
            Verdict::Sat,
        );
    }
}

#[test]
fn matrix_nested_not_and_sat() {
    for n in [1usize, 3, 6] {
        cross_validate(
            &format!("nested_not_and_sat_n={}", n),
            &build_nested_not_and(n),
            Verdict::Sat,
        );
    }
}

#[test]
fn matrix_ite_chain_sat() {
    for &(depth, target) in &[(1usize, 0u64), (3, 2)] {
        cross_validate(
            &format!("ite_chain_sat_depth={}_t={}", depth, target),
            &build_ite_chain(depth, target),
            Verdict::Sat,
        );
    }
}

#[test]
fn matrix_ite_chain_unsat() {
    // `target` outside `[0, depth]`: every ite branch fixes `y` to
    // one of `{0, 1, …, depth}`, so an external `y = target` with
    // `target > depth` rules out every branch.
    for &(depth, target) in &[(1usize, 7u64), (3, 50)] {
        cross_validate(
            &format!("ite_chain_unsat_depth={}_t={}", depth, target),
            &build_ite_chain(depth, target),
            Verdict::Unsat,
        );
    }
}

#[test]
fn matrix_double_negation() {
    // `(not (not (= x 0)))` ≡ `(= x 0)`: SAT (x = 0 satisfies).
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (not (not (= x (as ff0 F)))))
"#;
    cross_validate("double_negation", src, Verdict::Sat);
}

#[test]
fn matrix_triple_negation() {
    // Odd number of negations flips polarity.
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (not (not (not (= x (as ff0 F))))))
(assert (= x (as ff0 F)))
"#;
    cross_validate("triple_negation_unsat", src, Verdict::Unsat);
}

// ──────────── Property-based cross-validation (CDCL(T) vs DNF) ─────────────

/// Assert CDCL(T) and DNF agree, skipping when DNF gave up at the
/// size cap.
fn cross_validate_agreement(name: &str, src: &str) {
    let q = picus_solver::smt2::parse_boolean(src)
        .unwrap_or_else(|e| panic!("[{}] parse: {:?}", name, e));
    let cdclt = picus_solver::cdclt::solve_formula(
        q.prime.clone(),
        q.var_names(),
        &q.formula,
        &picus_core::timeout::CancelToken::none(),
    );
    let dnf = picus_solver::boolean::solve_boolean_query_dnf(
        &q,
        &picus_core::timeout::CancelToken::none(),
    );
    let cv = verdict(&cdclt);
    let dv = verdict(&dnf);
    if dv == Verdict::Unknown {
        return;
    }
    assert_eq!(cv, dv, "[{}] CDCL(T)={:?} DNF={:?}", name, cdclt, dnf);
}

/// Tiny xorshift used to build deterministic random Boolean inputs.
fn xorshift(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn rand_3cnf(seed: u64, n_vars: usize, n_clauses: usize) -> String {
    let mut s = format!("(set-logic QF_FF)\n(define-sort F () (_ FiniteField 7))\n");
    for i in 0..n_vars {
        s.push_str(&format!("(declare-fun x{} () F)\n", i));
    }
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    for _ in 0..n_clauses {
        s.push_str("(assert (or");
        for _ in 0..3 {
            let v = (xorshift(&mut state) as usize) % n_vars;
            let c = (xorshift(&mut state) as usize) % 3;
            let neg = xorshift(&mut state) & 1 == 1;
            let lit = format!(" (= x{} (as ff{} F))", v, c);
            if neg {
                s.push_str(" (not");
                s.push_str(&lit);
                s.push(')');
            } else {
                s.push_str(&lit);
            }
        }
        s.push_str("))\n");
    }
    s.push_str("(check-sat)\n");
    s
}

fn rand_implies_chain(seed: u64, n_steps: usize) -> String {
    let mut state = seed.wrapping_mul(0xC2B2_AE3D_27D4_EB4F).wrapping_add(1);
    let mut s = String::from("(set-logic QF_FF)\n(define-sort F () (_ FiniteField 11))\n");
    let n_vars = (n_steps + 1).max(2);
    for i in 0..n_vars {
        s.push_str(&format!("(declare-fun x{} () F)\n", i));
    }
    let v0 = (xorshift(&mut state) as usize) % 3;
    s.push_str(&format!("(assert (= x0 (as ff{} F)))\n", v0));
    for i in 0..n_steps {
        let a_idx = i;
        let b_idx = i + 1;
        let a_const = (xorshift(&mut state) as usize) % 3;
        let b_const = (xorshift(&mut state) as usize) % 3;
        s.push_str(&format!(
            "(assert (=> (= x{} (as ff{} F)) (= x{} (as ff{} F))))\n",
            a_idx, a_const, b_idx, b_const,
        ));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn cross_validate_random_3cnf_sweep() {
    for seed in 0..8u64 {
        for &(nv, nc) in &[(3usize, 5usize), (4, 8), (5, 10), (6, 12)] {
            let src = rand_3cnf(seed * 9973 + (nv * 100 + nc) as u64, nv, nc);
            cross_validate_agreement(
                &format!("random_3cnf_seed={}_vars={}_clauses={}", seed, nv, nc),
                &src,
            );
        }
    }
}

#[test]
fn cross_validate_random_implies_chain_sweep() {
    for seed in 0..8u64 {
        for n_steps in [1usize, 3, 5, 8] {
            let src = rand_implies_chain(seed * 31337 + n_steps as u64, n_steps);
            cross_validate_agreement(
                &format!("random_implies_seed={}_steps={}", seed, n_steps),
                &src,
            );
        }
    }
}

#[test]
fn cross_validate_dense_atom_reuse() {
    // Stress atom interning + mutex emission: many ors that reuse the
    // same variables with various constants. Verifies CDCL(T) and DNF
    // agree even when SAT prunes assignments via mutex clauses.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 13))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(assert (or (= a (as ff0 F)) (= a (as ff1 F)) (= a (as ff2 F))))
(assert (or (= b (as ff0 F)) (= b (as ff1 F))))
(assert (or (= c (as ff0 F)) (= c (as ff2 F))))
(assert (=> (= a (as ff1 F)) (= b (as ff0 F))))
(assert (=> (= b (as ff0 F)) (= c (as ff0 F))))
(check-sat)
"#;
    cross_validate_agreement("dense_atom_reuse", src);
}

#[test]
fn cross_validate_mutex_pin_unsat() {
    // Non-bit constants block `rewrite_disjunctive_bit`, leaving the
    // OR branches as distinct single-var-eq atoms; mutex clauses then
    // make `(= a 7)` conflict with both disjuncts.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 13))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(assert (or (= a (as ff5 F)) (= a (as ff6 F))))
(assert (or (= b (as ff5 F)) (= b (as ff6 F))))
(assert (or (= c (as ff5 F)) (= c (as ff6 F))))
(assert (= a (as ff7 F)))
(check-sat)
"#;
    cross_validate("mutex_pin_unsat", src, Verdict::Unsat);
}

#[test]
fn cross_validate_repeated_intern_no_extra_clauses() {
    // Same atom appears many times. CDCL(T) and DNF must still agree
    // (and CDCL(T) should not blow up on redundant atom interning).
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 7))
(declare-fun a () F)
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(assert (or (= a (as ff0 F)) (= a (as ff1 F))))
(check-sat)
"#;
    cross_validate("repeated_intern", src, Verdict::Sat);
}

// ───────── Theory propagation (pinned-var linear substitution) ─────────

#[test]
fn cross_validate_theory_prop_linear_sat() {
    // x=3 + (x+y=7) forces y=4; OR satisfied by y=4 branch.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff3 F)))
(assert (or (= y (as ff4 F)) (= y (as ff5 F))))
(assert (= (ff.add x y) (as ff7 F)))
(check-sat)
"#;
    cross_validate("theory_prop_linear_sat", src, Verdict::Sat);
}

#[test]
fn cross_validate_theory_prop_linear_unsat() {
    // x=3, x+y=7 ⇒ y=4; OR over y ∈ {5, 6} excludes y=4 ⇒ UNSAT.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff3 F)))
(assert (or (= y (as ff5 F)) (= y (as ff6 F))))
(assert (= (ff.add x y) (as ff7 F)))
(check-sat)
"#;
    cross_validate("theory_prop_linear_unsat", src, Verdict::Unsat);
}

#[test]
fn cross_validate_theory_prop_chain_unsat() {
    // x=2, x+y=10 ⇒ y=8; y+z=20 ⇒ z=12; contradicts z=4.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(declare-fun z () F)
(assert (= x (as ff2 F)))
(assert (= (ff.add x y) (as ff10 F)))
(assert (= (ff.add y z) (as ff20 F)))
(assert (= z (as ff4 F)))
(check-sat)
"#;
    cross_validate("theory_prop_chain_unsat", src, Verdict::Unsat);
}

#[test]
fn cross_validate_theory_prop_three_branch_sat() {
    // 3-way OR over b; theory propagation picks the matching branch.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 13))
(declare-fun a () F)
(declare-fun b () F)
(assert (= a (as ff5 F)))
(assert (or (= b (as ff1 F)) (= b (as ff2 F)) (= b (as ff3 F))))
(assert (= (ff.add a b) (as ff7 F)))
(check-sat)
"#;
    cross_validate("theory_prop_three_branch_sat", src, Verdict::Sat);
}

#[test]
fn cross_validate_theory_prop_three_branch_unsat() {
    // 3-way OR over b; every branch contradicts the sum.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 13))
(declare-fun a () F)
(declare-fun b () F)
(assert (= a (as ff5 F)))
(assert (or (= b (as ff7 F)) (= b (as ff8 F)) (= b (as ff9 F))))
(assert (= (ff.add a b) (as ff7 F)))
(check-sat)
"#;
    cross_validate("theory_prop_three_branch_unsat", src, Verdict::Unsat);
}

#[test]
fn cross_validate_negated_eq_does_not_drive_pinning() {
    // Negative-polarity literals must not contribute to pinning.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (not (= x (as ff5 F))))
(assert (= (ff.add x y) (as ff10 F)))
(check-sat)
"#;
    cross_validate("negated_eq_no_pinning", src, Verdict::Sat);
}

#[test]
fn cross_validate_degree_two_pinned_sat() {
    // x=3, (x*x = 9): theory evaluates 3*3 = 9 ⇒ True.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (= x (as ff3 F)))
(assert (= (ff.mul x x) (as ff9 F)))
(check-sat)
"#;
    cross_validate("degree_two_pinned_sat", src, Verdict::Sat);
}

#[test]
fn cross_validate_degree_two_pinned_unsat() {
    // x=3, (x*x = 8) over GF(101): 3*3 ≠ 8 ⇒ UNSAT.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (= x (as ff3 F)))
(assert (= (ff.mul x x) (as ff8 F)))
(check-sat)
"#;
    cross_validate("degree_two_pinned_unsat", src, Verdict::Unsat);
}

// ───────── Tier 2: linear-residue propagation through asserted atoms ─────────

#[test]
fn cross_validate_tier2_linear_residue_sat() {
    // Tier 2: x=3 + (x+y=7) ⇒ y=4 propagated against the OR.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff3 F)))
(assert (= (ff.add x y) (as ff7 F)))
(assert (or (= y (as ff4 F)) (= y (as ff5 F))))
(check-sat)
"#;
    cross_validate("tier2_linear_residue_sat", src, Verdict::Sat);
}

#[test]
fn cross_validate_tier2_linear_residue_unsat() {
    // Same shape but the OR over y excludes the derived value (=4).
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff3 F)))
(assert (= (ff.add x y) (as ff7 F)))
(assert (or (= y (as ff5 F)) (= y (as ff6 F))))
(check-sat)
"#;
    cross_validate("tier2_linear_residue_unsat", src, Verdict::Unsat);
}

#[test]
fn cross_validate_tier2_chain_sat() {
    // Tier 2 cascade: x=2 ⇒ y=8 ⇒ z=12; OR picks the z=12 branch.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(declare-fun z () F)
(assert (= x (as ff2 F)))
(assert (= (ff.add x y) (as ff10 F)))
(assert (= (ff.add y z) (as ff20 F)))
(assert (or (= z (as ff4 F)) (= z (as ff12 F))))
(check-sat)
"#;
    cross_validate("tier2_chain_sat", src, Verdict::Sat);
}

#[test]
fn cross_validate_tier2_nonunit_coefficient_sat() {
    // x=4 + (x*y = 12) ⇒ 4y = 12 ⇒ y = 3 (Fermat-based inverse).
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff4 F)))
(assert (= (ff.mul x y) (as ff12 F)))
(assert (or (= y (as ff3 F)) (= y (as ff5 F))))
(check-sat)
"#;
    cross_validate("tier2_nonunit_coeff_sat", src, Verdict::Sat);
}

#[test]
fn cross_validate_tier2_multi_unpinned_falls_back_to_post_check() {
    // Two unpinned vars under x pinned ⇒ Tier 2 bails; verdict via
    // SAT + post_check.
    let src = r#"
(set-logic QF_FF)
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(declare-fun z () F)
(assert (= x (as ff3 F)))
(assert (= (ff.add x (ff.add y z)) (as ff10 F)))
(assert (or (= y (as ff2 F)) (= y (as ff5 F))))
(assert (or (= z (as ff5 F)) (= z (as ff2 F))))
(check-sat)
"#;
    cross_validate("tier2_multi_unpinned", src, Verdict::Sat);
}

#[test]
fn cross_validate_theory_prop_random_linear_sweep() {
    // 20 random `(x=c_x, y=c_y, x+y=c_sum)` instances over GF(13).
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let prime: u64 = 13;
    for _ in 0..20 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let cx = (state as u64) % prime;
        let cy = (state.wrapping_mul(0x100000001B3)) % prime;
        let csum = (state.wrapping_mul(0xCBF29CE484222325)) % prime;
        let expected = if (cx + cy) % prime == csum {
            Verdict::Sat
        } else {
            Verdict::Unsat
        };
        let src = format!(
            "(set-logic QF_FF)\n\
             (define-sort F () (_ FiniteField {p}))\n\
             (declare-fun x () F)\n\
             (declare-fun y () F)\n\
             (assert (= x (as ff{cx} F)))\n\
             (assert (= y (as ff{cy} F)))\n\
             (assert (= (ff.add x y) (as ff{csum} F)))\n\
             (check-sat)\n",
            p = prime,
            cx = cx,
            cy = cy,
            csum = csum,
        );
        cross_validate(
            &format!("theory_prop_rand_linear cx={cx} cy={cy} csum={csum}"),
            &src,
            expected,
        );
    }
}

// ─────────────────── SAT model contents ────────────────────────────

/// CDCL(T) SAT must return a model that includes the FF variable.
#[test]
fn cdclt_sat_model_includes_ff_var() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(assert (= x #f3m7))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("x"), Some(&BigUint::from(3u32)),
                "x must be present and equal to 3; got {:?}", m);
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// CDCL(T) SAT must return a model that includes any Bool variable
/// that appeared on the trail. Bool vars are encoded as FF elements
/// in {0, 1}, so the model entry is a `BigUint` of 0 or 1.
#[test]
fn cdclt_sat_model_includes_bool_var_true() {
    let src = r#"
(set-logic QF_FF)
(declare-fun b () Bool)
(assert b)
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b"), Some(&BigUint::from(1u32)),
                "b asserted ⇒ model must have b = 1; got {:?}", m);
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

#[test]
fn cdclt_sat_model_includes_bool_var_false() {
    let src = r#"
(set-logic QF_FF)
(declare-fun b () Bool)
(assert (not b))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b"), Some(&BigUint::from(0u32)),
                "¬b asserted ⇒ model must have b = 0; got {:?}", m);
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Free Bool variable (no constraint on it): the model must still
/// include it, with value in {0, 1}.
#[test]
fn cdclt_sat_model_includes_free_bool_var() {
    let src = r#"
(set-logic QF_FF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            let a_val = m.get("a").expect("a in model").clone();
            let b_val = m.get("b").expect("b in model").clone();
            assert!(a_val == BigUint::from(0u32) || a_val == BigUint::from(1u32),
                "a must be 0 or 1, got {:?}", a_val);
            assert!(b_val == BigUint::from(0u32) || b_val == BigUint::from(1u32),
                "b must be 0 or 1, got {:?}", b_val);
            assert!(a_val == BigUint::from(1u32) || b_val == BigUint::from(1u32),
                "(or a b) ⇒ at least one is 1; got a={:?} b={:?}", a_val, b_val);
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Mixed Bool + FF SAT: both must be present in the model.
#[test]
fn cdclt_sat_model_includes_mixed_bool_and_ff() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(declare-fun b () Bool)
(assert b)
(assert (= x #f3m7))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("x"), Some(&BigUint::from(3u32)));
            assert_eq!(m.get("b"), Some(&BigUint::from(1u32)));
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Term-level ite SAT: the named FF variables must appear; the
/// skolem `__ite_N` is an implementation detail and is allowed to
/// be present or not.
#[test]
fn cdclt_sat_model_with_term_level_ite() {
    let src = r#"
(set-logic QF_FF)
(declare-fun c () Bool)
(declare-fun x () (_ FiniteField 101))
(assert (= (ite c x #f0m101) #f5m101))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            let c_val = m.get("c").expect("c in model").clone();
            let x_val = m.get("x").expect("x in model").clone();
            // ite picks x when c is True (== 1).
            if c_val == BigUint::from(1u32) {
                assert_eq!(x_val, BigUint::from(5u32),
                    "c=1 ⇒ x must equal 5; got x={:?}", x_val);
            } else {
                panic!("c must be 1 for the equality to hold; got c={:?}", c_val);
            }
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}
