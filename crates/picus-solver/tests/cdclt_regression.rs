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

use picus_solver::boolean::solve_boolean_query_dnf;
use picus_solver::cdclt::solve_formula;
use picus_solver::core::SolveOutcome;
use picus_solver::smt2::parse_boolean;
use picus_solver::timeout::CancelToken;

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
    let cdclt = solve_formula(q.prime.clone(), &q.formula, &CancelToken::none());
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
