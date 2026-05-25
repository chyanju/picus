//! Boolean structure handling on QF_FF inputs.
//!
//! Pipeline:
//!
//! 1. Parse a Boolean formula over FF equality/disequality atoms
//!    (`and`, `or`, `not`, `=>`, assertion-level `ite`).
//! 2. Apply [`rewrite_disjunctive_bit`].
//! 3. Negation-normal form via [`Formula::nnf`].
//! 4. Disjunctive normal form via [`Formula::to_dnf`] (worst case
//!    exponential in the number of `or` nodes).
//! 5. Dispatch each DNF disjunct as a conjunctive [`ConstraintSystem`]
//!    to [`solve_encoded_with_cancel`]. The query is SAT iff some
//!    disjunct is SAT; UNSAT iff every disjunct is UNSAT.
//!
//! [`Literal`] carries index-keyed `Vec<PolyTerm>` whose `VarIdx`
//! values reference [`BooleanQuery::builder`]'s variable frame.
//! [`rewrite_disjunctive_bit`] is the equivalent of cvc5's disjunctive-bit preprocessing pass.

use num_bigint::BigUint;
use num_traits::Zero;

use crate::core::{solve_encoded_with_cancel, SolveOutcome};
use crate::frontend::encoder::{
    encode, ConstraintSystemBuilder, ConstraintSystem, PolyTerm, VarIdx,
};
use crate::timeout::CancelToken;

/// A literal over FF terms: an equality or a disequality.
/// `Vec<PolyTerm>` indices reference the producing
/// [`BooleanQuery::builder`]'s variable frame.
#[derive(Clone, Debug)]
pub enum Literal {
    Eq(Vec<PolyTerm>, Vec<PolyTerm>),
    Neq(Vec<PolyTerm>, Vec<PolyTerm>),
}

/// A Boolean formula over FF literals.
#[derive(Clone, Debug)]
pub enum Formula {
    Lit(Literal),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Not(Box<Formula>),
    True,
    False,
}

impl Formula {
    /// Push negations to the leaves (negation-normal form). Negated
    /// literals flip `Eq`↔`Neq`.
    pub fn nnf(self) -> Formula {
        match self {
            Formula::Not(inner) => match *inner {
                Formula::Lit(Literal::Eq(a, b)) => Formula::Lit(Literal::Neq(a, b)),
                Formula::Lit(Literal::Neq(a, b)) => Formula::Lit(Literal::Eq(a, b)),
                Formula::And(fs) => Formula::Or(
                    fs.into_iter()
                        .map(|f| Formula::Not(Box::new(f)).nnf())
                        .collect(),
                ),
                Formula::Or(fs) => Formula::And(
                    fs.into_iter()
                        .map(|f| Formula::Not(Box::new(f)).nnf())
                        .collect(),
                ),
                Formula::Not(g) => g.nnf(),
                Formula::True => Formula::False,
                Formula::False => Formula::True,
            },
            Formula::And(fs) => Formula::And(fs.into_iter().map(|f| f.nnf()).collect()),
            Formula::Or(fs) => Formula::Or(fs.into_iter().map(|f| f.nnf()).collect()),
            f @ Formula::Lit(_) => f,
            f @ Formula::True => f,
            f @ Formula::False => f,
        }
    }

    /// Expand to disjunctive normal form. Caller must call [`nnf`]
    /// first. The result is `Vec<Vec<Literal>>` where the outer list is
    /// the disjuncts and each inner list is a conjunction of literals.
    /// `vec![]` represents `False`; `vec![vec![]]` represents `True`.
    pub fn to_dnf(self) -> Vec<Vec<Literal>> {
        match self {
            Formula::Lit(l) => vec![vec![l]],
            Formula::True => vec![vec![]],
            Formula::False => vec![],
            Formula::And(fs) => {
                let mut result: Vec<Vec<Literal>> = vec![vec![]];
                for f in fs {
                    let f_dnf = f.to_dnf();
                    if f_dnf.is_empty() {
                        return vec![];
                    }
                    let mut new_result = Vec::with_capacity(result.len() * f_dnf.len());
                    for r in &result {
                        for fd in &f_dnf {
                            let mut combined = r.clone();
                            combined.extend_from_slice(fd);
                            new_result.push(combined);
                        }
                    }
                    result = new_result;
                }
                result
            }
            Formula::Or(fs) => {
                let mut result = Vec::new();
                for f in fs {
                    result.extend(f.to_dnf());
                }
                result
            }
            Formula::Not(_) => {
                panic!("Formula::to_dnf called on non-NNF input — call nnf() first")
            }
        }
    }

    /// Upper-bound estimate of `self.to_dnf().len()`, computed without
    /// materializing the DNF. Saturates at `cap` (returned as `cap`).
    /// `True` evaluates to 1, `False` to 0. Caller must have applied
    /// [`Formula::nnf`] (only the NNF Lit/And/Or/True/False shape is
    /// handled).
    pub fn dnf_size_estimate(&self, cap: u64) -> u64 {
        match self {
            Formula::Lit(_) => 1,
            Formula::True => 1,
            Formula::False => 0,
            Formula::And(fs) => {
                let mut acc: u64 = 1;
                for f in fs {
                    let s = f.dnf_size_estimate(cap);
                    if s == 0 {
                        return 0;
                    }
                    acc = acc.saturating_mul(s);
                    if acc >= cap {
                        return cap;
                    }
                }
                acc
            }
            Formula::Or(fs) => {
                let mut acc: u64 = 0;
                for f in fs {
                    acc = acc.saturating_add(f.dnf_size_estimate(cap));
                    if acc >= cap {
                        return cap;
                    }
                }
                acc
            }
            Formula::Not(_) => {
                panic!("Formula::dnf_size_estimate called on non-NNF input")
            }
        }
    }
}

/// A parsed Boolean QF_FF query. `formula` is the preprocessed-NNF
/// representation consumed by the CDCL(T) path; [`BooleanQuery::dnf`]
/// computes the DNF expansion on demand (size `O(3^k)` for k-clause
/// CNF inputs). `builder` owns the query-level variable frame; every
/// `PolyTerm` inside `formula`'s literals references indices in this
/// frame.
#[derive(Debug)]
pub struct BooleanQuery {
    pub prime: BigUint,
    pub builder: ConstraintSystemBuilder,
    /// Result of `rewrite_disjunctive_bit` + `nnf`. Suitable for
    /// Tseitin CNF conversion.
    pub formula: Formula,
    dnf_cell: std::sync::OnceLock<Vec<Vec<Literal>>>,
}

impl BooleanQuery {
    /// Build a `BooleanQuery` from a populated `builder` (containing
    /// the query's variable frame) and a Boolean formula whose
    /// `PolyTerm` indices reference that frame. Applies
    /// `rewrite_disjunctive_bit` then NNF; DNF expansion is deferred.
    pub fn from_builder_and_formula(builder: ConstraintSystemBuilder, f: Formula) -> Self {
        let prime = builder.prime().clone();
        let preprocessed = rewrite_disjunctive_bit(f, &prime);
        let nnf = preprocessed.nnf();
        BooleanQuery {
            prime,
            builder,
            formula: nnf,
            dnf_cell: std::sync::OnceLock::new(),
        }
    }

    pub fn var_names(&self) -> &[String] {
        self.builder.var_names()
    }

    /// Compute (or return the cached) DNF expansion of `self.formula`.
    /// May allocate `O(3^k)` literal containers for k-CNF inputs.
    pub fn dnf(&self) -> &Vec<Vec<Literal>> {
        self.dnf_cell
            .get_or_init(|| self.formula.clone().to_dnf())
    }

    /// Translate each DNF disjunct (a conjunction of literals) into a
    /// stand-alone [`ConstraintSystem`]. Each disjunct clones the
    /// query-level builder (inheriting the variable frame the
    /// `PolyTerm` indices reference), then appends disjunct-specific
    /// `__diseq_d_N` / `__zero` synthetics. `compact_used_vars`
    /// (called from `encode`) drops vars no disjunct
    /// constraint references.
    pub fn to_disjunct_systems(&self) -> Vec<ConstraintSystem> {
        self.dnf()
            .iter()
            .map(|disjunct| {
                let mut builder = self.builder.clone();
                let mut diseq_seq: usize = 0;
                let mut zero_idx: Option<VarIdx> = None;
                for lit in disjunct {
                    match lit {
                        Literal::Eq(a, b) => {
                            let mut combined: Vec<PolyTerm> = a.clone();
                            for t in b {
                                let neg_coeff = if t.coeff.is_zero() {
                                    BigUint::zero()
                                } else {
                                    &self.prime - &t.coeff
                                };
                                combined.push(PolyTerm {
                                    coeff: neg_coeff,
                                    vars: t.vars.clone(),
                                });
                            }
                            builder.add_equality(combined);
                        }
                        Literal::Neq(a, b) => {
                            let d_name = format!("__diseq_d_{}", diseq_seq);
                            diseq_seq += 1;
                            let d_idx = builder.var(&d_name);
                            let zero = match zero_idx {
                                Some(z) => z,
                                None => {
                                    let z = builder.var("__zero");
                                    builder.add_assignment(z, BigUint::zero());
                                    zero_idx = Some(z);
                                    z
                                }
                            };
                            // def = d - a + b
                            let mut def: Vec<PolyTerm> = vec![PolyTerm {
                                coeff: BigUint::from(1u32),
                                vars: vec![(d_idx, 1)],
                            }];
                            for t in a {
                                let neg_coeff = if t.coeff.is_zero() {
                                    BigUint::zero()
                                } else {
                                    &self.prime - &t.coeff
                                };
                                def.push(PolyTerm {
                                    coeff: neg_coeff,
                                    vars: t.vars.clone(),
                                });
                            }
                            def.extend(b.iter().cloned());
                            builder.add_equality(def);
                            builder.add_disequality(d_idx, zero);
                        }
                    }
                }
                builder.build()
            })
            .collect()
    }
}

/// `Eq(a, b)` → normalized form of `a - b`. Returns `None` for
/// disequalities. The result is a `Vec<PolyTerm>` in the same
/// variable frame as `lit`.
fn eq_normalized_poly(lit: &Literal, prime: &BigUint) -> Option<Vec<PolyTerm>> {
    if let Literal::Eq(a, b) = lit {
        let mut poly: Vec<PolyTerm> = a.clone();
        for t in b {
            let neg_coeff = if t.coeff.is_zero() {
                BigUint::zero()
            } else {
                prime - &t.coeff
            };
            poly.push(PolyTerm {
                coeff: neg_coeff,
                vars: t.vars.clone(),
            });
        }
        crate::frontend::rewriter::normalize_term_list(&mut poly, prime);
        Some(poly)
    } else {
        None
    }
}

/// Match an equality literal of the form `x = const`. Returns
/// `(var_idx, const_value)` on match; the index is in the input
/// literal's frame.
fn parse_var_equals_const(lit: &Literal, prime: &BigUint) -> Option<(VarIdx, BigUint)> {
    let poly = eq_normalized_poly(lit, prime)?;
    let mut var_term: Option<&PolyTerm> = None;
    let mut const_term: Option<&PolyTerm> = None;
    for t in &poly {
        if t.vars.is_empty() {
            if const_term.is_some() {
                return None;
            }
            const_term = Some(t);
        } else if t.vars.len() == 1 && t.vars[0].1 == 1 {
            if var_term.is_some() {
                return None;
            }
            var_term = Some(t);
        } else {
            return None;
        }
    }
    let vt = var_term?;
    if vt.coeff != BigUint::from(1u32) {
        return None;
    }
    let val = match const_term {
        Some(ct) => {
            if ct.coeff.is_zero() {
                BigUint::zero()
            } else {
                prime - &ct.coeff
            }
        }
        None => BigUint::zero(),
    };
    Some((vt.vars[0].0, val))
}

/// Match cvc5's `parse::disjunctiveBitConstraint`: `(or (= x 0) (= x 1))`
/// or its symmetric form. On match return `Some(var_idx)`.
fn try_disjunctive_bit(or_children: &[Formula], prime: &BigUint) -> Option<VarIdx> {
    if or_children.len() != 2 {
        return None;
    }
    let (lit0, lit1) = match (&or_children[0], &or_children[1]) {
        (Formula::Lit(l0), Formula::Lit(l1)) => (l0, l1),
        _ => return None,
    };
    let (v0, c0) = parse_var_equals_const(lit0, prime)?;
    let (v1, c1) = parse_var_equals_const(lit1, prime)?;
    if v0 != v1 {
        return None;
    }
    let zero = BigUint::zero();
    let one = BigUint::from(1u32);
    let bit_match = (c0 == zero && c1 == one) || (c0 == one && c1 == zero);
    if bit_match {
        Some(v0)
    } else {
        None
    }
}

/// Equivalent of cvc5's disjunctive-bit preprocessing pass.
/// Rewrites every `(or (= x 0) (= x 1))` subformula to the polynomial
/// equality `x * x = x` (a single-conjunct literal). Other formula
/// nodes are recursed into unchanged.
pub fn rewrite_disjunctive_bit(f: Formula, prime: &BigUint) -> Formula {
    match f {
        Formula::Or(children) => {
            if let Some(idx) = try_disjunctive_bit(&children, prime) {
                return Formula::Lit(Literal::Eq(
                    vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![(idx, 2)],
                    }],
                    vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![(idx, 1)],
                    }],
                ));
            }
            Formula::Or(
                children
                    .into_iter()
                    .map(|c| rewrite_disjunctive_bit(c, prime))
                    .collect(),
            )
        }
        Formula::And(children) => Formula::And(
            children
                .into_iter()
                .map(|c| rewrite_disjunctive_bit(c, prime))
                .collect(),
        ),
        Formula::Not(inner) => Formula::Not(Box::new(rewrite_disjunctive_bit(*inner, prime))),
        f @ (Formula::Lit(_) | Formula::True | Formula::False) => f,
    }
}

/// Solve a [`BooleanQuery`].
///
/// Default path: CDCL(T) over the original formula via
/// [`crate::cdclt::solve_formula`]. The DNF-enumeration path is
/// retained as a baseline and is selected by setting the environment
/// variable `PICUS_BOOLEAN=dnf` (used for cross-validation tests).
pub fn solve_boolean_query(query: &BooleanQuery, cancel: &CancelToken) -> SolveOutcome {
    if crate::config::with(|c| c.dnf_enabled) {
        solve_boolean_query_dnf(query, cancel)
    } else {
        crate::cdclt::solve_formula(
            query.prime.clone(),
            query.var_names(),
            &query.formula,
            cancel,
        )
    }
}

/// Maximum DNF disjunct count before [`solve_boolean_query_dnf`]
/// gives up and returns `Unknown`. Configured via
/// [`crate::config::RuntimeConfig::dnf_cap`].
pub fn dnf_size_cap() -> u64 {
    crate::config::with(|c| c.dnf_cap)
}

/// DNF-enumeration path: try each DNF disjunct in order through the
/// GB solver. Returns `Sat` on the first SAT disjunct, `Unsat` only
/// if every disjunct is UNSAT (with an empty core — per-disjunct
/// cores index into different polynomial sets), or `Unknown` if any
/// disjunct came back `Unknown` and none came back SAT.
///
/// Returns `Unknown` without materializing the DNF when the formula's
/// estimated DNF size exceeds [`dnf_size_cap`].
pub fn solve_boolean_query_dnf(query: &BooleanQuery, cancel: &CancelToken) -> SolveOutcome {
    let cap = dnf_size_cap();
    if query.formula.dnf_size_estimate(cap) >= cap {
        return SolveOutcome::Unknown;
    }
    let systems = query.to_disjunct_systems();
    if systems.is_empty() {
        return SolveOutcome::Unsat(Vec::new());
    }
    let mut saw_unknown = false;
    for sys in &systems {
        if cancel.is_cancelled() {
            return SolveOutcome::Unknown;
        }
        let encoded = match encode(sys) {
            Ok(e) => e,
            Err(_) => {
                saw_unknown = true;
                continue;
            }
        };
        match solve_encoded_with_cancel(&encoded, cancel) {
            SolveOutcome::Sat(m) => return SolveOutcome::Sat(m),
            SolveOutcome::Unknown => saw_unknown = true,
            SolveOutcome::Unsat(_) => continue,
        }
    }
    if saw_unknown {
        SolveOutcome::Unknown
    } else {
        SolveOutcome::Unsat(Vec::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// PolyTerm constructor: `coeff * <idx>^exp` (exp=0 → constant).
    fn pt(coeff: u64, idx: u32, exp: u16) -> PolyTerm {
        let vars = if exp == 0 { vec![] } else { vec![(idx, exp)] };
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars,
        }
    }

    /// Construct a builder pre-populated with the given var names.
    fn builder_with_vars(prime: u64, names: &[&str]) -> ConstraintSystemBuilder {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(prime));
        for n in names {
            b.var(n);
        }
        b
    }

    /// Build a Lit::Eq for `coeff * <var_idx> == rhs_const`.
    fn lit_eq(coeff: u64, var_idx: u32, rhs_const: u64) -> Formula {
        Formula::Lit(Literal::Eq(vec![pt(coeff, var_idx, 1)], vec![pt(rhs_const, 0, 0)]))
    }

    #[test]
    fn nnf_distributes_not() {
        // Frame: x=0, y=1
        let f = Formula::Not(Box::new(Formula::And(vec![
            lit_eq(1, 0, 0),
            lit_eq(1, 1, 0),
        ])));
        let nnf = f.nnf();
        match nnf {
            Formula::Or(fs) => {
                assert_eq!(fs.len(), 2);
                for f in fs {
                    matches!(f, Formula::Lit(Literal::Neq(_, _)));
                }
            }
            _ => panic!("expected Or after nnf"),
        }
    }

    #[test]
    fn dnf_of_and_or() {
        // frame: a=0, b=1, c=2, d=3
        let a = lit_eq(1, 0, 0);
        let b = lit_eq(1, 1, 0);
        let c = lit_eq(1, 2, 0);
        let d = lit_eq(1, 3, 0);
        let f = Formula::And(vec![Formula::Or(vec![a, b]), Formula::Or(vec![c, d])]);
        let dnf = f.nnf().to_dnf();
        assert_eq!(dnf.len(), 4);
        for d in &dnf {
            assert_eq!(d.len(), 2);
        }
    }

    #[test]
    fn dnf_false_propagates() {
        let f = Formula::And(vec![Formula::True, Formula::False]);
        let dnf = f.nnf().to_dnf();
        assert!(dnf.is_empty());
    }

    #[test]
    fn dnf_true_is_single_empty_conj() {
        let dnf = Formula::True.nnf().to_dnf();
        assert_eq!(dnf.len(), 1);
        assert!(dnf[0].is_empty());
    }

    #[test]
    fn disjunct_systems_split() {
        // or(x = 0, y = 0) → two ConstraintSystems
        let builder = builder_with_vars(101, &["x", "y"]);
        let f = Formula::Or(vec![lit_eq(1, 0, 0), lit_eq(1, 1, 0)]);
        let q = BooleanQuery::from_builder_and_formula(builder, f);
        let systems = q.to_disjunct_systems();
        assert_eq!(systems.len(), 2);
        assert_eq!(systems[0].equalities.len(), 1);
        assert_eq!(systems[1].equalities.len(), 1);
    }

    #[test]
    fn solve_disjunctive_bit_sat() {
        let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff0 F)) (= x (as ff1 F))))
";
        let q = crate::smt2::parse_boolean(src).expect("parse");
        assert_eq!(q.dnf().len(), 1);
        let outcome = solve_boolean_query(&q, &CancelToken::none());
        assert!(matches!(outcome, SolveOutcome::Sat(_)));
    }

    #[test]
    fn disjunctive_bit_rewrites_pattern() {
        // Direct test of the rewrite pass: or(x=0, x=1) → x*x = x
        let prime = BigUint::from(101u32);
        let f = Formula::Or(vec![lit_eq(1, 0, 0), lit_eq(1, 0, 1)]);
        let rewritten = rewrite_disjunctive_bit(f, &prime);
        match rewritten {
            Formula::Lit(Literal::Eq(lhs, rhs)) => {
                assert_eq!(lhs.len(), 1);
                assert_eq!(lhs[0].vars, vec![(0, 2)]);
                assert_eq!(rhs.len(), 1);
                assert_eq!(rhs[0].vars, vec![(0, 1)]);
            }
            _ => panic!("expected single Eq literal after disjunctive-bit rewrite"),
        }
    }

    fn outcome_kind(o: &SolveOutcome) -> &'static str {
        match o {
            SolveOutcome::Sat(_) => "sat",
            SolveOutcome::Unsat(_) => "unsat",
            SolveOutcome::Unknown => "unknown",
        }
    }

    fn assert_cdclt_dnf_agree(src: &str) {
        let q = crate::smt2::parse_boolean(src).expect("parse");
        let cdclt_out = crate::cdclt::solve_formula(
            q.prime.clone(),
            q.var_names(),
            &q.formula,
            &CancelToken::none(),
        );
        let dnf_out = solve_boolean_query_dnf(&q, &CancelToken::none());
        assert_eq!(outcome_kind(&cdclt_out), outcome_kind(&dnf_out));
    }

    #[test]
    fn cross_validate_disjunctive_bit() {
        let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff0 F)) (= x (as ff1 F))))
";
        assert_cdclt_dnf_agree(src);
    }

    #[test]
    fn cross_validate_unsat_chain() {
        let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff0 F)))
(assert (=> (= x (as ff0 F)) (= y (as ff0 F))))
(assert (not (= y (as ff0 F))))
";
        assert_cdclt_dnf_agree(src);
    }

    #[test]
    fn cross_validate_or_with_distinct_branches() {
        let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff5 F)) (= x (as ff6 F))))
";
        assert_cdclt_dnf_agree(src);
    }

    #[test]
    fn cross_validate_three_or_unsat() {
        let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff0 F)) (= x (as ff1 F)) (= x (as ff2 F))))
(assert (= x (as ff7 F)))
";
        assert_cdclt_dnf_agree(src);
    }

    #[test]
    fn disjunctive_bit_does_not_match_unrelated_vars() {
        // or(x = 0, y = 1) — different vars, should NOT collapse.
        let prime = BigUint::from(101u32);
        let f = Formula::Or(vec![lit_eq(1, 0, 0), lit_eq(1, 1, 1)]);
        let rewritten = rewrite_disjunctive_bit(f, &prime);
        assert!(matches!(rewritten, Formula::Or(_)));
    }

    #[test]
    fn solve_disjunctive_unsat() {
        let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (= x (as ff1 F)))
(assert (or (= x (as ff0 F)) (= x (as ff2 F))))
";
        let q = crate::smt2::parse_boolean(src).expect("parse");
        let outcome = solve_boolean_query(&q, &CancelToken::none());
        assert!(matches!(outcome, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn solve_with_not_and_implies() {
        let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff0 F)))
(assert (=> (= x (as ff0 F)) (= y (as ff0 F))))
(assert (not (= y (as ff0 F))))
";
        let q = crate::smt2::parse_boolean(src).expect("parse");
        let outcome = solve_boolean_query(&q, &CancelToken::none());
        assert!(matches!(outcome, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn dnf_size_estimate_lit_is_one() {
        let f = lit_eq(1, 0, 0);
        assert_eq!(f.dnf_size_estimate(1_000), 1);
    }

    #[test]
    fn dnf_size_estimate_and_of_ors_multiplies() {
        // 5 fold and-of-ors with each or having 2 disjuncts → 2^5 = 32.
        // Use distinct indices 0..4 to keep literals over distinct vars.
        let ors: Vec<Formula> = (0..5)
            .map(|i| Formula::Or(vec![lit_eq(1, i as u32, 0), lit_eq(1, i as u32, 1)]))
            .collect();
        let f = Formula::And(ors).nnf();
        assert_eq!(f.dnf_size_estimate(1_000), 32);
        assert_eq!(f.to_dnf().len(), 32);
    }

    #[test]
    fn dnf_size_estimate_saturates_at_cap() {
        let ors: Vec<Formula> = (0..30)
            .map(|i| Formula::Or(vec![lit_eq(1, i as u32, 0), lit_eq(1, i as u32, 1)]))
            .collect();
        let f = Formula::And(ors).nnf();
        let est = f.dnf_size_estimate(100_000);
        assert_eq!(est, 100_000);
    }

    #[test]
    fn solve_boolean_query_dnf_returns_unknown_past_cap() {
        // 4 ors × 2 = DNF length 16; cap 8 ⇒ Unknown. ConfigGuard
        // scopes the override so we don't need a cross-test lock.
        let _g = crate::config::ConfigGuard::with_override(|c| {
            c.dnf_enabled = true;
            c.dnf_cap = 8;
        });
        let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(declare-fun d () F)
(assert (or (= a (as ff5 F)) (= a (as ff6 F))))
(assert (or (= b (as ff5 F)) (= b (as ff6 F))))
(assert (or (= c (as ff5 F)) (= c (as ff6 F))))
(assert (or (= d (as ff5 F)) (= d (as ff6 F))))
"#;
        let q = crate::smt2::parse_boolean(src).expect("parse");
        let outcome = solve_boolean_query_dnf(&q, &CancelToken::none());
        assert!(matches!(outcome, SolveOutcome::Unknown));
    }
}
