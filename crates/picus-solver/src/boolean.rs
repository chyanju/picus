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
//! [`rewrite_disjunctive_bit`] is the equivalent of cvc5
//! `preprocessing/passes/ff_disjunctive_bit.cpp`.

use num_bigint::BigUint;
use num_traits::Zero;

use crate::core::{solve_encoded_with_cancel, SolveOutcome};
use crate::encoder::{encode, ConstraintSystem, PolyTerm};
use crate::timeout::CancelToken;

/// A literal over FF terms: an equality or a disequality.
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
}

/// A parsed Boolean QF_FF query in DNF.
#[derive(Debug)]
pub struct BooleanQuery {
    pub prime: BigUint,
    pub var_names: Vec<String>,
    pub dnf: Vec<Vec<Literal>>,
}

impl BooleanQuery {
    /// Build a `BooleanQuery` from a Boolean formula. Applies the
    /// `ff_disjunctive_bit` preprocessing pass before NNF/DNF expansion.
    pub fn from_formula(prime: BigUint, var_names: Vec<String>, f: Formula) -> Self {
        let preprocessed = rewrite_disjunctive_bit(f, &prime);
        let nnf = preprocessed.nnf();
        let dnf = nnf.to_dnf();
        BooleanQuery {
            prime,
            var_names,
            dnf,
        }
    }

    /// Translate each DNF disjunct (a conjunction of literals) into a
    /// stand-alone [`ConstraintSystem`]. `__zero` is pinned to the
    /// field's zero for any disjunct that contains a disequality.
    pub fn to_disjunct_systems(&self) -> Vec<ConstraintSystem> {
        let mut diseq_seq: usize = 0;
        self.dnf
            .iter()
            .map(|disjunct| {
                let mut equalities: Vec<Vec<PolyTerm>> = Vec::new();
                let mut disequalities: Vec<(String, String)> = Vec::new();
                let mut needs_zero = false;
                for lit in disjunct {
                    match lit {
                        Literal::Eq(a, b) => {
                            let mut poly: Vec<PolyTerm> = a.clone();
                            for t in b {
                                let neg_coeff = if t.coeff.is_zero() {
                                    BigUint::zero()
                                } else {
                                    &self.prime - &t.coeff
                                };
                                poly.push(PolyTerm {
                                    coeff: neg_coeff,
                                    vars: t.vars.clone(),
                                });
                            }
                            equalities.push(poly);
                        }
                        Literal::Neq(a, b) => {
                            let d_name = format!("__diseq_d_{}", diseq_seq);
                            diseq_seq += 1;
                            let mut def: Vec<PolyTerm> = vec![PolyTerm {
                                coeff: BigUint::from(1u32),
                                vars: vec![d_name.clone()],
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
                            equalities.push(def);
                            disequalities.push((d_name, "__zero".to_string()));
                            needs_zero = true;
                        }
                    }
                }
                let mut assignments: Vec<(String, BigUint)> = Vec::new();
                if needs_zero {
                    assignments.push(("__zero".into(), BigUint::zero()));
                }
                let mut sys = ConstraintSystem {
                    prime: self.prime.clone(),
                    equalities,
                    disequalities,
                    assignments,
                    add_field_polys: false,
                    bitsums: vec![],
                };
                crate::rewriter::rewrite_system(&mut sys);
                sys
            })
            .collect()
    }
}

/// `Eq(a, b)` → normalized form of `a - b`. Returns `None` for
/// disequalities.
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
        crate::rewriter::normalize_term_list(&mut poly, prime);
        Some(poly)
    } else {
        None
    }
}

/// Match an equality literal of the form `x = const` (with the
/// variable side having a coefficient of 1 in the canonical
/// representation). Returns `(var_name, const_value)` on match.
fn parse_var_equals_const(lit: &Literal, prime: &BigUint) -> Option<(String, BigUint)> {
    let poly = eq_normalized_poly(lit, prime)?;
    let mut var_term: Option<&PolyTerm> = None;
    let mut const_term: Option<&PolyTerm> = None;
    for t in &poly {
        if t.vars.is_empty() {
            if const_term.is_some() {
                return None;
            }
            const_term = Some(t);
        } else if t.vars.len() == 1 {
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
    Some((vt.vars[0].clone(), val))
}

/// Match cvc5's `parse::disjunctiveBitConstraint`: `(or (= x 0) (= x 1))`
/// or its symmetric form. On match return `Some(var_name)`.
fn try_disjunctive_bit(or_children: &[Formula], prime: &BigUint) -> Option<String> {
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

/// Equivalent of cvc5's `preprocessing/passes/ff_disjunctive_bit.cpp`.
/// Rewrites every `(or (= x 0) (= x 1))` subformula to the polynomial
/// equality `x * x = x` (a single-conjunct literal). Other formula
/// nodes are recursed into unchanged.
pub fn rewrite_disjunctive_bit(f: Formula, prime: &BigUint) -> Formula {
    match f {
        Formula::Or(children) => {
            if let Some(var) = try_disjunctive_bit(&children, prime) {
                return Formula::Lit(Literal::Eq(
                    vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![var.clone(), var.clone()],
                    }],
                    vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![var],
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

/// Dispatch a [`BooleanQuery`] to the GB solver: try each DNF
/// disjunct in order. Returns `Sat` on the first SAT disjunct,
/// `Unsat` only if every disjunct is UNSAT (with the union of input
/// indices as the core — coarsened over disjuncts), or `Unknown` if
/// any disjunct came back `Unknown` and none came back SAT.
///
/// `Unsat` returns an empty core because the per-disjunct cores index
/// into different polynomial sets — coalescing them into a single core
/// index list is not meaningful.
pub fn solve_boolean_query(query: &BooleanQuery, cancel: &CancelToken) -> SolveOutcome {
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

    fn t(coeff: u64, vars: &[&str]) -> PolyTerm {
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars: vars.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn nnf_distributes_not() {
        // not(and(eq, eq)) → or(neq, neq)
        let f = Formula::Not(Box::new(Formula::And(vec![
            Formula::Lit(Literal::Eq(vec![t(1, &["x"])], vec![t(0, &[])])),
            Formula::Lit(Literal::Eq(vec![t(1, &["y"])], vec![t(0, &[])])),
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
        // and(or(a, b), or(c, d)) → 4 disjuncts: ac, ad, bc, bd
        let a = Formula::Lit(Literal::Eq(vec![t(1, &["a"])], vec![t(0, &[])]));
        let b = Formula::Lit(Literal::Eq(vec![t(1, &["b"])], vec![t(0, &[])]));
        let c = Formula::Lit(Literal::Eq(vec![t(1, &["c"])], vec![t(0, &[])]));
        let d = Formula::Lit(Literal::Eq(vec![t(1, &["d"])], vec![t(0, &[])]));
        let f = Formula::And(vec![
            Formula::Or(vec![a, b]),
            Formula::Or(vec![c, d]),
        ]);
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
        assert!(dnf.is_empty(), "False should DNF to empty disjunct list");
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
        let prime = BigUint::from(101u32);
        let f = Formula::Or(vec![
            Formula::Lit(Literal::Eq(vec![t(1, &["x"])], vec![t(0, &[])])),
            Formula::Lit(Literal::Eq(vec![t(1, &["y"])], vec![t(0, &[])])),
        ]);
        let q = BooleanQuery::from_formula(prime, vec!["x".into(), "y".into()], f);
        let systems = q.to_disjunct_systems();
        assert_eq!(systems.len(), 2);
        assert_eq!(systems[0].equalities.len(), 1);
        assert_eq!(systems[1].equalities.len(), 1);
    }

    #[test]
    fn solve_disjunctive_bit_sat() {
        // or(x = 0, x = 1) is satisfiable. The disjunctive-bit pass
        // collapses the disjunction into the single polynomial
        // `x*x = x`, so DNF length is 1.
        let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff0 F)) (= x (as ff1 F))))
";
        let q = crate::smt2::parse_boolean(src).expect("parse");
        assert_eq!(q.dnf.len(), 1, "disjunctive-bit pass should collapse to one disjunct");
        let outcome = solve_boolean_query(&q, &CancelToken::none());
        assert!(matches!(outcome, SolveOutcome::Sat(_)));
    }

    #[test]
    fn disjunctive_bit_rewrites_pattern() {
        // Direct test of the rewrite pass: or(x=0, x=1) → x*x = x
        let prime = BigUint::from(101u32);
        let f = Formula::Or(vec![
            Formula::Lit(Literal::Eq(vec![t(1, &["x"])], vec![t(0, &[])])),
            Formula::Lit(Literal::Eq(vec![t(1, &["x"])], vec![t(1, &[])])),
        ]);
        let rewritten = rewrite_disjunctive_bit(f, &prime);
        match rewritten {
            Formula::Lit(Literal::Eq(lhs, rhs)) => {
                // lhs is x*x, rhs is x
                assert_eq!(lhs.len(), 1);
                assert_eq!(lhs[0].vars, vec!["x".to_string(), "x".to_string()]);
                assert_eq!(rhs.len(), 1);
                assert_eq!(rhs[0].vars, vec!["x".to_string()]);
            }
            _ => panic!("expected single Eq literal after disjunctive-bit rewrite"),
        }
    }

    #[test]
    fn disjunctive_bit_does_not_match_unrelated_vars() {
        // or(x = 0, y = 1) — different vars, should NOT collapse.
        let prime = BigUint::from(101u32);
        let f = Formula::Or(vec![
            Formula::Lit(Literal::Eq(vec![t(1, &["x"])], vec![t(0, &[])])),
            Formula::Lit(Literal::Eq(vec![t(1, &["y"])], vec![t(1, &[])])),
        ]);
        let rewritten = rewrite_disjunctive_bit(f, &prime);
        assert!(
            matches!(rewritten, Formula::Or(_)),
            "different vars must not collapse"
        );
    }

    #[test]
    fn solve_disjunctive_unsat() {
        // and(x = 1, or(x = 0, x = 2)) on GF(101) is UNSAT.
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
        // (=> (= x ff0) (= y ff0)), x = ff0 -> y must be 0.
        // assert x = 0 and (=> (x = 0) (y = 0)) and y != 0 → UNSAT
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
}
