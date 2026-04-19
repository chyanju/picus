//! CVC5 backend using QF_FF (native finite field theory).

use num_bigint::BigUint;
use std::collections::HashMap;

use crate::backends::{SolverBackend, SolverError, SolverResult};
use crate::query::*;

pub struct Cvc5FfBackend;

impl Default for Cvc5FfBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Cvc5FfBackend {
    pub fn new() -> Self {
        Self
    }
}

impl SolverBackend for Cvc5FfBackend {
    fn solve(
        &mut self,
        query: &UniquenessQuery,
        timeout_ms: u64,
    ) -> Result<SolverResult, SolverError> {
        let tm = cvc5::TermManager::new();
        let mut solver = cvc5::Solver::new(&tm);
        solver.set_logic("QF_FF");
        solver.set_option("produce-models", "true");
        solver.set_option("tlimit", &timeout_ms.to_string());

        let p_str = query.prime.to_string();
        let ff = tm.mk_ff_sort(&p_str, 10);

        let mut vars: HashMap<String, cvc5::Term> = HashMap::new();

        // Declare all variables
        for i in 0..query.n_wires {
            let xname = orig_var(i);
            let x = tm.mk_const(ff.clone(), &xname);
            vars.insert(xname, x);
        }
        for i in 0..query.n_wires {
            if !query.input_indices.contains(&i) {
                let yname = format!("y{}", i);
                let y = tm.mk_const(ff.clone(), &yname);
                vars.insert(yname, y);
            }
        }

        // Named constants
        for (name, val) in &query.constants {
            let c = tm.mk_const(ff.clone(), name);
            let val_term = tm.mk_ff_elem(&val.to_string(), ff.clone(), 10);
            solver.assert_formula(tm.mk_term(cvc5::Kind::Equal, &[c.clone(), val_term]));
            vars.insert(name.clone(), c);
        }

        // x0 = 1
        let one = tm.mk_ff_elem("1", ff.clone(), 10);
        if let Some(x0) = vars.get("x0") {
            solver.assert_formula(tm.mk_term(cvc5::Kind::Equal, &[x0.clone(), one]));
        }

        // Constraints
        for constraint in &query.orig_constraints {
            if let Some(ast) = build_constraint_ff(&tm, &vars, constraint, ff.clone()) {
                solver.assert_formula(ast);
            }
        }
        for constraint in &query.alt_constraints {
            if let Some(ast) = build_constraint_ff(&tm, &vars, constraint, ff.clone()) {
                solver.assert_formula(ast);
            }
        }

        // Known equalities
        for &j in &query.known_signals {
            let xname = orig_var(j);
            let yname = format!("y{}", j);
            if let (Some(x), Some(y)) = (vars.get(&xname), vars.get(&yname)) {
                solver.assert_formula(tm.mk_term(cvc5::Kind::Equal, &[x.clone(), y.clone()]));
            }
        }

        // Target inequality
        let sid = query.target_signal;
        let xname = orig_var(sid);
        let yname = format!("y{}", sid);
        if let (Some(x), Some(y)) = (vars.get(&xname), vars.get(&yname)) {
            let eq = tm.mk_term(cvc5::Kind::Equal, &[x.clone(), y.clone()]);
            solver.assert_formula(tm.mk_term(cvc5::Kind::Not, &[eq]));
        }

        let result = solver.check_sat();
        if result.is_unsat() {
            Ok(SolverResult::Unsat)
        } else if result.is_sat() {
            let mut model = HashMap::new();
            for (name, var) in &vars {
                let val = solver.get_value(var.clone());
                let val_str = val.to_string();
                if let Some(n) = parse_ff_value(&val_str) {
                    model.insert(name.clone(), n);
                }
            }
            Ok(SolverResult::Sat(model))
        } else {
            Ok(SolverResult::Unknown)
        }
    }

    fn dump_smt(&self, query: &UniquenessQuery) -> String {
        let p = &query.prime;
        let mut lines = Vec::new();

        lines.push("(set-logic QF_FF)".to_string());
        lines.push(format!("(define-sort F () (_ FiniteField {}))", p));

        for (name, val) in &query.constants {
            lines.push(format!("(declare-const {} F)", name));
            lines.push(format!("(assert (= {} #f{}m{}))", name, val, p));
        }

        for i in 0..query.n_wires {
            lines.push(format!("(declare-const x{} F)", i));
        }
        for i in 0..query.n_wires {
            if !query.input_indices.contains(&i) {
                lines.push(format!("(declare-const y{} F)", i));
            }
        }

        lines.push(format!("(assert (= x0 #f1m{}))", p));

        for c in &query.orig_constraints {
            lines.push(format!("(assert {})", constraint_to_smtlib_ff(c, p)));
        }
        for c in &query.alt_constraints {
            lines.push(format!("(assert {})", constraint_to_smtlib_ff(c, p)));
        }

        for &j in &query.known_signals {
            if !query.input_indices.contains(&j) {
                lines.push(format!("(assert (= x{} y{}))", j, j));
            }
        }

        let sid = query.target_signal;
        lines.push(format!("(assert (not (= x{} y{})))", sid, sid));
        lines.push("(check-sat)".to_string());
        lines.push("(get-model)".to_string());

        lines.join("\n")
    }
}

fn build_constraint_ff<'a>(
    tm: &'a cvc5::TermManager,
    vars: &HashMap<String, cvc5::Term<'a>>,
    constraint: &IRConstraint,
    ff: cvc5::Sort<'a>,
) -> Option<cvc5::Term<'a>> {
    match constraint {
        IRConstraint::Linear(terms) => {
            let zero = tm.mk_ff_elem("0", ff.clone(), 10);
            let sum = build_ff_linear_sum(tm, vars, terms, ff)?;
            Some(tm.mk_term(cvc5::Kind::Equal, &[sum, zero]))
        }
        IRConstraint::NonLinear { lhs_terms, rhs_terms } => {
            let zero = tm.mk_ff_elem("0", ff.clone(), 10);
            let mut lhs_parts = Vec::new();
            for term in lhs_terms {
                let c = tm.mk_ff_elem(&term.coeff.to_string(), ff.clone(), 10);
                let va = vars.get(&term.var_a)?.clone();
                let vb = vars.get(&term.var_b)?.clone();
                lhs_parts.push(tm.mk_term(cvc5::Kind::FiniteFieldMult, &[c, va, vb]));
            }
            let lhs = ff_add_terms(tm, &lhs_parts, ff.clone());

            let rhs = if rhs_terms.is_empty() {
                zero
            } else {
                build_ff_linear_sum(tm, vars, rhs_terms, ff)?
            };

            Some(tm.mk_term(cvc5::Kind::Equal, &[lhs, rhs]))
        }
        IRConstraint::Or(subs) => {
            let terms: Vec<cvc5::Term> = subs
                .iter()
                .filter_map(|c| build_constraint_ff(tm, vars, c, ff.clone()))
                .collect();
            match terms.len() {
                0 => None,
                1 => Some(terms.into_iter().next().unwrap()),
                _ => Some(tm.mk_term(cvc5::Kind::Or, &terms)),
            }
        }
        IRConstraint::VarEq(var, val) => {
            let v = vars.get(var)?.clone();
            let val_term = tm.mk_ff_elem(&val.to_string(), ff, 10);
            Some(tm.mk_term(cvc5::Kind::Equal, &[v, val_term]))
        }
        IRConstraint::VarNeq(var_a, var_b) => {
            let a = vars.get(var_a)?.clone();
            let b = vars.get(var_b)?.clone();
            let eq = tm.mk_term(cvc5::Kind::Equal, &[a, b]);
            Some(tm.mk_term(cvc5::Kind::Not, &[eq]))
        }
    }
}

fn build_ff_linear_sum<'a>(
    tm: &'a cvc5::TermManager,
    vars: &HashMap<String, cvc5::Term<'a>>,
    terms: &[IRTerm],
    ff: cvc5::Sort<'a>,
) -> Option<cvc5::Term<'a>> {
    let mut parts = Vec::new();
    for term in terms {
        let c = tm.mk_ff_elem(&term.coeff.to_string(), ff.clone(), 10);
        let v = vars.get(&term.var)?.clone();
        parts.push(tm.mk_term(cvc5::Kind::FiniteFieldMult, &[c, v]));
    }
    Some(ff_add_terms(tm, &parts, ff))
}

fn ff_add_terms<'a>(
    tm: &'a cvc5::TermManager,
    parts: &[cvc5::Term<'a>],
    ff: cvc5::Sort<'a>,
) -> cvc5::Term<'a> {
    match parts.len() {
        0 => tm.mk_ff_elem("0", ff, 10),
        1 => parts[0].clone(),
        _ => tm.mk_term(cvc5::Kind::FiniteFieldAdd, parts),
    }
}

fn constraint_to_smtlib_ff(c: &IRConstraint, p: &BigUint) -> String {
    match c {
        IRConstraint::Linear(terms) => {
            let inner: Vec<String> = terms
                .iter()
                .map(|t| format!("(ff.mul #f{}m{} {})", t.coeff, p, t.var))
                .collect();
            let sum = if inner.len() == 1 { inner[0].clone() } else { format!("(ff.add {})", inner.join(" ")) };
            format!("(= #f0m{} {})", p, sum)
        }
        IRConstraint::NonLinear { lhs_terms, rhs_terms } => {
            let lhs: Vec<String> = lhs_terms.iter().map(|t| format!("(ff.mul #f{}m{} {} {})", t.coeff, p, t.var_a, t.var_b)).collect();
            let rhs: Vec<String> = rhs_terms.iter().map(|t| format!("(ff.mul #f{}m{} {})", t.coeff, p, t.var)).collect();
            let lhs_str = if lhs.len() == 1 { lhs[0].clone() } else { format!("(ff.add {})", lhs.join(" ")) };
            let rhs_str = if rhs.is_empty() { format!("#f0m{}", p) } else if rhs.len() == 1 { rhs[0].clone() } else { format!("(ff.add {})", rhs.join(" ")) };
            format!("(= {} {})", lhs_str, rhs_str)
        }
        IRConstraint::Or(subs) => {
            let inner: Vec<String> = subs.iter().map(|s| constraint_to_smtlib_ff(s, p)).collect();
            format!("(or {})", inner.join(" "))
        }
        IRConstraint::VarEq(var, val) => format!("(= {} #f{}m{})", var, val, p),
        IRConstraint::VarNeq(a, b) => format!("(not (= {} {}))", a, b),
    }
}

fn parse_ff_value(s: &str) -> Option<BigUint> {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix("#f") {
        let m_pos = rest.find('m')?;
        rest[..m_pos].parse().ok()
    } else {
        s.parse().ok()
    }
}
