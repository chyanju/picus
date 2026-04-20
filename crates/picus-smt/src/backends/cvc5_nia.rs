//! CVC5 backend using QF_NIA (nonlinear integer arithmetic with mod p).

use num_bigint::BigUint;
use std::collections::HashMap;

use crate::backends::{SolverBackend, SolverError, SolverResult};
use crate::query::*;

pub struct Cvc5NiaBackend;

impl Default for Cvc5NiaBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Cvc5NiaBackend {
    pub fn new() -> Self { Self }
}

impl SolverBackend for Cvc5NiaBackend {
    fn solve(&mut self, query: &UniquenessQuery, timeout_ms: u64) -> Result<SolverResult, SolverError> {
        let tm = cvc5_ff::TermManager::new();
        let mut solver = cvc5_ff::Solver::new(&tm);
        solver.set_logic("QF_NIA");
        solver.set_option("produce-models", "true");
        solver.set_option("tlimit", &timeout_ms.to_string());

        let int_sort = tm.integer_sort();
        let p_term = tm.mk_integer_from_str(&query.prime.to_string());
        let zero_term = tm.mk_integer(0);
        let one_term = tm.mk_integer(1);

        let mut vars: HashMap<String, cvc5_ff::Term> = HashMap::new();

        for i in 0..query.n_wires {
            let xname = orig_var(i);
            let x = tm.mk_const(int_sort.clone(), &xname);
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Geq, &[x.clone(), zero_term.clone()]));
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Lt, &[x.clone(), p_term.clone()]));
            vars.insert(xname, x);
        }
        for i in 0..query.n_wires {
            if !query.input_indices.contains(&i) {
                let yname = format!("y{}", i);
                let y = tm.mk_const(int_sort.clone(), &yname);
                solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Geq, &[y.clone(), zero_term.clone()]));
                solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Lt, &[y.clone(), p_term.clone()]));
                vars.insert(yname, y);
            }
        }

        for (name, val) in &query.constants {
            let c = tm.mk_const(int_sort.clone(), name);
            let val_term = tm.mk_integer_from_str(&val.to_string());
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Equal, &[c.clone(), val_term]));
            vars.insert(name.clone(), c);
        }

        if let Some(x0) = vars.get("x0") {
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Equal, &[x0.clone(), one_term]));
        }

        for constraint in &query.orig_constraints {
            if let Some(ast) = build_constraint_nia(&tm, &vars, constraint, &p_term, &zero_term) {
                solver.assert_formula(ast);
            }
        }
        for constraint in &query.alt_constraints {
            if let Some(ast) = build_constraint_nia(&tm, &vars, constraint, &p_term, &zero_term) {
                solver.assert_formula(ast);
            }
        }

        for &j in &query.known_signals {
            let xname = orig_var(j);
            let yname = format!("y{}", j);
            if let (Some(x), Some(y)) = (vars.get(&xname), vars.get(&yname)) {
                solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Equal, &[x.clone(), y.clone()]));
            }
        }

        let sid = query.target_signal;
        let xname = orig_var(sid);
        let yname = format!("y{}", sid);
        if let (Some(x), Some(y)) = (vars.get(&xname), vars.get(&yname)) {
            let eq = tm.mk_term(cvc5_ff::Kind::Equal, &[x.clone(), y.clone()]);
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Not, &[eq]));
        }

        let result = solver.check_sat();
        if result.is_unsat() {
            Ok(SolverResult::Unsat)
        } else if result.is_sat() {
            let mut model = HashMap::new();
            for (name, var) in &vars {
                let val = solver.get_value(var.clone());
                if let Ok(n) = val.to_string().parse::<BigUint>() {
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
        lines.push("(set-logic QF_NIA)".to_string());
        for (name, val) in &query.constants {
            lines.push(format!("(declare-const {} Int)", name));
            lines.push(format!("(assert (= {} {}))", name, val));
        }
        for i in 0..query.n_wires {
            lines.push(format!("(declare-const x{} Int)", i));
            lines.push(format!("(assert (and (>= x{0} 0) (< x{0} {1})))", i, p));
        }
        for i in 0..query.n_wires {
            if !query.input_indices.contains(&i) {
                lines.push(format!("(declare-const y{} Int)", i));
                lines.push(format!("(assert (and (>= y{0} 0) (< y{0} {1})))", i, p));
            }
        }
        lines.push("(assert (= x0 1))".to_string());
        for c in &query.orig_constraints {
            lines.push(format!("(assert {})", super::constraint_to_smtlib_nia(c, p, "mod")));
        }
        for c in &query.alt_constraints {
            lines.push(format!("(assert {})", super::constraint_to_smtlib_nia(c, p, "mod")));
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

fn build_constraint_nia<'a>(
    tm: &'a cvc5_ff::TermManager,
    vars: &HashMap<String, cvc5_ff::Term<'a>>,
    constraint: &IRConstraint,
    p: &cvc5_ff::Term<'a>,
    zero: &cvc5_ff::Term<'a>,
) -> Option<cvc5_ff::Term<'a>> {
    match constraint {
        IRConstraint::Linear(terms) => {
            let sum = build_nia_sum(tm, vars, terms)?;
            let modded = tm.mk_term(cvc5_ff::Kind::IntsModulus, &[sum, p.clone()]);
            Some(tm.mk_term(cvc5_ff::Kind::Equal, &[modded, zero.clone()]))
        }
        IRConstraint::NonLinear { lhs_terms, rhs_terms } => {
            let mut lhs_parts = Vec::new();
            for term in lhs_terms {
                let c = tm.mk_integer_from_str(&term.coeff.to_string());
                let va = vars.get(&term.var_a)?.clone();
                let vb = vars.get(&term.var_b)?.clone();
                lhs_parts.push(tm.mk_term(cvc5_ff::Kind::Mult, &[c, va, vb]));
            }
            let lhs = match lhs_parts.len() {
                1 => lhs_parts.into_iter().next().unwrap(),
                _ => tm.mk_term(cvc5_ff::Kind::Add, &lhs_parts),
            };
            let rhs = if rhs_terms.is_empty() { zero.clone() } else { build_nia_sum(tm, vars, rhs_terms)? };
            let lhs_mod = tm.mk_term(cvc5_ff::Kind::IntsModulus, &[lhs, p.clone()]);
            let rhs_mod = tm.mk_term(cvc5_ff::Kind::IntsModulus, &[rhs, p.clone()]);
            Some(tm.mk_term(cvc5_ff::Kind::Equal, &[lhs_mod, rhs_mod]))
        }
        IRConstraint::Or(subs) => {
            let terms: Vec<cvc5_ff::Term> = subs.iter().filter_map(|c| build_constraint_nia(tm, vars, c, p, zero)).collect();
            match terms.len() {
                0 => None,
                1 => Some(terms.into_iter().next().unwrap()),
                _ => Some(tm.mk_term(cvc5_ff::Kind::Or, &terms)),
            }
        }
        IRConstraint::VarEq(var, val) => {
            let v = vars.get(var)?.clone();
            Some(tm.mk_term(cvc5_ff::Kind::Equal, &[v, tm.mk_integer_from_str(&val.to_string())]))
        }
        IRConstraint::VarNeq(var_a, var_b) => {
            let a = vars.get(var_a)?.clone();
            let b = vars.get(var_b)?.clone();
            let eq = tm.mk_term(cvc5_ff::Kind::Equal, &[a, b]);
            Some(tm.mk_term(cvc5_ff::Kind::Not, &[eq]))
        }
    }
}

fn build_nia_sum<'a>(
    tm: &'a cvc5_ff::TermManager,
    vars: &HashMap<String, cvc5_ff::Term<'a>>,
    terms: &[IRTerm],
) -> Option<cvc5_ff::Term<'a>> {
    let mut parts = Vec::new();
    for term in terms {
        let c = tm.mk_integer_from_str(&term.coeff.to_string());
        let v = vars.get(&term.var)?.clone();
        parts.push(tm.mk_term(cvc5_ff::Kind::Mult, &[c, v]));
    }
    match parts.len() {
        0 => Some(tm.mk_integer(0)),
        1 => Some(parts.into_iter().next().unwrap()),
        _ => Some(tm.mk_term(cvc5_ff::Kind::Add, &parts)),
    }
}

