//! Z3 backend using QF_NIA (nonlinear integer arithmetic with mod p).

use num_bigint::BigUint;
use std::collections::HashMap;
use z3::ast::Int;
use z3::{Params, SatResult, Solver};

use crate::backends::{SolverBackend, SolverError, SolverResult};
use crate::query::*;

pub struct Z3NiaBackend;

impl Default for Z3NiaBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Z3NiaBackend {
    pub fn new() -> Self {
        Self
    }
}

impl SolverBackend for Z3NiaBackend {
    fn solve(
        &mut self,
        query: &UniquenessQuery,
        timeout_ms: u64,
    ) -> Result<SolverResult, SolverError> {
        let solver = Solver::new();

        let mut params = Params::new();
        params.set_u32("timeout", timeout_ms as u32);
        solver.set_params(&params);

        let p_ast = bigint(&query.prime);

        // Declare variables with range constraints
        let mut vars: HashMap<String, Int> = HashMap::new();

        for i in 0..query.n_wires {
            let xname = orig_var(i);
            let x = Int::new_const(xname.as_str());
            solver.assert(x.ge(Int::from_u64(0)));
            solver.assert(x.lt(&p_ast));
            vars.insert(xname, x);
        }
        for i in 0..query.n_wires {
            if !query.input_indices.contains(&i) {
                let yname = format!("y{}", i);
                let y = Int::new_const(yname.as_str());
                solver.assert(y.ge(Int::from_u64(0)));
                solver.assert(y.lt(&p_ast));
                vars.insert(yname, y);
            }
        }

        // Named constants
        for (name, val) in &query.constants {
            let c = Int::new_const(name.as_str());
            solver.assert(c.eq(bigint(val)));
            vars.insert(name.clone(), c);
        }

        // x0 = 1
        if let Some(x0) = vars.get("x0") {
            solver.assert(x0.eq(Int::from_u64(1)));
        }

        // Constraints
        for constraint in &query.orig_constraints {
            if let Some(ast) = build_constraint_z3(&vars, constraint, &p_ast) {
                solver.assert(&ast);
            }
        }
        for constraint in &query.alt_constraints {
            if let Some(ast) = build_constraint_z3(&vars, constraint, &p_ast) {
                solver.assert(&ast);
            }
        }

        // Known equalities
        for &j in &query.known_signals {
            let xname = orig_var(j);
            let yname = format!("y{}", j);
            if let (Some(x), Some(y)) = (vars.get(&xname), vars.get(&yname)) {
                solver.assert(x.eq(y));
            }
        }

        // Target inequality
        let sid = query.target_signal;
        let xname = orig_var(sid);
        let yname = format!("y{}", sid);
        if let (Some(x), Some(y)) = (vars.get(&xname), vars.get(&yname)) {
            solver.assert(x.eq(y).not());
        }

        match solver.check() {
            SatResult::Unsat => Ok(SolverResult::Unsat),
            SatResult::Sat => {
                let model = solver.get_model().expect("model unavailable after SAT");
                let mut result = HashMap::new();
                for (name, var) in &vars {
                    if let Some(val) = model.eval(var, true) {
                        let s = val.to_string();
                        if let Ok(n) = s.parse::<BigUint>() {
                            result.insert(name.clone(), n);
                        }
                    }
                }
                Ok(SolverResult::Sat(result))
            }
            SatResult::Unknown => Ok(SolverResult::Unknown),
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
            lines.push(format!("(assert {})", constraint_to_smtlib_nia(c, p)));
        }
        for c in &query.alt_constraints {
            lines.push(format!("(assert {})", constraint_to_smtlib_nia(c, p)));
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

fn bigint(val: &BigUint) -> Int {
    val.to_string().parse::<Int>().expect("BigUint should produce valid z3 Int")
}

fn build_constraint_z3(
    vars: &HashMap<String, Int>,
    constraint: &IRConstraint,
    p: &Int,
) -> Option<z3::ast::Bool> {
    match constraint {
        IRConstraint::Linear(terms) => {
            let mut sum = Int::from_u64(0);
            for term in terms {
                if let Some(v) = vars.get(&term.var) {
                    let c = bigint(&term.coeff);
                    sum = Int::add(&[&sum, &Int::mul(&[&c, v])]);
                }
            }
            Some(sum.rem(p).eq(Int::from_u64(0)))
        }
        IRConstraint::NonLinear { lhs_terms, rhs_terms } => {
            let mut lhs = Int::from_u64(0);
            for term in lhs_terms {
                if let (Some(va), Some(vb)) = (vars.get(&term.var_a), vars.get(&term.var_b)) {
                    let c = bigint(&term.coeff);
                    let product = Int::mul(&[&c, va, vb]);
                    lhs = Int::add(&[&lhs, &product]);
                }
            }
            let mut rhs = Int::from_u64(0);
            for term in rhs_terms {
                if let Some(v) = vars.get(&term.var) {
                    let c = bigint(&term.coeff);
                    rhs = Int::add(&[&rhs, &Int::mul(&[&c, v])]);
                }
            }
            Some(lhs.rem(p).eq(rhs.rem(p)))
        }
        IRConstraint::Or(subs) => {
            let bools: Vec<z3::ast::Bool> = subs
                .iter()
                .filter_map(|c| build_constraint_z3(vars, c, p))
                .collect();
            if bools.is_empty() {
                None
            } else {
                let refs: Vec<&z3::ast::Bool> = bools.iter().collect();
                Some(z3::ast::Bool::or(&refs))
            }
        }
        IRConstraint::VarEq(var, val) => {
            vars.get(var).map(|v| v.eq(bigint(val)))
        }
        IRConstraint::VarNeq(var_a, var_b) => {
            if let (Some(a), Some(b)) = (vars.get(var_a), vars.get(var_b)) {
                Some(a.eq(b).not())
            } else {
                None
            }
        }
    }
}

fn constraint_to_smtlib_nia(c: &IRConstraint, p: &BigUint) -> String {
    match c {
        IRConstraint::Linear(terms) => {
            let inner: Vec<String> = terms.iter().map(|t| format!("(* {} {})", t.coeff, t.var)).collect();
            let sum = if inner.len() == 1 { inner[0].clone() } else { format!("(+ {})", inner.join(" ")) };
            format!("(= (rem {} {}) 0)", sum, p)
        }
        IRConstraint::NonLinear { lhs_terms, rhs_terms } => {
            let lhs: Vec<String> = lhs_terms.iter().map(|t| format!("(* {} {} {})", t.coeff, t.var_a, t.var_b)).collect();
            let rhs: Vec<String> = rhs_terms.iter().map(|t| format!("(* {} {})", t.coeff, t.var)).collect();
            let lhs_str = if lhs.len() == 1 { lhs[0].clone() } else { format!("(+ {})", lhs.join(" ")) };
            let rhs_str = if rhs.is_empty() { "0".into() } else if rhs.len() == 1 { rhs[0].clone() } else { format!("(+ {})", rhs.join(" ")) };
            format!("(= (rem {} {}) (rem {} {}))", lhs_str, p, rhs_str, p)
        }
        IRConstraint::Or(subs) => {
            let inner: Vec<String> = subs.iter().map(|s| constraint_to_smtlib_nia(s, p)).collect();
            format!("(or {})", inner.join(" "))
        }
        IRConstraint::VarEq(var, val) => format!("(= {} {})", var, val),
        IRConstraint::VarNeq(a, b) => format!("(not (= {} {}))", a, b),
    }
}
