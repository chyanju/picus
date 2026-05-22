//! cvc5 backend using QF_NIA (nonlinear integer arithmetic mod p).

use num_bigint::BigUint;
use std::collections::HashMap;

use crate::backends::{poly_to_smtlib_nia, SolverBackend, SolverBackendDescriptor, SolverError, SolverResult, UnknownReason};
use crate::Theory;
use picus_solver::timeout::CancelToken;
use crate::poly_ir::PolyIR;

pub struct Cvc5NiaBackend;

impl Default for Cvc5NiaBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Cvc5NiaBackend {
    pub fn new() -> Self {
        Self
    }
}

impl SolverBackend for Cvc5NiaBackend {
    fn solve(
        &mut self,
        ir: &PolyIR,
        timeout_ms: u64,
        cancel: &CancelToken,
    ) -> Result<SolverResult, SolverError> {
        // Entry-only cancellation; see comment on `Cvc5FfBackend::solve`.
        if cancel.is_cancelled() {
            return Ok(SolverResult::Unknown(UnknownReason::Timeout));
        }
        let tm = cvc5_ff::TermManager::new();
        let mut solver = cvc5_ff::Solver::new(&tm);
        solver.set_logic("QF_NIA");
        solver.set_option("produce-models", "true");
        solver.set_option("tlimit", &timeout_ms.to_string());

        let int_sort = tm.integer_sort();
        let prime = ir.ring.field.prime();
        let p_term = tm.mk_integer_from_str(&prime.to_string());
        let zero_term = tm.mk_integer(0);

        // Declare every ring variable with a `[0, p)` range constraint.
        let mut vars: HashMap<String, cvc5_ff::Term> = HashMap::new();
        for name in ir.ring.ring.var_names() {
            let v = tm.mk_const(int_sort.clone(), name);
            solver.assert_formula(
                tm.mk_term(cvc5_ff::Kind::Geq, &[v.clone(), zero_term.clone()]),
            );
            solver.assert_formula(
                tm.mk_term(cvc5_ff::Kind::Lt, &[v.clone(), p_term.clone()]),
            );
            vars.insert(name.clone(), v);
        }

        // Equalities: `(mod poly p) = 0`.
        for poly in &ir.equalities {
            let lhs = build_poly_nia(&tm, &vars, ir, poly);
            let modded = tm.mk_term(cvc5_ff::Kind::IntsModulus, &[lhs, p_term.clone()]);
            solver.assert_formula(
                tm.mk_term(cvc5_ff::Kind::Equal, &[modded, zero_term.clone()]),
            );
        }

        // Target disequality.
        let s = ir.target_signal;
        let target_x = vars.get(ir.x_name(s)).cloned();
        let target_y = vars.get(ir.y_name(s)).cloned();
        if let (Some(x), Some(y)) = (target_x, target_y) {
            let eq = tm.mk_term(cvc5_ff::Kind::Equal, &[x, y]);
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
            Ok(SolverResult::Unknown(UnknownReason::IncompleteTheory))
        }
    }

    fn dump_smt(&self, ir: &PolyIR) -> String {
        let p = ir.ring.field.prime();
        let mut lines = Vec::new();
        lines.push("(set-logic QF_NIA)".to_string());
        for name in ir.ring.ring.var_names() {
            lines.push(format!("(declare-const {} Int)", name));
            lines.push(format!("(assert (and (>= {0} 0) (< {0} {1})))", name, p));
        }
        for poly in &ir.equalities {
            lines.push(format!(
                "(assert (= (mod {} {}) 0))",
                poly_to_smtlib_nia(ir, poly),
                p
            ));
        }
        let s = ir.target_signal;
        lines.push(format!(
            "(assert (not (= {} {})))",
            ir.x_name(s),
            ir.y_name(s)
        ));
        lines.push("(check-sat)".to_string());
        lines.push("(get-model)".to_string());
        lines.join("\n")
    }
}

fn build_poly_nia<'a>(
    tm: &'a cvc5_ff::TermManager,
    vars: &HashMap<String, cvc5_ff::Term<'a>>,
    ir: &PolyIR,
    poly: &picus_solver::poly::Poly,
) -> cvc5_ff::Term<'a> {
    let mut sum_parts: Vec<cvc5_ff::Term<'a>> = Vec::new();
    for (coeff, var_names) in ir.poly_terms(poly) {
        let c = tm.mk_integer_from_str(&coeff.to_string());
        if var_names.is_empty() {
            sum_parts.push(c);
            continue;
        }
        let mut factors: Vec<cvc5_ff::Term<'a>> = Vec::with_capacity(var_names.len() + 1);
        factors.push(c);
        for n in var_names {
            factors.push(
                vars.get(&n)
                    .cloned()
                    .unwrap_or_else(|| tm.mk_const(tm.integer_sort(), &n)),
            );
        }
        sum_parts.push(tm.mk_term(cvc5_ff::Kind::Mult, &factors));
    }
    match sum_parts.len() {
        0 => tm.mk_integer(0),
        1 => sum_parts.into_iter().next().unwrap(),
        _ => tm.mk_term(cvc5_ff::Kind::Add, &sum_parts),
    }
}

inventory::submit! {
    SolverBackendDescriptor {
        name: "cvc5",
        theory: Theory::Nia,
        factory: || Box::new(Cvc5NiaBackend::new()),
    }
}
