//! Z3 backend using QF_NIA (nonlinear integer arithmetic with mod p).

use num_bigint::BigUint;
use std::collections::HashMap;
use z3::ast::Int;
use z3::{Params, SatResult, Solver};

use crate::backends::{poly_to_smtlib_nia, SolverBackend, SolverBackendDescriptor, SolverError, SolverResult, UnknownReason};
use crate::Theory;
use picus_solver::timeout::CancelToken;
use crate::poly_ir::PolyIR;

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
        ir: &PolyIR,
        timeout_ms: u64,
        cancel: &CancelToken,
    ) -> Result<SolverResult, SolverError> {
        // Entry-only cancellation; see comment on `Cvc5FfBackend::solve`.
        if cancel.is_cancelled() {
            return Ok(SolverResult::Unknown(UnknownReason::Timeout));
        }
        let solver = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", timeout_ms.min(u32::MAX as u64) as u32);
        solver.set_params(&params);

        let prime = ir.ring.field.prime();
        let p_ast = bigint(prime);

        // Declare every ring variable with a `[0, p)` range constraint.
        let mut vars: HashMap<String, Int> = HashMap::new();
        for name in ir.ring.ring.var_names() {
            let v = Int::new_const(name.as_str());
            solver.assert(v.ge(Int::from_u64(0)));
            solver.assert(v.lt(&p_ast));
            vars.insert(name.clone(), v);
        }

        // Equalities: `(rem poly p) = 0`.
        for poly in &ir.equalities {
            let sum = build_poly_z3(&vars, ir, poly);
            solver.assert(sum.rem(&p_ast).eq(Int::from_u64(0)));
        }

        // Target disequality.
        let s = ir.target_signal;
        if let (Some(x), Some(y)) = (vars.get(ir.x_name(s)), vars.get(ir.y_name(s))) {
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
            SatResult::Unknown => Ok(SolverResult::Unknown(UnknownReason::IncompleteTheory)),
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
                "(assert (= (rem {} {}) 0))",
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

fn bigint(val: &BigUint) -> Int {
    val.to_string()
        .parse::<Int>()
        .expect("BigUint should produce valid z3 Int")
}

fn build_poly_z3(vars: &HashMap<String, Int>, ir: &PolyIR, poly: &picus_solver::poly::Poly) -> Int {
    let mut sum = Int::from_u64(0);
    for (coeff, var_names) in ir.poly_terms(poly) {
        let c = bigint(&coeff);
        let mut factors: Vec<Int> = Vec::with_capacity(var_names.len() + 1);
        factors.push(c);
        for n in var_names {
            factors.push(vars.get(&n).cloned().unwrap_or_else(|| Int::new_const(n.as_str())));
        }
        let refs: Vec<&Int> = factors.iter().collect();
        let product = if refs.len() == 1 {
            factors.into_iter().next().unwrap()
        } else {
            Int::mul(&refs)
        };
        sum = Int::add(&[&sum, &product]);
    }
    sum
}

inventory::submit! {
    SolverBackendDescriptor {
        name: "z3",
        theory: Theory::Nia,
        factory: || Box::new(Z3NiaBackend::new()),
    }
}
