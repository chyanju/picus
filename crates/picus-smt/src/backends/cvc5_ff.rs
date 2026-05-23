//! cvc5 backend using QF_FF (native finite-field theory).
//!
//! Lowers each polynomial equality in the IR to a cvc5 `ff.add` of
//! `ff.mul` products, then asserts `(= 0 ...)`. The target wire's
//! disequality `(not (= x_t y_t))` closes the query.

use num_bigint::BigUint;
use std::collections::HashMap;

use crate::backends::{poly_to_smtlib_ff, SolverBackend, SolverBackendDescriptor, SolverError, SolverResult, UnknownReason};
use crate::Theory;
use picus_solver::timeout::CancelToken;
use crate::poly_ir::PolyIR;

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
        ir: &PolyIR,
        timeout_ms: u64,
        cancel: &CancelToken,
    ) -> Result<SolverResult, SolverError> {
        // Mid-solve cancellation requires terminating the cvc5
        // subprocess mid-call, which the `cvc5-ff` bindings do not
        // expose. The token is honoured at entry only: a
        // pre-cancelled query returns immediately, and cvc5's own
        // `tlimit` covers the wall-clock budget.
        if cancel.is_cancelled() {
            return Ok(SolverResult::Unknown(UnknownReason::Timeout));
        }
        let tm = cvc5_ff::TermManager::new();
        let mut solver = cvc5_ff::Solver::new(&tm);
        solver.set_logic("QF_FF");
        solver.set_option("produce-models", "true");
        solver.set_option("tlimit", &timeout_ms.to_string());

        let prime = ir.ring.field.prime();
        let p_str = prime.to_string();
        let ff = tm.mk_ff_sort(&p_str, 10);

        // Declare every ring variable (both `x_i` and `y_i`). The IR's
        // input equalities will collapse `x_i = y_i` for inputs during
        // solving; we don't special-case them at declaration time.
        let mut vars: HashMap<String, cvc5_ff::Term> = HashMap::new();
        for name in ir.ring.ring.var_names() {
            let v = tm.mk_const(ff.clone(), name);
            vars.insert(name.clone(), v);
        }

        let zero = tm.mk_ff_elem("0", ff.clone(), 10);

        // Equalities.
        for poly in &ir.equalities {
            let lhs = build_poly_term(&tm, &vars, ir, poly, ff.clone());
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Equal, &[lhs, zero.clone()]));
        }

        // Target disequality.
        let target_x = vars.get(ir.x_name(ir.target_signal)).cloned();
        let target_y = vars.get(ir.y_name(ir.target_signal)).cloned();
        if let (Some(x), Some(y)) = (target_x, target_y) {
            let eq = tm.mk_term(cvc5_ff::Kind::Equal, &[x, y]);
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Not, &[eq]));
        }

        // Disjunctions: clause `[p_1, ..., p_k]` ⇒ `(or (= p_1 0) ... (=
        // p_k 0))`. We hand cvc5 the `or` directly (no special-casing);
        // its QF_FF DPLL(T) does the case split. The dpvl-level target
        // disequality guard is the backstop for cvc5's known
        // `or`-spurious-SAT defect.
        for clause in &ir.disjunctions {
            let mut alts: Vec<cvc5_ff::Term> = Vec::with_capacity(clause.len());
            for poly in clause {
                let lhs = build_poly_term(&tm, &vars, ir, poly, ff.clone());
                alts.push(tm.mk_term(cvc5_ff::Kind::Equal, &[lhs, zero.clone()]));
            }
            match alts.len() {
                0 => {}
                1 => solver.assert_formula(alts.into_iter().next().unwrap()),
                _ => solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Or, &alts)),
            }
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
            // cvc5 returned `unknown` (or `timeout`). Without a way to
            // distinguish at this level we record it as `IncompleteTheory`
            // — the caller can still retry with more time.
            Ok(SolverResult::Unknown(UnknownReason::IncompleteTheory))
        }
    }

    fn dump_smt(&self, ir: &PolyIR) -> String {
        let p = ir.ring.field.prime();
        let mut lines = Vec::new();
        lines.push("(set-logic QF_FF)".to_string());
        lines.push(format!("(define-sort F () (_ FiniteField {}))", p));
        for name in ir.ring.ring.var_names() {
            lines.push(format!("(declare-const {} F)", name));
        }
        for poly in &ir.equalities {
            lines.push(format!(
                "(assert (= #f0m{} {}))",
                p,
                poly_to_smtlib_ff(ir, poly)
            ));
        }
        let s = ir.target_signal;
        lines.push(format!(
            "(assert (not (= {} {})))",
            ir.x_name(s),
            ir.y_name(s)
        ));
        for clause in &ir.disjunctions {
            let parts: Vec<String> = clause
                .iter()
                .map(|poly| format!("(= #f0m{} {})", p, poly_to_smtlib_ff(ir, poly)))
                .collect();
            match parts.len() {
                0 => {}
                1 => lines.push(format!("(assert {})", parts[0])),
                _ => lines.push(format!("(assert (or {}))", parts.join(" "))),
            }
        }
        lines.push("(check-sat)".to_string());
        lines.push("(get-model)".to_string());
        lines.join("\n")
    }
}

fn build_poly_term<'a>(
    tm: &'a cvc5_ff::TermManager,
    vars: &HashMap<String, cvc5_ff::Term<'a>>,
    ir: &PolyIR,
    poly: &picus_solver::poly::Poly,
    ff: cvc5_ff::Sort<'a>,
) -> cvc5_ff::Term<'a> {
    let mut sum_parts: Vec<cvc5_ff::Term<'a>> = Vec::new();
    for (coeff, var_names) in ir.poly_terms(poly) {
        let c = tm.mk_ff_elem(&coeff.to_string(), ff.clone(), 10);
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
                    .unwrap_or_else(|| tm.mk_const(ff.clone(), &n)),
            );
        }
        sum_parts.push(tm.mk_term(cvc5_ff::Kind::FiniteFieldMult, &factors));
    }
    match sum_parts.len() {
        0 => tm.mk_ff_elem("0", ff, 10),
        1 => sum_parts.into_iter().next().unwrap(),
        _ => tm.mk_term(cvc5_ff::Kind::FiniteFieldAdd, &sum_parts),
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

inventory::submit! {
    SolverBackendDescriptor {
        name: "cvc5",
        theory: Theory::Ff,
        factory: || Box::new(Cvc5FfBackend::new()),
    }
}
