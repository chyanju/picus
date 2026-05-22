//! Persistent SMT-LIB v2 session.
//!
//! [`SmtSession`] keeps declarations, asserts, push/pop levels, and the
//! last `check-sat` verdict across multiple top-level commands so the
//! same store can answer several `(check-sat)` queries with different
//! incremental extensions of an existing assertion set.
//!
//! Solver integration: `check-sat` lowers the accumulated `Formula`
//! into the in-tree CDCL(T) entry point [`crate::cdclt::solve_formula`].
//! Per-check timeouts honour `(set-option :tlimit-per <ms>)`.

use std::collections::HashMap;

use num_bigint::BigUint;

use super::tokenizer::{parse_sexprs, tokenize, Sexpr};
use super::{
    assert_to_formula, classify_sort, parse_define_fun, MacroDef, ParseCtx, ParseError, Polynomial,
    VarSort,
};
use crate::boolean::{Formula, Literal};
use crate::encoder::PolyTerm;

/// Verdict returned by `(check-sat)`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SessionVerdict {
    Sat,
    Unsat,
    Unknown,
}

/// One command's output. `Silent` covers commands that produce no
/// response (`set-logic`, `declare-fun`, `assert`, `push`, `pop`, …).
#[derive(Clone, Debug)]
pub enum SessionOutput {
    Silent,
    CheckSat(SessionVerdict),
    /// SMT-LIB-style model formatted as a multi-line `(...)` block.
    Model(String),
    /// `(get-value (x ...))` — one (name, formatted-value) per query.
    Values(Vec<(String, String)>),
    /// `(get-unsat-core)` — names of every `:named` assert in scope
    /// when the last [`SessionVerdict::Unsat`] was produced. Empty
    /// when the last check was SAT/Unknown or no check has run.
    UnsatCore(Vec<String>),
    /// `(echo "...")`.
    Echo(String),
}

/// Persistent SMT-LIB v2 session: parses and executes commands one
/// at a time. Supports `(push n)` / `(pop n)` checkpointing so the
/// same `(check-sat)` can be re-run against different incremental
/// extensions of an existing assertion set.
pub struct SmtSession {
    pub(super) prime: Option<BigUint>,
    pub(super) vars: HashMap<String, VarSort>,
    /// Insertion order of `declare-fun` / `declare-const`. Used for
    /// truncation on `(pop)` and for a deterministic `(get-model)`
    /// print order.
    pub(super) var_order: Vec<String>,
    pub(super) macros: HashMap<String, MacroDef>,
    pub(super) macro_order: Vec<String>,
    pub(super) formulas: Vec<Formula>,
    /// `assert_names[i]` is the `:named` label of `formulas[i]`, if
    /// any. Parallel to `formulas`; `None` for unlabelled asserts.
    pub(super) assert_names: Vec<Option<String>>,
    /// Per-check timeout in milliseconds, set by
    /// `(set-option :tlimit-per <N>)`. `None` ⇒ no timeout.
    pub(super) tlimit_per_ms: Option<u64>,
    pub(super) side_constraints: Vec<Formula>,
    pub(super) next_ite_skolem: usize,
    pub(super) levels: Vec<SessionLevel>,
    pub(super) last_check: Option<SessionVerdict>,
    pub(super) last_model: Option<HashMap<String, BigUint>>,
    /// Set after the last `(check-sat)` returned UNSAT: every
    /// `:named` assert in scope at that moment. SMT-LIB allows the
    /// core to be any sufficient subset (not necessarily minimal),
    /// so the full named-assert list is a sound conservative answer.
    pub(super) last_unsat_core_names: Vec<String>,
}

#[derive(Clone)]
pub(super) struct SessionLevel {
    var_count: usize,
    macro_count: usize,
    formula_count: usize,
    side_constraint_count: usize,
    next_ite_skolem: usize,
}

impl Default for SmtSession {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtSession {
    pub fn new() -> Self {
        SmtSession {
            prime: None,
            vars: HashMap::new(),
            var_order: Vec::new(),
            macros: HashMap::new(),
            macro_order: Vec::new(),
            formulas: Vec::new(),
            assert_names: Vec::new(),
            tlimit_per_ms: None,
            side_constraints: Vec::new(),
            next_ite_skolem: 0,
            levels: Vec::new(),
            last_check: None,
            last_model: None,
            last_unsat_core_names: Vec::new(),
        }
    }

    /// Parse and evaluate every top-level S-expression in `src`,
    /// returning the outputs of every non-silent command in order.
    /// Processing stops as soon as `(exit)` is encountered; commands
    /// after `(exit)` are not evaluated.
    pub fn eval_script(&mut self, src: &str) -> Result<Vec<SessionOutput>, ParseError> {
        let toks = tokenize(src);
        let sexprs = parse_sexprs(&toks)?;
        let mut out = Vec::new();
        for s in &sexprs {
            if is_exit(s) {
                break;
            }
            let r = self.eval(s)?;
            if !matches!(r, SessionOutput::Silent) {
                out.push(r);
            }
        }
        Ok(out)
    }

    /// Evaluate a single command. Returns `Silent` for `(exit)`;
    /// script-termination on `(exit)` is enforced by
    /// [`SmtSession::eval_script`] rather than this method.
    fn eval(&mut self, s: &Sexpr) -> Result<SessionOutput, ParseError> {
        let list = match s {
            Sexpr::List(l) => l,
            Sexpr::Atom(_) => return Ok(SessionOutput::Silent),
        };
        let head = match list.first() {
            Some(Sexpr::Atom(a)) => a.as_str(),
            _ => return Ok(SessionOutput::Silent),
        };
        match head {
            "set-logic" | "set-info" | "exit" => Ok(SessionOutput::Silent),
            "set-option" => {
                self.eval_set_option(list);
                Ok(SessionOutput::Silent)
            }
            "echo" => match list.get(1) {
                Some(Sexpr::Atom(a)) => Ok(SessionOutput::Echo(a.clone())),
                _ => Ok(SessionOutput::Echo(String::new())),
            },
            "define-sort" => {
                self.eval_define_sort(list)?;
                Ok(SessionOutput::Silent)
            }
            "declare-fun" | "declare-const" => {
                self.eval_declare(head, list)?;
                Ok(SessionOutput::Silent)
            }
            "define-fun" => {
                let (name, def) = parse_define_fun(list)?;
                if !self.macros.contains_key(&name) {
                    self.macro_order.push(name.clone());
                }
                self.macros.insert(name, def);
                Ok(SessionOutput::Silent)
            }
            "assert" => {
                if list.len() != 2 {
                    return Err(ParseError::Malformed("'assert' arity".into()));
                }
                // Recognise the SMT-LIB `(! term :named NAME)` annotation
                // wrapper. Any other attribute on `!` is silently
                // ignored; the inner term is used as the assertion.
                let (inner, name) = strip_named_annotation(&list[1]);
                let mut ctx = self.borrow_ctx();
                let formula = assert_to_formula(inner, &mut ctx)?;
                let added_side = ctx.side_constraints.split_off(0);
                let new_ite_count = ctx.next_ite_skolem;
                drop(ctx);
                self.next_ite_skolem = new_ite_count;
                self.formulas.push(formula);
                self.assert_names.push(name);
                self.side_constraints.extend(added_side);
                Ok(SessionOutput::Silent)
            }
            "push" => {
                let n = list
                    .get(1)
                    .and_then(|s| if let Sexpr::Atom(a) = s { a.parse::<usize>().ok() } else { None })
                    .unwrap_or(1);
                for _ in 0..n {
                    self.push();
                }
                Ok(SessionOutput::Silent)
            }
            "pop" => {
                let n = list
                    .get(1)
                    .and_then(|s| if let Sexpr::Atom(a) = s { a.parse::<usize>().ok() } else { None })
                    .unwrap_or(1);
                for _ in 0..n {
                    self.pop();
                }
                Ok(SessionOutput::Silent)
            }
            "check-sat" => Ok(SessionOutput::CheckSat(self.check_sat())),
            "get-model" => Ok(SessionOutput::Model(self.format_model())),
            "get-value" => {
                let values = self.eval_get_value(list)?;
                Ok(SessionOutput::Values(values))
            }
            "get-unsat-core" => {
                Ok(SessionOutput::UnsatCore(self.last_unsat_core_names.clone()))
            }
            "reset" => {
                // `(reset)` clears everything — declarations,
                // options, the logic, push trail, asserts.
                *self = SmtSession::new();
                Ok(SessionOutput::Silent)
            }
            "reset-assertions" => {
                // `(reset-assertions)` clears the assertion stack
                // and the push trail but keeps declarations, macros,
                // the prime, and options (per SMT-LIB v2 §4.2.1).
                self.formulas.clear();
                self.assert_names.clear();
                self.side_constraints.clear();
                self.levels.clear();
                self.last_check = None;
                self.last_model = None;
                self.last_unsat_core_names.clear();
                Ok(SessionOutput::Silent)
            }
            _ => Ok(SessionOutput::Silent),
        }
    }

    /// Last `(check-sat)` verdict, if any.
    pub fn last_verdict(&self) -> Option<SessionVerdict> {
        self.last_check
    }

    /// Last SAT model, if any.
    pub fn last_model(&self) -> Option<&HashMap<String, BigUint>> {
        self.last_model.as_ref()
    }

    /// Number of active push levels.
    pub fn decision_level(&self) -> usize {
        self.levels.len()
    }

    fn borrow_ctx(&self) -> ParseCtx {
        ParseCtx {
            prime: self.prime.clone().unwrap_or_else(|| BigUint::from(2u32)),
            vars: self.vars.clone(),
            macros: self.macros.clone(),
            next_ite_skolem: self.next_ite_skolem,
            side_constraints: Vec::new(),
        }
    }

    fn push(&mut self) {
        self.levels.push(SessionLevel {
            var_count: self.var_order.len(),
            macro_count: self.macro_order.len(),
            formula_count: self.formulas.len(),
            side_constraint_count: self.side_constraints.len(),
            next_ite_skolem: self.next_ite_skolem,
        });
        // Invalidate any cached check-sat — semantics changed.
        self.last_check = None;
        self.last_model = None;
        self.last_unsat_core_names.clear();
    }

    fn pop(&mut self) {
        let lvl = match self.levels.pop() {
            Some(l) => l,
            None => return,
        };
        for name in self.var_order.drain(lvl.var_count..) {
            self.vars.remove(&name);
        }
        for name in self.macro_order.drain(lvl.macro_count..) {
            self.macros.remove(&name);
        }
        self.formulas.truncate(lvl.formula_count);
        self.assert_names.truncate(lvl.formula_count);
        self.side_constraints.truncate(lvl.side_constraint_count);
        self.next_ite_skolem = lvl.next_ite_skolem;
        self.last_check = None;
        self.last_model = None;
        self.last_unsat_core_names.clear();
    }

    fn check_sat(&mut self) -> SessionVerdict {
        let mut all: Vec<Formula> = self.formulas.clone();
        all.extend(self.side_constraints.iter().cloned());
        // Auto bit constraint for every declared Bool var. Iterate
        // `var_order` (not `self.vars`) so the constraint sequence is
        // deterministic across runs — HashMap iteration order is not.
        let one = BigUint::from(1u32);
        for name in &self.var_order {
            if matches!(self.vars.get(name), Some(VarSort::Bool)) {
                let b_sq: Polynomial = vec![PolyTerm {
                    coeff: one.clone(),
                    vars: vec![name.clone(), name.clone()],
                }];
                let b: Polynomial = vec![PolyTerm {
                    coeff: one.clone(),
                    vars: vec![name.clone()],
                }];
                all.push(Formula::Lit(Literal::Eq(b_sq, b)));
            }
        }
        let combined = if all.is_empty() {
            Formula::True
        } else if all.len() == 1 {
            all.pop().unwrap()
        } else {
            Formula::And(all)
        };
        let prime = self.prime.clone().unwrap_or_else(|| BigUint::from(2u32));
        let cancel = match self.tlimit_per_ms {
            Some(ms) => crate::timeout::CancelToken::with_timeout(
                std::time::Duration::from_millis(ms),
            ),
            None => crate::timeout::CancelToken::none(),
        };
        let outcome = crate::cdclt::solve_formula(prime, &combined, &cancel);
        match outcome {
            crate::core::SolveOutcome::Sat(model) => {
                self.last_check = Some(SessionVerdict::Sat);
                self.last_model = Some(model);
                self.last_unsat_core_names.clear();
                SessionVerdict::Sat
            }
            crate::core::SolveOutcome::Unsat(_) => {
                self.last_check = Some(SessionVerdict::Unsat);
                self.last_model = None;
                // SMT-LIB allows any sufficient subset; report every
                // `:named` assert in scope (sound, possibly broader
                // than minimal). Without per-assert deps tracing the
                // solver-side core can't be narrowed any further here.
                self.last_unsat_core_names = self
                    .assert_names
                    .iter()
                    .filter_map(|n| n.clone())
                    .collect();
                SessionVerdict::Unsat
            }
            crate::core::SolveOutcome::Unknown => {
                self.last_check = Some(SessionVerdict::Unknown);
                self.last_model = None;
                self.last_unsat_core_names.clear();
                SessionVerdict::Unknown
            }
        }
    }

    fn eval_set_option(&mut self, list: &[Sexpr]) {
        // `(set-option :tlimit-per <ms>)` — per-check timeout. Other
        // options are accepted silently.
        let mut i = 1;
        while i < list.len() {
            if let Sexpr::Atom(k) = &list[i] {
                if k == ":tlimit-per" {
                    if let Some(Sexpr::Atom(v)) = list.get(i + 1) {
                        if let Ok(n) = v.parse::<u64>() {
                            self.tlimit_per_ms = if n == 0 { None } else { Some(n) };
                        }
                    }
                    i += 2;
                    continue;
                }
                if k.starts_with(':') {
                    i += 2;
                    continue;
                }
            }
            i += 1;
        }
    }

    fn eval_define_sort(&mut self, list: &[Sexpr]) -> Result<(), ParseError> {
        if list.len() < 4 {
            return Ok(());
        }
        let body = &list[3];
        if let Sexpr::List(inner) = body {
            if inner.len() == 3 {
                if let (Sexpr::Atom(u), Sexpr::Atom(ff), Sexpr::Atom(p)) =
                    (&inner[0], &inner[1], &inner[2])
                {
                    if u == "_" && ff == "FiniteField" {
                        let n = p.parse::<BigUint>().map_err(|_| {
                            ParseError::Malformed(format!("bad prime: {}", p))
                        })?;
                        self.prime = Some(n);
                    }
                }
            }
        }
        Ok(())
    }

    fn eval_declare(&mut self, head: &str, list: &[Sexpr]) -> Result<(), ParseError> {
        if list.len() < 2 {
            return Ok(());
        }
        let name = match &list[1] {
            Sexpr::Atom(n) => n.clone(),
            _ => return Ok(()),
        };
        let sort_sexpr = if head == "declare-fun" {
            list.get(3)
        } else {
            list.get(2)
        };
        let sort = classify_sort(sort_sexpr).unwrap_or(VarSort::Ff);
        if self.prime.is_none() {
            if let Some(Sexpr::List(inner)) = sort_sexpr {
                if inner.len() == 3 {
                    if let (Sexpr::Atom(u), Sexpr::Atom(ff), Sexpr::Atom(p)) =
                        (&inner[0], &inner[1], &inner[2])
                    {
                        if u == "_" && ff == "FiniteField" {
                            if let Ok(n) = p.parse::<BigUint>() {
                                self.prime = Some(n);
                            }
                        }
                    }
                }
            }
        }
        if !self.vars.contains_key(&name) {
            self.var_order.push(name.clone());
        }
        self.vars.insert(name, sort);
        Ok(())
    }

    fn eval_get_value(&self, list: &[Sexpr]) -> Result<Vec<(String, String)>, ParseError> {
        let model = match &self.last_model {
            Some(m) => m,
            None => return Ok(Vec::new()),
        };
        let queries = match list.get(1) {
            Some(Sexpr::List(items)) => items,
            _ => return Ok(Vec::new()),
        };
        let mut out = Vec::new();
        for q in queries {
            if let Sexpr::Atom(name) = q {
                // Skip names not declared in the session — fabricating
                // a zero value would silently misreport the model.
                let sort = match self.vars.get(name) {
                    Some(s) => *s,
                    None => continue,
                };
                let val = model.get(name).cloned().unwrap_or_default();
                out.push((name.clone(), format_value(&val, sort, self.prime.as_ref())));
            }
        }
        Ok(out)
    }

    fn format_model(&self) -> String {
        let model = match &self.last_model {
            Some(m) => m,
            None => return "(\n)".to_string(),
        };
        let zero = BigUint::from(0u32);
        let mut out = String::from("(\n");
        for name in &self.var_order {
            let val = model.get(name).unwrap_or(&zero);
            let sort = self.vars.get(name).copied().unwrap_or(VarSort::Ff);
            out.push_str("  ");
            out.push_str(&format_define_fun(name, val, sort, self.prime.as_ref()));
            out.push('\n');
        }
        out.push(')');
        out
    }
}

/// `(exit)` head match — used by [`SmtSession::eval_script`] to
/// stop processing further commands.
fn is_exit(s: &Sexpr) -> bool {
    match s {
        Sexpr::List(l) => matches!(l.first(), Some(Sexpr::Atom(a)) if a == "exit"),
        _ => false,
    }
}

/// If `s` matches `(! inner :named NAME [other :attr value ...])`,
/// return `(inner, Some(NAME))`. The annotation may carry additional
/// `:key value` pairs that are ignored. Any other shape — including a
/// `!` wrapper without `:named` — returns `(s, None)` with the inner
/// term in place.
fn strip_named_annotation(s: &Sexpr) -> (&Sexpr, Option<String>) {
    let list = match s {
        Sexpr::List(l) => l,
        _ => return (s, None),
    };
    if list.len() < 2 {
        return (s, None);
    }
    let head = match list.first() {
        Some(Sexpr::Atom(a)) => a,
        _ => return (s, None),
    };
    if head != "!" {
        return (s, None);
    }
    let inner = &list[1];
    let mut name: Option<String> = None;
    let mut i = 2;
    while i < list.len() {
        if let Sexpr::Atom(k) = &list[i] {
            if k == ":named" {
                if let Some(Sexpr::Atom(v)) = list.get(i + 1) {
                    name = Some(v.clone());
                }
                i += 2;
                continue;
            }
            if k.starts_with(':') {
                // Generic attribute with a value: skip both tokens.
                i += 2;
                continue;
            }
        }
        i += 1;
    }
    (inner, name)
}

fn format_value(val: &BigUint, sort: VarSort, prime: Option<&BigUint>) -> String {
    match sort {
        VarSort::Bool => {
            if val == &BigUint::from(0u32) { "false".into() } else { "true".into() }
        }
        VarSort::Ff => match prime {
            Some(p) => format!("#f{}m{}", val, p),
            None => format!("{}", val),
        },
    }
}

fn format_define_fun(
    name: &str,
    val: &BigUint,
    sort: VarSort,
    prime: Option<&BigUint>,
) -> String {
    match sort {
        VarSort::Bool => format!(
            "(define-fun {} () Bool {})",
            name,
            format_value(val, sort, prime)
        ),
        VarSort::Ff => match prime {
            Some(p) => format!(
                "(define-fun {} () (_ FiniteField {}) {})",
                name,
                p,
                format_value(val, sort, prime)
            ),
            None => format!("(define-fun {} () _ {})", name, val),
        },
    }
}

impl SessionOutput {
    /// SMT-LIB-compatible textual form. `Silent` returns an empty
    /// string; other variants emit one or more lines matching the
    /// expected response shape.
    pub fn to_smtlib(&self) -> String {
        match self {
            SessionOutput::Silent => String::new(),
            SessionOutput::CheckSat(SessionVerdict::Sat) => "sat".into(),
            SessionOutput::CheckSat(SessionVerdict::Unsat) => "unsat".into(),
            SessionOutput::CheckSat(SessionVerdict::Unknown) => "unknown".into(),
            SessionOutput::Model(s) => s.clone(),
            SessionOutput::Values(vs) => {
                let mut s = String::from("(");
                for (i, (n, v)) in vs.iter().enumerate() {
                    if i > 0 {
                        s.push('\n');
                        s.push(' ');
                    }
                    s.push_str(&format!("({} {})", n, v));
                }
                s.push(')');
                s
            }
            SessionOutput::UnsatCore(names) => {
                let mut s = String::from("(");
                for (i, n) in names.iter().enumerate() {
                    if i > 0 {
                        s.push(' ');
                    }
                    s.push_str(n);
                }
                s.push(')');
                s
            }
            SessionOutput::Echo(t) => format!("\"{}\"", t),
        }
    }
}
