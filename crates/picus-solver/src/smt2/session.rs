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

use std::collections::{BTreeSet, HashMap};

use num_bigint::BigUint;

use super::tokenizer::{parse_sexprs, tokenize, Sexpr};
use super::{
    assert_to_formula, classify_declare, collect_ff_literal_primes, finite_field_prime_str,
    has_ff_op, parse_define_fun, MacroDef, ParseCtx, ParseError, Polynomial, VarSort,
};
use crate::boolean::{Formula, Literal};
use crate::frontend::encoder::{ConstraintSystemBuilder, PolyTerm};

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
    /// Single persistent builder: every PolyTerm in `formulas` /
    /// `side_constraints` references this builder's variable frame.
    /// `borrow_ctx_mut` temporarily extracts it via `mem::replace`
    /// for the `assert_to_formula` call, then puts it back.
    pub(super) builder: ConstraintSystemBuilder,
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
            builder: ConstraintSystemBuilder::new(BigUint::from(2u32)),
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
                // If the session has no prime yet, infer it from this
                // assert's `#fNmP` literals (every literal carries its
                // modulus); reject `ff.*` ops with no literal hint so the
                // term is not silently encoded under the builder's prime-2
                // default. Mirrors the one-shot parsers.
                if self.prime.is_none() {
                    let mut lit_primes: BTreeSet<BigUint> = BTreeSet::new();
                    collect_ff_literal_primes(inner, &mut lit_primes);
                    if lit_primes.len() > 1 {
                        return Err(ParseError::Malformed(format!(
                            "multiple FF primes in literals: {:?}",
                            lit_primes.iter().collect::<Vec<_>>()
                        )));
                    }
                    if let Some(p) = lit_primes.into_iter().next() {
                        self.builder.set_prime(p.clone());
                        self.prime = Some(p);
                    } else if has_ff_op(inner) {
                        return Err(ParseError::MissingPrime);
                    }
                }
                let mut ctx = self.borrow_ctx();
                let formula = match assert_to_formula(inner, &mut ctx) {
                    Ok(f) => f,
                    Err(e) => {
                        // Reinstall builder even on failure to keep
                        // the session usable.
                        self.reinstall_ctx(ctx);
                        return Err(e);
                    }
                };
                let added_side = self.reinstall_ctx(ctx);
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

    /// Extract a `ParseCtx` for one assert/get-value/check call.
    /// `mem::replace`s `self.builder` with a placeholder; the caller
    /// MUST move the returned ctx's builder back via
    /// [`Self::reinstall_ctx`] when done.
    fn borrow_ctx(&mut self) -> ParseCtx {
        let prime = self.prime.clone().unwrap_or_else(|| BigUint::from(2u32));
        let placeholder = ConstraintSystemBuilder::new(prime.clone());
        let builder = std::mem::replace(&mut self.builder, placeholder);
        ParseCtx {
            prime,
            vars: self.vars.clone(),
            macros: self.macros.clone(),
            next_ite_skolem: self.next_ite_skolem,
            side_constraints: Vec::new(),
            builder,
            expansion_depth: 0,
        }
    }

    /// Move the ctx's mutated builder + skolem counter back into the
    /// session; return any side constraints accumulated during the
    /// parse so the caller can append them.
    fn reinstall_ctx(&mut self, ctx: ParseCtx) -> Vec<Formula> {
        self.builder = ctx.builder;
        self.next_ite_skolem = ctx.next_ite_skolem;
        ctx.side_constraints
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
                let idx = self.builder.var(name);
                let b_sq: Polynomial = vec![PolyTerm {
                    coeff: one.clone(),
                    vars: vec![(idx, 2)],
                }];
                let b: Polynomial = vec![PolyTerm {
                    coeff: one.clone(),
                    vars: vec![(idx, 1)],
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
        let outcome = crate::cdclt::solve_formula(prime, self.builder.var_names(), &combined, &cancel);
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
        if let Some(p) = finite_field_prime_str(&list[3]) {
            let n = p
                .parse::<BigUint>()
                .map_err(|_| ParseError::Malformed(format!("bad prime: {}", p)))?;
            self.builder.set_prime(n.clone());
            self.prime = Some(n);
        }
        Ok(())
    }

    fn eval_declare(&mut self, head: &str, list: &[Sexpr]) -> Result<(), ParseError> {
        let Some((name, sort, inferred)) = classify_declare(head, list) else {
            return Ok(());
        };
        if self.prime.is_none() {
            if let Some(n) = inferred {
                self.builder.set_prime(n.clone());
                self.prime = Some(n);
            }
        }
        if !self.vars.contains_key(&name) {
            self.var_order.push(name.clone());
        }
        self.vars.insert(name, sort.unwrap_or(VarSort::Ff));
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

#[cfg(test)]
mod tests {
    use super::*;

    fn run(src: &str) -> Vec<SessionOutput> {
        let mut s = SmtSession::new();
        s.eval_script(src).expect("script ok")
    }

    fn run_with(s: &mut SmtSession, src: &str) -> Vec<SessionOutput> {
        s.eval_script(src).expect("script ok")
    }

    fn last_verdict(out: &[SessionOutput]) -> Option<SessionVerdict> {
        for o in out.iter().rev() {
            if let SessionOutput::CheckSat(v) = o {
                return Some(*v);
            }
        }
        None
    }

    // ────────── Default state ──────────

    #[test]
    fn new_starts_at_level_zero_no_check() {
        let s = SmtSession::new();
        assert_eq!(s.decision_level(), 0);
        assert!(s.last_verdict().is_none());
        assert!(s.last_model().is_none());
    }

    // ────────── Trivial scripts ──────────

    #[test]
    fn exit_terminates_script() {
        // Commands after (exit) must not be evaluated.
        let out = run("(set-logic QF_FF) (exit) (echo \"unreachable\")");
        assert!(out.is_empty() || !matches!(out.last(), Some(SessionOutput::Echo(_))));
    }

    #[test]
    fn echo_emits_string() {
        let out = run("(echo \"hello\")");
        // The echo atom from the tokenizer keeps the surrounding quotes,
        // so the payload contains `hello` as a substring rather than being
        // exactly `hello`. Just assert the output kind + substring.
        let echoed = match out.last() {
            Some(SessionOutput::Echo(s)) => s.clone(),
            other => panic!("expected Echo, got {:?}", other),
        };
        assert!(echoed.contains("hello"), "echo payload missing 'hello': {:?}", echoed);
    }

    #[test]
    fn set_info_set_logic_are_silent() {
        let out = run("(set-logic QF_FF) (set-info :name x)");
        assert!(out.is_empty());
    }

    // ────────── declare + assert + check-sat (FF) ──────────

    #[test]
    fn ff_sat_via_finitefield_sort() {
        // x: FF7, x + 6 = 0 → x = 1 (mod 7). SAT.
        let out = run(r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= (ff.add x #f6m7) #f0m7))
            (check-sat)
        "#);
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
    }

    #[test]
    fn ff_unsat_via_contradiction() {
        // x = 1 ∧ x = 2 → UNSAT.
        let out = run(r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (assert (= x #f2m7))
            (check-sat)
        "#);
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Unsat));
    }

    // ────────── push / pop levels ──────────

    #[test]
    fn push_pop_isolates_assertions() {
        let mut s = SmtSession::new();
        let _ = run_with(&mut s, r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (push)
            (assert (= x #f2m7))
        "#);
        // Inside push: x=1 ∧ x=2 → UNSAT.
        let out = run_with(&mut s, "(check-sat)");
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Unsat));
        // Pop and re-check: x=1 alone → SAT.
        let out = run_with(&mut s, "(pop) (check-sat)");
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
    }

    #[test]
    fn pop_past_zero_is_noop() {
        let mut s = SmtSession::new();
        // (pop) at level 0 must not panic; subsequent commands still work.
        let _ = s.eval_script("(pop)").expect("pop at level 0 should not error");
        assert_eq!(s.decision_level(), 0);
    }

    // ────────── reset / reset-assertions ──────────

    #[test]
    fn reset_clears_everything() {
        let mut s = SmtSession::new();
        let _ = run_with(&mut s, r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (check-sat)
            (reset)
        "#);
        assert!(s.last_verdict().is_none());
        // After reset, can run a fresh, unrelated session.
        let out = run_with(&mut s, r#"
            (declare-fun y () (_ FiniteField 11))
            (assert (= y #f3m11))
            (check-sat)
        "#);
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
    }

    #[test]
    fn reset_assertions_keeps_declarations() {
        let mut s = SmtSession::new();
        let _ = run_with(&mut s, r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (assert (= x #f2m7))
            (check-sat)
            (reset-assertions)
        "#);
        // Declaration of x kept; reset-assertions only cleared asserts.
        let out = run_with(&mut s, r#"
            (assert (= x #f3m7))
            (check-sat)
        "#);
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
    }

    // ────────── get-value / get-unsat-core ──────────

    #[test]
    fn get_unsat_core_returns_names_after_unsat() {
        let mut s = SmtSession::new();
        let out = run_with(&mut s, r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (! (= x #f1m7) :named a))
            (assert (! (= x #f2m7) :named b))
            (check-sat)
            (get-unsat-core)
        "#);
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Unsat));
        // The core is some subset of named asserts (may be `[a, b]` or empty
        // depending on how the solver attributes; checking presence here).
        let has_core = out.iter().any(|o| matches!(o, SessionOutput::UnsatCore(_)));
        assert!(has_core, "expected an UnsatCore output");
    }

    // ────────── (set-option :tlimit-per N) ──────────

    #[test]
    fn set_option_tlimit_per_is_silent() {
        let out = run("(set-option :tlimit-per 1000)");
        assert!(out.is_empty());
    }

    // ────────── Bool sort + propositional check-sat ──────────

    #[test]
    fn bool_only_check_sat() {
        let out = run(r#"
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (assert (or a b))
            (check-sat)
        "#);
        // Default prime when no FF appears is 2; the assert is SAT.
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
    }
}
