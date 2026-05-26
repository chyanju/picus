//! SMT-LIB v2 parser for QF_FF + Boolean structure.
//!
//! Sorts: `F` (or `(_ FiniteField N)`) and `Bool`.
//! Field ops: `ff.add`/`+`, `ff.mul`/`*`, `ff.neg`/unary `-`, `(as ffN F)`.
//! Constants: `ffN`, `#fNmP`, decimal integers (reduced mod prime).
//! Boolean ops: `and`, `or`, `not`, `=>`, `xor`, `ite` (both Bool- and
//! term-level), n-ary `=` (FF equality chain or Bool iff), `distinct`,
//! `define-fun` macros.
//!
//! [`parse`] handles the conjunctive subset and returns a
//! [`ConstraintSystem`]; Boolean connectives in `(assert ...)` are
//! rejected with [`ParseError::BooleanInAssert`].
//!
//! [`parse_boolean`] handles the full structure above and returns a
//! [`crate::boolean::BooleanQuery`]. Term-level `(ite c x y)` over FF
//! terms is skolem-eliminated into a fresh FF variable plus two
//! conditional equalities at the formula level.
//!
//! Both entry points thread a single `ConstraintSystemBuilder`
//! through the AST recursion: every leaf-variable reference goes
//! through `builder.var(name)` so the parser emits index-keyed
//! `Vec<PolyTerm>` directly with no separate intern step.

mod session;
mod tokenizer;

pub use session::{SessionOutput, SessionVerdict, SmtSession};

use std::collections::{BTreeMap, HashMap};
use std::fmt;

use num_bigint::BigUint;
use num_traits::Zero;

use crate::frontend::encoder::{ConstraintSystemBuilder, ConstraintSystem, PolyTerm, VarIdx};
use tokenizer::{parse_sexprs, tokenize, Sexpr};

// ─────────────────────── Errors ──────────────────────────────────────────

/// Errors produced by [`parse`].
#[derive(Debug, Clone)]
pub enum ParseError {
    /// Unexpected token at top level.
    UnexpectedToken(String),
    /// FF operator not in the supported subset.
    UnknownOperator(String),
    /// Identifier referenced before declaration.
    UnknownSymbol(String),
    /// Boolean connective (`and`/`or`/`=>`/`ite`) appeared inside `(assert ...)`.
    BooleanInAssert(String),
    /// `(assert ...)` appeared before `(define-sort F () (_ FiniteField N))` or
    /// any `(declare-fun x () (_ FiniteField N))`.
    MissingPrime,
    /// Top-level form malformed (wrong arity, unexpected shape, etc.).
    Malformed(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnexpectedToken(s) => write!(f, "unexpected token: {}", s),
            ParseError::UnknownOperator(s) => write!(f, "unsupported FF operator: {}", s),
            ParseError::UnknownSymbol(s) => write!(f, "unknown symbol: {}", s),
            ParseError::BooleanInAssert(s) => {
                write!(f, "boolean operator '{}' inside assert (QF_FF only)", s)
            }
            ParseError::MissingPrime => write!(f, "assert before any FF sort declaration"),
            ParseError::Malformed(s) => write!(f, "malformed form: {}", s),
        }
    }
}

impl std::error::Error for ParseError {}

// ─────────────────────── Sort tracking ───────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::smt2) enum VarSort {
    Ff,
    Bool,
}

#[derive(Debug, Clone)]
pub(in crate::smt2) struct MacroDef {
    params: Vec<(String, VarSort)>,
    body: Sexpr,
}

/// Classify a sort s-expression as `Ff`, `Bool`, or unknown.
pub(in crate::smt2) fn classify_sort(s: Option<&Sexpr>) -> Option<VarSort> {
    let sexpr = s?;
    match sexpr {
        Sexpr::Atom(a) => match a.as_str() {
            "Bool" => Some(VarSort::Bool),
            "F" => Some(VarSort::Ff),
            _ => None,
        },
        Sexpr::List(inner) => {
            if inner.len() == 3 {
                if let (Sexpr::Atom(u), Sexpr::Atom(ff), Sexpr::Atom(_)) =
                    (&inner[0], &inner[1], &inner[2])
                {
                    if u == "_" && ff == "FiniteField" {
                        return Some(VarSort::Ff);
                    }
                }
            }
            None
        }
    }
}

// ─────────────────────── Polynomial-expression builder ───────────────────

pub(in crate::smt2) type Polynomial = Vec<PolyTerm>;

fn neg_poly(p: &Polynomial, prime: &BigUint) -> Polynomial {
    p.iter()
        .map(|t| PolyTerm {
            coeff: if t.coeff.is_zero() {
                BigUint::zero()
            } else {
                prime - &t.coeff
            },
            vars: t.vars.clone(),
        })
        .collect()
}

fn add_polys(a: Polynomial, b: Polynomial) -> Polynomial {
    let mut out = a;
    out.extend(b);
    out
}

/// Multiply two `Vec<PolyTerm>` lists. For each cross-product
/// `t_a * t_b`, merge exponents per variable via `BTreeMap` (so
/// `x*x` stays as `(x_idx, 2)` rather than two `(x_idx, 1)` entries).
fn mul_polys(a: &Polynomial, b: &Polynomial, prime: &BigUint) -> Polynomial {
    let mut out = Vec::with_capacity(a.len() * b.len());
    for ta in a {
        for tb in b {
            let coeff = (&ta.coeff * &tb.coeff) % prime;
            if coeff.is_zero() {
                continue;
            }
            let mut counts: BTreeMap<VarIdx, u16> = BTreeMap::new();
            // Accumulate per-variable exponents with `checked_add`, matching the
            // engine's u16-exponent discipline (monomial.rs / polynomial.rs):
            // an `ff.mul` chain raising one variable past 65535 panics (caught
            // at the backend boundary → Unknown) rather than silently wrapping
            // to a wrong exponent and mistranslating the polynomial.
            for &(idx, exp) in ta.vars.iter().chain(tb.vars.iter()) {
                let e = counts.entry(idx).or_insert(0);
                *e = e
                    .checked_add(exp)
                    .expect("SMT2 monomial exponent exceeds u16");
            }
            out.push(PolyTerm {
                coeff,
                vars: counts.into_iter().collect(),
            });
        }
    }
    out
}

/// Parse `ffN`, `ff-N`, `#fNmP`, or `#f-NmP` constant. Negative forms
/// return `(p - N) mod p`. Returns `None` for non-constant symbols.
fn parse_ff_const(sym: &str, prime: &BigUint) -> Option<BigUint> {
    let parse_signed = |rest: &str| -> Option<BigUint> {
        let neg = rest.starts_with('-');
        let body = if neg { &rest[1..] } else { rest };
        let n: BigUint = body.parse().ok()?;
        let n_mod = &n % prime;
        Some(if neg && !n_mod.is_zero() {
            prime - n_mod
        } else {
            n_mod
        })
    };
    if let Some(rest) = sym.strip_prefix("ff") {
        // Reject `ff.add`, `ff.mul`, etc.; only ff-followed-by-digit-or-minus.
        if rest.is_empty() || rest.starts_with('.') {
            return None;
        }
        return parse_signed(rest);
    }
    if let Some(rest) = sym.strip_prefix("#f") {
        let mut split = rest.splitn(2, 'm');
        let n_str = split.next()?;
        let _ = split.next()?;
        return parse_signed(n_str);
    }
    None
}

fn build_poly(
    s: &Sexpr,
    prime: &BigUint,
    vars: &HashMap<String, VarSort>,
    builder: &mut ConstraintSystemBuilder,
) -> Result<Polynomial, ParseError> {
    match s {
        Sexpr::Atom(a) => {
            if let Some(c) = parse_ff_const(a, prime) {
                return Ok(vec![PolyTerm { coeff: c, vars: vec![] }]);
            }
            if let Ok(c) = a.parse::<BigUint>() {
                return Ok(vec![PolyTerm { coeff: c % prime, vars: vec![] }]);
            }
            match vars.get(a) {
                None => Err(ParseError::UnknownSymbol(a.clone())),
                Some(VarSort::Bool) => Err(ParseError::Malformed(format!(
                    "Bool variable '{}' used in FF term context",
                    a
                ))),
                Some(VarSort::Ff) => {
                    let idx = builder.var(a);
                    Ok(vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![(idx, 1)],
                    }])
                }
            }
        }
        Sexpr::List(elts) => {
            let head = match elts.first() {
                Some(Sexpr::Atom(a)) => a.as_str(),
                _ => return Err(ParseError::Malformed("non-atom head".into())),
            };
            match head {
                "as" => {
                    if elts.len() != 3 {
                        return Err(ParseError::Malformed("'as' arity".into()));
                    }
                    let sym = match &elts[1] {
                        Sexpr::Atom(a) => a,
                        _ => return Err(ParseError::Malformed("'as' first arg".into())),
                    };
                    let c = parse_ff_const(sym, prime)
                        .ok_or_else(|| ParseError::Malformed(format!("bad 'as' constant: {}", sym)))?;
                    Ok(vec![PolyTerm { coeff: c, vars: vec![] }])
                }
                "ff.add" | "+" => {
                    let mut acc: Polynomial = Vec::new();
                    for child in &elts[1..] {
                        let p = build_poly(child, prime, vars, builder)?;
                        acc = add_polys(acc, p);
                    }
                    Ok(acc)
                }
                "ff.bitsum" => {
                    let mut acc: Polynomial = Vec::new();
                    let mut weight = BigUint::from(1u32);
                    let two = BigUint::from(2u32);
                    for child in &elts[1..] {
                        let p = build_poly(child, prime, vars, builder)?;
                        let weighted: Polynomial = p
                            .into_iter()
                            .map(|t| PolyTerm {
                                coeff: (&t.coeff * &weight) % prime,
                                vars: t.vars,
                            })
                            .collect();
                        acc = add_polys(acc, weighted);
                        weight = (&weight * &two) % prime;
                    }
                    Ok(acc)
                }
                "ff.mul" | "*" => {
                    let mut acc: Polynomial = vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![],
                    }];
                    for child in &elts[1..] {
                        let p = build_poly(child, prime, vars, builder)?;
                        acc = mul_polys(&acc, &p, prime);
                    }
                    Ok(acc)
                }
                "ff.neg" => {
                    if elts.len() != 2 {
                        return Err(ParseError::Malformed("'ff.neg' arity".into()));
                    }
                    let p = build_poly(&elts[1], prime, vars, builder)?;
                    Ok(neg_poly(&p, prime))
                }
                "-" if elts.len() == 2 => {
                    let p = build_poly(&elts[1], prime, vars, builder)?;
                    Ok(neg_poly(&p, prime))
                }
                "-" => {
                    let mut acc = build_poly(&elts[1], prime, vars, builder)?;
                    for child in &elts[2..] {
                        let p = build_poly(child, prime, vars, builder)?;
                        acc = add_polys(acc, neg_poly(&p, prime));
                    }
                    Ok(acc)
                }
                other => Err(ParseError::UnknownOperator(other.into())),
            }
        }
    }
}

// ─────────────────────── Assert handler ──────────────────────────────────

fn handle_assert(
    s: &Sexpr,
    prime: &BigUint,
    vars: &HashMap<String, VarSort>,
    builder: &mut ConstraintSystemBuilder,
    diseq_zero_pinned: &mut bool,
    diseq_counter: &mut usize,
) -> Result<(), ParseError> {
    let list = match s {
        Sexpr::List(l) => l,
        _ => return Err(ParseError::Malformed("non-list assert body".into())),
    };
    let head = match list.first() {
        Some(Sexpr::Atom(a)) => a.as_str(),
        _ => return Err(ParseError::Malformed("non-atom head in assert".into())),
    };
    match head {
        "=" => {
            if list.len() != 3 {
                return Err(ParseError::Malformed("'=' arity".into()));
            }
            let a = build_poly(&list[1], prime, vars, builder)?;
            let b = build_poly(&list[2], prime, vars, builder)?;
            let poly = add_polys(a, neg_poly(&b, prime));
            builder.add_equality(poly);
            Ok(())
        }
        "not" => {
            if list.len() != 2 {
                return Err(ParseError::Malformed("'not' arity".into()));
            }
            let inner = match &list[1] {
                Sexpr::List(l) => l,
                _ => return Err(ParseError::Malformed("'not' inner".into())),
            };
            let inner_head = match inner.first() {
                Some(Sexpr::Atom(a)) => a.as_str(),
                _ => return Err(ParseError::Malformed("'not' inner head".into())),
            };
            if inner_head != "=" {
                return Err(ParseError::Malformed(format!(
                    "(not <X>) only supports (not (= a b)); got (not ({} ..))",
                    inner_head
                )));
            }
            if inner.len() != 3 {
                return Err(ParseError::Malformed("inner '=' arity".into()));
            }
            let a = build_poly(&inner[1], prime, vars, builder)?;
            let b = build_poly(&inner[2], prime, vars, builder)?;

            // d = a - b; assert d != 0 via the disequality list.
            let d_name = format!("__diseq_d_{}", diseq_counter);
            *diseq_counter += 1;
            let d_idx = builder.var(&d_name);
            let zero_idx = builder.var("__zero");
            if !*diseq_zero_pinned {
                builder.add_assignment(zero_idx, BigUint::zero());
                *diseq_zero_pinned = true;
            }
            let mut def: Vec<PolyTerm> = vec![PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(d_idx, 1)],
            }];
            def.extend(neg_poly(&a, prime));
            def.extend(b);
            builder.add_equality(def);
            builder.add_disequality(d_idx, zero_idx);
            Ok(())
        }
        "and" | "or" | "=>" | "ite" => Err(ParseError::BooleanInAssert(head.into())),
        other => Err(ParseError::Malformed(format!(
            "unsupported assert head '{}'",
            other
        ))),
    }
}

// ─────────────────────── Top-level loop ──────────────────────────────────

/// Parse an SMT-LIB v2 QF_FF source and produce a
/// [`ConstraintSystem`]. Threads a single `ConstraintSystemBuilder`
/// through `build_poly` so each variable reference is interned in
/// encounter order; the indexed rewriter canonicalises every
/// equality at the end.
pub fn parse(src: &str) -> Result<ConstraintSystem, ParseError> {
    let toks = tokenize(src);
    let sexprs = parse_sexprs(&toks)?;

    // First pass: collect prime + declared variables.
    let mut prime: Option<BigUint> = None;
    let mut vars: HashMap<String, VarSort> = HashMap::new();

    for s in &sexprs {
        let list = match s {
            Sexpr::List(l) => l,
            Sexpr::Atom(_) => continue,
        };
        if list.is_empty() {
            continue;
        }
        let head = match list.first() {
            Some(Sexpr::Atom(a)) => a.as_str(),
            _ => continue,
        };
        match head {
            "set-logic" | "set-info" | "set-option" | "check-sat" | "exit" | "get-model"
            | "push" | "pop" | "echo" | "assert" => {}
            "define-sort" => {
                if list.len() < 4 {
                    continue;
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
                                prime = Some(n);
                            }
                        }
                    }
                }
            }
            "declare-fun" | "declare-const" => {
                if list.len() < 2 {
                    continue;
                }
                let name = match &list[1] {
                    Sexpr::Atom(n) => n.clone(),
                    _ => continue,
                };
                let sort_sexpr = if head == "declare-fun" {
                    list.get(3)
                } else {
                    list.get(2)
                };
                let sort = classify_sort(sort_sexpr);
                if matches!(sort, Some(VarSort::Bool)) {
                    return Err(ParseError::Malformed(format!(
                        "Bool sort '{}' not supported by conjunctive parser; use parse_boolean",
                        name
                    )));
                }
                vars.insert(name, VarSort::Ff);
                if prime.is_none() {
                    if let Some(Sexpr::List(inner)) = sort_sexpr {
                        if inner.len() == 3 {
                            if let (Sexpr::Atom(u), Sexpr::Atom(ff), Sexpr::Atom(p)) =
                                (&inner[0], &inner[1], &inner[2])
                            {
                                if u == "_" && ff == "FiniteField" {
                                    if let Ok(n) = p.parse::<BigUint>() {
                                        prime = Some(n);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    let prime_val = prime.ok_or(ParseError::MissingPrime)?;
    let mut builder = ConstraintSystemBuilder::new(prime_val.clone());
    let mut diseq_counter = 0usize;
    let mut diseq_zero_pinned = false;

    // Second pass: handle asserts now that the builder is ready.
    for s in &sexprs {
        let list = match s {
            Sexpr::List(l) => l,
            Sexpr::Atom(_) => continue,
        };
        let head = match list.first() {
            Some(Sexpr::Atom(a)) => a.as_str(),
            _ => continue,
        };
        if head == "assert" {
            if list.len() != 2 {
                return Err(ParseError::Malformed("'assert' arity".into()));
            }
            handle_assert(
                &list[1],
                &prime_val,
                &vars,
                &mut builder,
                &mut diseq_zero_pinned,
                &mut diseq_counter,
            )?;
        }
    }

    let mut indexed = builder.build();
    crate::frontend::rewriter::rewrite_system(&mut indexed);
    Ok(indexed)
}

// ─────────────────────── Boolean structure parser ────────────────────────

use crate::boolean::{BooleanQuery, Formula, Literal};

/// Parser state for `parse_boolean`. Threads through
/// `assert_to_formula` and `build_poly_with_ctx`, hosting the
/// builder that owns the query's variable frame; every FF-typed
/// leaf reference goes through `builder.var(name)`.
pub(in crate::smt2) struct ParseCtx {
    prime: BigUint,
    vars: HashMap<String, VarSort>,
    macros: HashMap<String, MacroDef>,
    /// Counter for `__ite_N` skolems introduced by term-level `ite`.
    next_ite_skolem: usize,
    /// Constraints generated as side effects (e.g. term-level `ite`).
    /// AND-conjoined into the final formula at the top of
    /// `parse_boolean`.
    side_constraints: Vec<Formula>,
    /// Query-level builder; owned here, donated to `BooleanQuery`
    /// at the end of `parse_boolean`.
    builder: ConstraintSystemBuilder,
}

impl ParseCtx {
    fn fresh_ite_var(&mut self) -> String {
        let name = format!("__ite_{}", self.next_ite_skolem);
        self.next_ite_skolem += 1;
        self.vars.insert(name.clone(), VarSort::Ff);
        name
    }

    /// Resolve a macro call by alpha-substituting arguments into the body.
    fn expand_macro(&self, name: &str, args: &[Sexpr]) -> Result<Sexpr, ParseError> {
        let m = self
            .macros
            .get(name)
            .ok_or_else(|| ParseError::UnknownOperator(name.into()))?;
        if args.len() != m.params.len() {
            return Err(ParseError::Malformed(format!(
                "macro '{}' expects {} args, got {}",
                name,
                m.params.len(),
                args.len()
            )));
        }
        let mut bindings: HashMap<String, Sexpr> = HashMap::new();
        for ((p, _), a) in m.params.iter().zip(args.iter()) {
            bindings.insert(p.clone(), a.clone());
        }
        Ok(substitute_sexpr(&m.body, &bindings))
    }
}

fn substitute_sexpr(s: &Sexpr, bindings: &HashMap<String, Sexpr>) -> Sexpr {
    match s {
        Sexpr::Atom(a) => bindings.get(a).cloned().unwrap_or_else(|| s.clone()),
        Sexpr::List(elts) => {
            Sexpr::List(elts.iter().map(|e| substitute_sexpr(e, bindings)).collect())
        }
    }
}

/// Heuristic Bool-context detector: does the expression `s` produce a
/// Bool value (rather than an FF term)? Used to dispatch `=` to iff
/// vs. FF equality, and to detect Bool ite vs term ite.
fn is_bool_expr(s: &Sexpr, ctx: &ParseCtx) -> bool {
    match s {
        Sexpr::Atom(a) => {
            if a == "true" || a == "false" {
                return true;
            }
            matches!(ctx.vars.get(a), Some(VarSort::Bool))
        }
        Sexpr::List(elts) => match elts.first() {
            Some(Sexpr::Atom(h)) => match h.as_str() {
                "and" | "or" | "not" | "=>" | "xor" | "=" | "distinct" | "true" | "false" => true,
                "ite" if elts.len() == 4 => is_bool_expr(&elts[2], ctx),
                name => {
                    // Macro: classify by body.
                    if let Some(m) = ctx.macros.get(name) {
                        is_bool_expr(&m.body, ctx)
                    } else {
                        false
                    }
                }
            },
            _ => false,
        },
    }
}

/// Build an FF polynomial recursively. Threads `ctx.builder` so
/// every FF-typed leaf reference goes through `builder.var(name)`,
/// producing index-keyed `Vec<PolyTerm>` directly.
fn build_poly_with_ctx(s: &Sexpr, ctx: &mut ParseCtx) -> Result<Polynomial, ParseError> {
    match s {
        Sexpr::Atom(a) => {
            if let Some(c) = parse_ff_const(a, &ctx.prime) {
                return Ok(vec![PolyTerm { coeff: c, vars: vec![] }]);
            }
            if let Ok(c) = a.parse::<BigUint>() {
                return Ok(vec![PolyTerm {
                    coeff: c % &ctx.prime,
                    vars: vec![],
                }]);
            }
            match ctx.vars.get(a) {
                None => Err(ParseError::UnknownSymbol(a.clone())),
                Some(VarSort::Bool) => Err(ParseError::Malformed(format!(
                    "Bool variable '{}' used in FF term context",
                    a
                ))),
                Some(VarSort::Ff) => {
                    let idx = ctx.builder.var(a);
                    Ok(vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![(idx, 1)],
                    }])
                }
            }
        }
        Sexpr::List(elts) => {
            let head = match elts.first() {
                Some(Sexpr::Atom(a)) => a.as_str(),
                _ => return Err(ParseError::Malformed("non-atom head in FF term".into())),
            };
            match head {
                "ite" if elts.len() == 4 => {
                    let cond = assert_to_formula(&elts[1], ctx)?;
                    let then_poly = build_poly_with_ctx(&elts[2], ctx)?;
                    let else_poly = build_poly_with_ctx(&elts[3], ctx)?;
                    let r_name = ctx.fresh_ite_var();
                    let r_idx = ctx.builder.var(&r_name);
                    let r_poly: Polynomial = vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![(r_idx, 1)],
                    }];
                    ctx.side_constraints.push(Formula::Or(vec![
                        Formula::Not(Box::new(cond.clone())),
                        Formula::Lit(Literal::Eq(r_poly.clone(), then_poly)),
                    ]));
                    ctx.side_constraints.push(Formula::Or(vec![
                        cond,
                        Formula::Lit(Literal::Eq(r_poly.clone(), else_poly)),
                    ]));
                    Ok(r_poly)
                }
                "as" => {
                    if elts.len() != 3 {
                        return Err(ParseError::Malformed("'as' arity".into()));
                    }
                    let sym = match &elts[1] {
                        Sexpr::Atom(a) => a,
                        _ => return Err(ParseError::Malformed("'as' first arg".into())),
                    };
                    let c = parse_ff_const(sym, &ctx.prime).ok_or_else(|| {
                        ParseError::Malformed(format!("bad 'as' constant: {}", sym))
                    })?;
                    Ok(vec![PolyTerm { coeff: c, vars: vec![] }])
                }
                "ff.add" | "+" => {
                    let mut acc: Polynomial = Vec::new();
                    for child in &elts[1..] {
                        let p = build_poly_with_ctx(child, ctx)?;
                        acc = add_polys(acc, p);
                    }
                    Ok(acc)
                }
                "ff.bitsum" => {
                    let mut acc: Polynomial = Vec::new();
                    let mut weight = BigUint::from(1u32);
                    let two = BigUint::from(2u32);
                    let prime = ctx.prime.clone();
                    for child in &elts[1..] {
                        let p = build_poly_with_ctx(child, ctx)?;
                        let weighted: Polynomial = p
                            .into_iter()
                            .map(|t| PolyTerm {
                                coeff: (&t.coeff * &weight) % &prime,
                                vars: t.vars,
                            })
                            .collect();
                        acc = add_polys(acc, weighted);
                        weight = (&weight * &two) % &prime;
                    }
                    Ok(acc)
                }
                "ff.mul" | "*" => {
                    let mut acc: Polynomial = vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![],
                    }];
                    for child in &elts[1..] {
                        let p = build_poly_with_ctx(child, ctx)?;
                        acc = mul_polys(&acc, &p, &ctx.prime);
                    }
                    Ok(acc)
                }
                "ff.neg" => {
                    if elts.len() != 2 {
                        return Err(ParseError::Malformed("'ff.neg' arity".into()));
                    }
                    let p = build_poly_with_ctx(&elts[1], ctx)?;
                    let prime = ctx.prime.clone();
                    Ok(neg_poly(&p, &prime))
                }
                "-" if elts.len() == 2 => {
                    let p = build_poly_with_ctx(&elts[1], ctx)?;
                    let prime = ctx.prime.clone();
                    Ok(neg_poly(&p, &prime))
                }
                "-" => {
                    let mut acc = build_poly_with_ctx(&elts[1], ctx)?;
                    let prime = ctx.prime.clone();
                    for child in &elts[2..] {
                        let p = build_poly_with_ctx(child, ctx)?;
                        acc = add_polys(acc, neg_poly(&p, &prime));
                    }
                    Ok(acc)
                }
                name => {
                    if ctx.macros.contains_key(name) {
                        let expanded = ctx.expand_macro(name, &elts[1..])?;
                        return build_poly_with_ctx(&expanded, ctx);
                    }
                    Err(ParseError::UnknownOperator(name.into()))
                }
            }
        }
    }
}

/// Build the iff of `bools` as `(¬b_i ∨ b_{i+1}) ∧ (b_i ∨ ¬b_{i+1})`
/// chained for `n ≥ 2`.
fn bool_chain_iff(bools: Vec<Formula>) -> Formula {
    if bools.len() < 2 {
        return Formula::True;
    }
    let mut clauses: Vec<Formula> = Vec::with_capacity((bools.len() - 1) * 2);
    for i in 0..bools.len() - 1 {
        let a = bools[i].clone();
        let b = bools[i + 1].clone();
        clauses.push(Formula::Or(vec![
            Formula::Not(Box::new(a.clone())),
            b.clone(),
        ]));
        clauses.push(Formula::Or(vec![Formula::Not(Box::new(b)), a]));
    }
    Formula::And(clauses)
}

/// FF equality chain `(= t_0 t_1 ... t_{n-1})` → conjunction of
/// `t_0 = t_1, t_1 = t_2, ..., t_{n-2} = t_{n-1}`. The binary case
/// returns a bare `Formula::Lit` (no `And` wrapper) so downstream
/// rewrites that pattern-match on `Or((Lit, Lit))` still fire.
fn ff_equality_chain(ts: &[Polynomial]) -> Formula {
    if ts.len() < 2 {
        return Formula::True;
    }
    if ts.len() == 2 {
        return Formula::Lit(Literal::Eq(ts[0].clone(), ts[1].clone()));
    }
    let mut eqs: Vec<Formula> = Vec::with_capacity(ts.len() - 1);
    for i in 0..ts.len() - 1 {
        eqs.push(Formula::Lit(Literal::Eq(ts[i].clone(), ts[i + 1].clone())));
    }
    Formula::And(eqs)
}

/// `(xor b_1 ... b_n)`: True iff an odd number of the `b_i` are True.
/// Built as a left-associative chain of binary `xor`.
fn build_xor(bools: Vec<Formula>) -> Formula {
    if bools.is_empty() {
        return Formula::False;
    }
    let mut iter = bools.into_iter();
    let mut acc = iter.next().unwrap();
    for b in iter {
        // a ⊕ b = (a ∧ ¬b) ∨ (¬a ∧ b)
        acc = Formula::Or(vec![
            Formula::And(vec![acc.clone(), Formula::Not(Box::new(b.clone()))]),
            Formula::And(vec![Formula::Not(Box::new(acc)), b]),
        ]);
    }
    acc
}

pub(in crate::smt2) fn assert_to_formula(s: &Sexpr, ctx: &mut ParseCtx) -> Result<Formula, ParseError> {
    match s {
        Sexpr::Atom(a) => match a.as_str() {
            "true" => return Ok(Formula::True),
            "false" => return Ok(Formula::False),
            name => match ctx.vars.get(name) {
                Some(VarSort::Bool) => {
                    // Treat a Bool variable atom as the predicate `b = 1`,
                    // wrapped in an Eq literal so downstream Tseitin /
                    // mutex handling sees a consistent shape. Note Bool
                    // vars live in the polynomial namespace too — they
                    // are FF-typed at the encoder layer with the SAT
                    // engine enforcing 0/1 via mutex clauses elsewhere.
                    let idx = ctx.builder.var(name);
                    let one: Polynomial = vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![],
                    }];
                    let b: Polynomial = vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![(idx, 1)],
                    }];
                    return Ok(Formula::Lit(Literal::Eq(b, one)));
                }
                Some(VarSort::Ff) => {
                    return Err(ParseError::Malformed(format!(
                        "FF variable '{}' used in Bool context",
                        name
                    )));
                }
                None => {
                    return Err(ParseError::UnknownSymbol(name.into()));
                }
            },
        },
        Sexpr::List(_) => {}
    }
    let list = match s {
        Sexpr::List(l) => l,
        _ => unreachable!(),
    };
    let head = match list.first() {
        Some(Sexpr::Atom(a)) => a.as_str(),
        _ => return Err(ParseError::Malformed("non-atom head in assert".into())),
    };
    match head {
        "true" => Ok(Formula::True),
        "false" => Ok(Formula::False),
        "=" => {
            if list.len() < 3 {
                return Err(ParseError::Malformed("'=' arity".into()));
            }
            let bool_args = is_bool_expr(&list[1], ctx);
            if bool_args {
                let mut bools: Vec<Formula> = Vec::with_capacity(list.len() - 1);
                for c in &list[1..] {
                    bools.push(assert_to_formula(c, ctx)?);
                }
                Ok(bool_chain_iff(bools))
            } else {
                let mut polys: Vec<Polynomial> = Vec::with_capacity(list.len() - 1);
                for c in &list[1..] {
                    polys.push(build_poly_with_ctx(c, ctx)?);
                }
                Ok(ff_equality_chain(&polys))
            }
        }
        "distinct" => {
            if list.len() < 3 {
                return Err(ParseError::Malformed("'distinct' arity".into()));
            }
            let bool_args = is_bool_expr(&list[1], ctx);
            if bool_args {
                let mut bools: Vec<Formula> = Vec::with_capacity(list.len() - 1);
                for c in &list[1..] {
                    bools.push(assert_to_formula(c, ctx)?);
                }
                if bools.len() > 2 {
                    return Ok(Formula::False);
                }
                // distinct(a, b) = ¬iff(a, b) = xor(a, b)
                Ok(build_xor(bools))
            } else {
                let mut polys: Vec<Polynomial> = Vec::with_capacity(list.len() - 1);
                for c in &list[1..] {
                    polys.push(build_poly_with_ctx(c, ctx)?);
                }
                let mut clauses: Vec<Formula> =
                    Vec::with_capacity(polys.len() * (polys.len() - 1) / 2);
                for i in 0..polys.len() {
                    for j in (i + 1)..polys.len() {
                        clauses.push(Formula::Lit(Literal::Neq(
                            polys[i].clone(),
                            polys[j].clone(),
                        )));
                    }
                }
                if clauses.len() == 1 {
                    Ok(clauses.pop().unwrap())
                } else {
                    Ok(Formula::And(clauses))
                }
            }
        }
        "not" => {
            if list.len() != 2 {
                return Err(ParseError::Malformed("'not' arity".into()));
            }
            let inner = assert_to_formula(&list[1], ctx)?;
            Ok(Formula::Not(Box::new(inner)))
        }
        "and" => {
            let mut children = Vec::with_capacity(list.len() - 1);
            for c in &list[1..] {
                children.push(assert_to_formula(c, ctx)?);
            }
            Ok(Formula::And(children))
        }
        "or" => {
            let mut children = Vec::with_capacity(list.len() - 1);
            for c in &list[1..] {
                children.push(assert_to_formula(c, ctx)?);
            }
            Ok(Formula::Or(children))
        }
        "xor" => {
            let mut bools: Vec<Formula> = Vec::with_capacity(list.len() - 1);
            for c in &list[1..] {
                bools.push(assert_to_formula(c, ctx)?);
            }
            Ok(build_xor(bools))
        }
        "=>" => {
            if list.len() < 3 {
                return Err(ParseError::Malformed("'=>' arity".into()));
            }
            let mut tail = assert_to_formula(list.last().unwrap(), ctx)?;
            for ant in list[1..list.len() - 1].iter().rev() {
                let a = assert_to_formula(ant, ctx)?;
                tail = Formula::Or(vec![Formula::Not(Box::new(a)), tail]);
            }
            Ok(tail)
        }
        "ite" => {
            if list.len() != 4 {
                return Err(ParseError::Malformed("'ite' arity".into()));
            }
            let then_is_bool = is_bool_expr(&list[2], ctx);
            if !then_is_bool {
                // Term-level ite at the assertion site: assertion is
                // `(ite c x y)` itself, which doesn't yield a Bool.
                return Err(ParseError::Malformed(
                    "term-level ite cannot appear directly as an assertion".into(),
                ));
            }
            let c = assert_to_formula(&list[1], ctx)?;
            let t = assert_to_formula(&list[2], ctx)?;
            let e = assert_to_formula(&list[3], ctx)?;
            Ok(Formula::Or(vec![
                Formula::And(vec![c.clone(), t]),
                Formula::And(vec![Formula::Not(Box::new(c)), e]),
            ]))
        }
        other => {
            // Macro? Expand and recurse.
            if ctx.macros.contains_key(other) {
                let expanded = ctx.expand_macro(other, &list[1..])?;
                return assert_to_formula(&expanded, ctx);
            }
            Err(ParseError::Malformed(format!(
                "unsupported assert head '{}'",
                other
            )))
        }
    }
}

/// Parse `(define-fun name ((p1 T1) ...) ret_T body)` into a `MacroDef`.
pub(in crate::smt2) fn parse_define_fun(list: &[Sexpr]) -> Result<(String, MacroDef), ParseError> {
    // (define-fun NAME ((p1 T1) (p2 T2) ...) RET BODY)
    if list.len() != 5 {
        return Err(ParseError::Malformed(
            "'define-fun' expects (name params ret body)".into(),
        ));
    }
    let name = match &list[1] {
        Sexpr::Atom(n) => n.clone(),
        _ => return Err(ParseError::Malformed("define-fun name must be atom".into())),
    };
    let params_list = match &list[2] {
        Sexpr::List(l) => l,
        _ => return Err(ParseError::Malformed("define-fun params must be a list".into())),
    };
    let mut params: Vec<(String, VarSort)> = Vec::with_capacity(params_list.len());
    for p in params_list {
        let p_list = match p {
            Sexpr::List(l) => l,
            _ => return Err(ParseError::Malformed("define-fun param must be (name sort)".into())),
        };
        if p_list.len() != 2 {
            return Err(ParseError::Malformed("define-fun param arity".into()));
        }
        let pname = match &p_list[0] {
            Sexpr::Atom(n) => n.clone(),
            _ => return Err(ParseError::Malformed("define-fun param name".into())),
        };
        let psort = classify_sort(Some(&p_list[1])).unwrap_or(VarSort::Ff);
        params.push((pname, psort));
    }
    let body = list[4].clone();
    Ok((name, MacroDef { params, body }))
}

/// Parse an SMT-LIB v2 QF_FF source with full Boolean structure.
pub fn parse_boolean(src: &str) -> Result<BooleanQuery, ParseError> {
    let toks = tokenize(src);
    let sexprs = parse_sexprs(&toks)?;

    let mut prime: Option<BigUint> = None;
    let mut vars: HashMap<String, VarSort> = HashMap::new();
    let mut macros: HashMap<String, MacroDef> = HashMap::new();
    let mut formulas: Vec<Formula> = Vec::new();

    // First pass: collect prime, declarations, and macros.
    for s in &sexprs {
        let list = match s {
            Sexpr::List(l) => l,
            Sexpr::Atom(_) => continue,
        };
        if list.is_empty() {
            continue;
        }
        let head = match list.first() {
            Some(Sexpr::Atom(a)) => a.as_str(),
            _ => continue,
        };
        match head {
            "set-logic" | "set-info" | "set-option" | "check-sat" | "exit" | "get-model"
            | "push" | "pop" | "echo" => {}
            "define-sort" => {
                if list.len() < 4 {
                    continue;
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
                                prime = Some(n);
                            }
                        }
                    }
                }
            }
            "declare-fun" | "declare-const" => {
                if list.len() < 2 {
                    continue;
                }
                let name = match &list[1] {
                    Sexpr::Atom(n) => n.clone(),
                    _ => continue,
                };
                let sort_sexpr = if head == "declare-fun" {
                    list.get(3)
                } else {
                    list.get(2)
                };
                let sort = classify_sort(sort_sexpr).unwrap_or(VarSort::Ff);
                vars.insert(name, sort);
                if prime.is_none() {
                    if let Some(Sexpr::List(inner)) = sort_sexpr {
                        if inner.len() == 3 {
                            if let (Sexpr::Atom(u), Sexpr::Atom(ff), Sexpr::Atom(p)) =
                                (&inner[0], &inner[1], &inner[2])
                            {
                                if u == "_" && ff == "FiniteField" {
                                    if let Ok(n) = p.parse::<BigUint>() {
                                        prime = Some(n);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            "define-fun" => {
                let (name, def) = parse_define_fun(list)?;
                macros.insert(name, def);
            }
            _ => {}
        }
    }

    // Default prime if only Bool decls appeared (still need *some* field).
    let prime = prime.unwrap_or_else(|| BigUint::from(2u32));

    let mut ctx = ParseCtx {
        prime: prime.clone(),
        vars,
        macros,
        next_ite_skolem: 0,
        side_constraints: Vec::new(),
        builder: ConstraintSystemBuilder::new(prime),
    };

    // Second pass: handle asserts in order. Asserts come after macros and
    // declarations in conforming inputs; reading them in source order is
    // sufficient for our needs.
    for s in &sexprs {
        let list = match s {
            Sexpr::List(l) => l,
            Sexpr::Atom(_) => continue,
        };
        if let Some(Sexpr::Atom(h)) = list.first() {
            if h == "assert" {
                if list.len() != 2 {
                    return Err(ParseError::Malformed("'assert' arity".into()));
                }
                formulas.push(assert_to_formula(&list[1], &mut ctx)?);
            }
        }
    }

    // Append side constraints from term-level ite, define-fun, etc.
    formulas.extend(ctx.side_constraints.drain(..));

    // Bool variables live in the polynomial namespace as FF elements
    // restricted to {0, 1}. Emit the bit-constraint `b * b = b` for
    // each (skolem ite vars are Ff and filtered out).
    let bool_names: Vec<String> = ctx
        .vars
        .iter()
        .filter_map(|(name, sort)| if matches!(sort, VarSort::Bool) { Some(name.clone()) } else { None })
        .collect();
    for name in &bool_names {
        let idx = ctx.builder.var(name);
        let b_sq: Polynomial = vec![PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(idx, 2)],
        }];
        let b: Polynomial = vec![PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(idx, 1)],
        }];
        formulas.push(Formula::Lit(Literal::Eq(b_sq, b)));
    }

    let combined = if formulas.is_empty() {
        Formula::True
    } else if formulas.len() == 1 {
        formulas.pop().unwrap()
    } else {
        Formula::And(formulas)
    };
    Ok(BooleanQuery::from_builder_and_formula(ctx.builder, combined))
}



#[cfg(test)]
mod tests;
