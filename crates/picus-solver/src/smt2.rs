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

use std::collections::HashMap;
use std::fmt;

use num_bigint::BigUint;
use num_traits::Zero;

use crate::encoder::{ConstraintSystem, PolyTerm};

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

// ─────────────────────── Tokenizer ───────────────────────────────────────

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    LParen,
    RParen,
    Sym(String),
}

fn tokenize(src: &str) -> Vec<Tok> {
    let mut out = Vec::new();
    let bytes = src.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b';' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else if b.is_ascii_whitespace() {
            i += 1;
        } else if b == b'(' {
            out.push(Tok::LParen);
            i += 1;
        } else if b == b')' {
            out.push(Tok::RParen);
            i += 1;
        } else if b == b'|' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j] != b'|' {
                j += 1;
            }
            let s = std::str::from_utf8(&bytes[i + 1..j]).unwrap_or("").to_string();
            out.push(Tok::Sym(s));
            i = j + 1;
        } else {
            let mut j = i;
            while j < bytes.len()
                && !bytes[j].is_ascii_whitespace()
                && bytes[j] != b'('
                && bytes[j] != b')'
            {
                j += 1;
            }
            let s = std::str::from_utf8(&bytes[i..j]).unwrap_or("").to_string();
            out.push(Tok::Sym(s));
            i = j;
        }
    }
    out
}

// ─────────────────────── S-expression tree ───────────────────────────────

#[derive(Debug, Clone)]
enum Sexpr {
    Atom(String),
    List(Vec<Sexpr>),
}

fn parse_sexprs(toks: &[Tok]) -> Result<Vec<Sexpr>, ParseError> {
    let mut i = 0;
    let mut out = Vec::new();
    while i < toks.len() {
        let (s, ni) = parse_one(toks, i)?;
        out.push(s);
        i = ni;
    }
    Ok(out)
}

fn parse_one(toks: &[Tok], i: usize) -> Result<(Sexpr, usize), ParseError> {
    match &toks[i] {
        Tok::LParen => {
            let mut j = i + 1;
            let mut children = Vec::new();
            while j < toks.len() && toks[j] != Tok::RParen {
                let (s, nj) = parse_one(toks, j)?;
                children.push(s);
                j = nj;
            }
            if j >= toks.len() {
                return Err(ParseError::Malformed("unclosed list".into()));
            }
            Ok((Sexpr::List(children), j + 1))
        }
        Tok::Sym(s) => Ok((Sexpr::Atom(s.clone()), i + 1)),
        Tok::RParen => Err(ParseError::UnexpectedToken(")".into())),
    }
}

// ─────────────────────── Sort tracking ───────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VarSort {
    Ff,
    Bool,
}

#[derive(Debug, Clone)]
struct MacroDef {
    params: Vec<(String, VarSort)>,
    body: Sexpr,
}

/// Classify a sort s-expression as `Ff`, `Bool`, or unknown.
fn classify_sort(s: Option<&Sexpr>) -> Option<VarSort> {
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

type Polynomial = Vec<PolyTerm>;

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

fn mul_polys(a: &Polynomial, b: &Polynomial, prime: &BigUint) -> Polynomial {
    let mut out = Vec::with_capacity(a.len() * b.len());
    for ta in a {
        for tb in b {
            let coeff = (&ta.coeff * &tb.coeff) % prime;
            if coeff.is_zero() {
                continue;
            }
            let mut vars = ta.vars.clone();
            vars.extend(tb.vars.iter().cloned());
            out.push(PolyTerm { coeff, vars });
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
                Some(VarSort::Ff) => Ok(vec![PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![a.clone()],
                }]),
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
                        let p = build_poly(child, prime, vars)?;
                        acc = add_polys(acc, p);
                    }
                    Ok(acc)
                }
                "ff.bitsum" => {
                    let mut acc: Polynomial = Vec::new();
                    let mut weight = BigUint::from(1u32);
                    let two = BigUint::from(2u32);
                    for child in &elts[1..] {
                        let p = build_poly(child, prime, vars)?;
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
                        let p = build_poly(child, prime, vars)?;
                        acc = mul_polys(&acc, &p, prime);
                    }
                    Ok(acc)
                }
                "ff.neg" => {
                    if elts.len() != 2 {
                        return Err(ParseError::Malformed("'ff.neg' arity".into()));
                    }
                    let p = build_poly(&elts[1], prime, vars)?;
                    Ok(neg_poly(&p, prime))
                }
                "-" if elts.len() == 2 => {
                    let p = build_poly(&elts[1], prime, vars)?;
                    Ok(neg_poly(&p, prime))
                }
                "-" => {
                    let mut acc = build_poly(&elts[1], prime, vars)?;
                    for child in &elts[2..] {
                        let p = build_poly(child, prime, vars)?;
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
    equalities: &mut Vec<Vec<PolyTerm>>,
    diseqs: &mut Vec<(String, String)>,
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
            let a = build_poly(&list[1], prime, vars)?;
            let b = build_poly(&list[2], prime, vars)?;
            let poly = add_polys(a, neg_poly(&b, prime));
            equalities.push(poly);
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
            let a = build_poly(&inner[1], prime, vars)?;
            let b = build_poly(&inner[2], prime, vars)?;

            // d = a - b; assert d != 0 via the disequality list.
            let d_name = format!("__diseq_d_{}", diseq_counter);
            *diseq_counter += 1;
            let zero_name = "__zero".to_string();
            let mut def: Vec<PolyTerm> = vec![PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![d_name.clone()],
            }];
            def.extend(neg_poly(&a, prime));
            def.extend(b);
            equalities.push(def);
            diseqs.push((d_name, zero_name));
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

/// Parse an SMT-LIB v2 QF_FF source and produce a [`ConstraintSystem`].
pub fn parse(src: &str) -> Result<ConstraintSystem, ParseError> {
    let toks = tokenize(src);
    let sexprs = parse_sexprs(&toks)?;

    let mut prime: Option<BigUint> = None;
    let mut vars: HashMap<String, VarSort> = HashMap::new();
    let mut equalities: Vec<Vec<PolyTerm>> = Vec::new();
    let mut diseqs: Vec<(String, String)> = Vec::new();
    let mut diseq_counter = 0usize;

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
            | "push" | "pop" | "echo" => {
                // ignored
            }
            "define-sort" => {
                // (define-sort F () (_ FiniteField N))
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
            "assert" => {
                if list.len() != 2 {
                    return Err(ParseError::Malformed("'assert' arity".into()));
                }
                let p = prime.as_ref().ok_or(ParseError::MissingPrime)?;
                handle_assert(
                    &list[1],
                    p,
                    &vars,
                    &mut equalities,
                    &mut diseqs,
                    &mut diseq_counter,
                )?;
            }
            _ => {
                // Unknown top-level form: ignore.
            }
        }
    }

    let prime = prime.ok_or(ParseError::MissingPrime)?;

    // Pin `__zero` to the field's zero so `__diseq_d_i != __zero` matches `d != 0`.
    let mut assignments: Vec<(String, BigUint)> = Vec::new();
    if diseq_counter > 0 {
        assignments.push(("__zero".into(), BigUint::zero()));
    }

    let mut sys = ConstraintSystem {
        prime,
        equalities,
        disequalities: diseqs,
        assignments,
        add_field_polys: false,
        bitsums: vec![],
    };
    crate::rewriter::rewrite_system(&mut sys);
    Ok(sys)
}

// ─────────────────────── Boolean structure parser ────────────────────────

use crate::boolean::{BooleanQuery, Formula, Literal};

/// Parser state for `parse_boolean`. Threads through `assert_to_formula`
/// and `build_poly_with_ctx` so they can introduce skolems and expand
/// macros.
struct ParseCtx {
    prime: BigUint,
    vars: HashMap<String, VarSort>,
    macros: HashMap<String, MacroDef>,
    /// Counter for `__ite_N` skolems introduced by term-level `ite`.
    next_ite_skolem: usize,
    /// Constraints generated as side effects (e.g. term-level `ite`).
    /// AND-conjoined into the final formula at the top of
    /// `parse_boolean`.
    side_constraints: Vec<Formula>,
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

/// Build an FF polynomial recursively. Handles every FF operator
/// directly (rather than delegating to `build_poly`) so term-level
/// `ite` and macro applications are detected at every nesting depth.
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
                Some(VarSort::Ff) => Ok(vec![PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![a.clone()],
                }]),
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
                    let r_poly: Polynomial = vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![r_name],
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
                    // sum_i (2^i * a_i)  mod prime
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

fn assert_to_formula(s: &Sexpr, ctx: &mut ParseCtx) -> Result<Formula, ParseError> {
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
                    let one: Polynomial = vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![],
                    }];
                    let b: Polynomial = vec![PolyTerm {
                        coeff: BigUint::from(1u32),
                        vars: vec![name.to_string()],
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
fn parse_define_fun(list: &[Sexpr]) -> Result<(String, MacroDef), ParseError> {
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
        prime,
        vars,
        macros,
        next_ite_skolem: 0,
        side_constraints: Vec::new(),
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
    for (name, sort) in &ctx.vars {
        if matches!(sort, VarSort::Bool) {
            let b_sq: Polynomial = vec![PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![name.clone(), name.clone()],
            }];
            let b: Polynomial = vec![PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![name.clone()],
            }];
            formulas.push(Formula::Lit(Literal::Eq(b_sq, b)));
        }
    }

    let var_names: Vec<String> = ctx.vars.keys().cloned().collect();
    let combined = if formulas.is_empty() {
        Formula::True
    } else if formulas.len() == 1 {
        formulas.pop().unwrap()
    } else {
        Formula::And(formulas)
    };
    Ok(BooleanQuery::from_formula(ctx.prime, var_names, combined))
}

// ─────────────────────────── SMT-LIB v2 session ─────────────────────────────

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
    prime: Option<BigUint>,
    vars: HashMap<String, VarSort>,
    /// Insertion order of `declare-fun` / `declare-const`. Used for
    /// truncation on `(pop)` and for a deterministic `(get-model)`
    /// print order.
    var_order: Vec<String>,
    macros: HashMap<String, MacroDef>,
    macro_order: Vec<String>,
    formulas: Vec<Formula>,
    /// `assert_names[i]` is the `:named` label of `formulas[i]`, if
    /// any. Parallel to `formulas`; `None` for unlabelled asserts.
    assert_names: Vec<Option<String>>,
    /// Per-check timeout in milliseconds, set by
    /// `(set-option :tlimit-per <N>)`. `None` ⇒ no timeout.
    tlimit_per_ms: Option<u64>,
    side_constraints: Vec<Formula>,
    next_ite_skolem: usize,
    levels: Vec<SessionLevel>,
    last_check: Option<SessionVerdict>,
    last_model: Option<HashMap<String, BigUint>>,
    /// Set after the last `(check-sat)` returned UNSAT: every
    /// `:named` assert in scope at that moment. SMT-LIB allows the
    /// core to be any sufficient subset (not necessarily minimal),
    /// so the full named-assert list is a sound conservative answer.
    last_unsat_core_names: Vec<String>,
}

#[derive(Clone)]
struct SessionLevel {
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
            out.push_str(&format_define_fun(name, &val, sort, self.prime.as_ref()));
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

    #[test]
    fn parses_minimal_unsat() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun x () F)
            (assert (= x (as ff2 F)))
            (assert (= x (as ff3 F)))
            (check-sat)
        "#;
        let cs = parse(src).expect("parse");
        assert_eq!(cs.prime, BigUint::from(7u32));
        assert_eq!(cs.equalities.len(), 2);
    }

    #[test]
    fn parses_inline_finite_field_sort() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 17))
            (assert (= (ff.mul x x) x))
            (check-sat)
        "#;
        let cs = parse(src).expect("parse");
        assert_eq!(cs.prime, BigUint::from(17u32));
        assert_eq!(cs.equalities.len(), 1);
    }

    #[test]
    fn rejects_boolean_in_assert() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun x () F)
            (declare-fun y () F)
            (assert (or (= x (as ff0 F)) (= y (as ff0 F))))
            (check-sat)
        "#;
        match parse(src) {
            Err(ParseError::BooleanInAssert(op)) => assert_eq!(op, "or"),
            other => panic!("expected BooleanInAssert(or); got {:?}", other),
        }
    }

    #[test]
    fn parses_disequality_via_not() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun x () F)
            (assert (not (= x (as ff0 F))))
            (check-sat)
        "#;
        let cs = parse(src).expect("parse");
        assert_eq!(cs.disequalities.len(), 1);
        assert_eq!(cs.assignments.len(), 1); // __zero pinned
    }

    #[test]
    fn rejects_unknown_symbol() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun x () F)
            (assert (= x y))
            (check-sat)
        "#;
        match parse(src) {
            Err(ParseError::UnknownSymbol(s)) => assert_eq!(s, "y"),
            other => panic!("expected UnknownSymbol(y); got {:?}", other),
        }
    }

    // ─────────────── Bool decl + iff (parse_boolean) ───────────────

    #[test]
    fn parse_boolean_accepts_bool_decl() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun b () Bool)
            (assert b)
            (check-sat)
        "#;
        let q = parse_boolean(src).expect("parse");
        assert!(q.var_names.iter().any(|n| n == "b"));
    }

    #[test]
    fn parse_boolean_iff_two_bools_pairwise() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (assert (= a b))
            (assert a)
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    #[test]
    fn parse_boolean_rejects_bool_var_in_ff_term() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun b () Bool)
            (declare-fun x () F)
            (assert (= (ff.add b x) (as ff0 F)))
            (check-sat)
        "#;
        match parse_boolean(src) {
            Err(ParseError::Malformed(_)) => {}
            other => panic!("expected Malformed for Bool in FF term: {:?}", other),
        }
    }

    // ─────────────── Term-level ite ───────────────

    #[test]
    fn parse_boolean_term_level_ite() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 101))
            (declare-fun c () Bool)
            (declare-fun x () F)
            (assert (= (ite c x (as ff0 F)) (as ff5 F)))
            (check-sat)
        "#;
        let q = parse_boolean(src).expect("parse");
        assert!(q.var_names.iter().any(|n| n.starts_with("__ite_")));
    }

    #[test]
    fn parse_boolean_term_level_ite_nested() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 101))
            (declare-fun c1 () Bool)
            (declare-fun c2 () Bool)
            (declare-fun x () F)
            (declare-fun y () F)
            (assert (= (ite c1 (ite c2 x y) (as ff0 F)) (as ff5 F)))
            (check-sat)
        "#;
        let q = parse_boolean(src).expect("parse");
        let skolems = q
            .var_names
            .iter()
            .filter(|n| n.starts_with("__ite_"))
            .count();
        assert_eq!(skolems, 2);
    }

    // ─────────────── n-ary `=` and `distinct` ───────────────

    #[test]
    fn parse_boolean_nary_ff_equality() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun x () F)
            (declare-fun y () F)
            (declare-fun z () F)
            (assert (= x y z (as ff2 F)))
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    #[test]
    fn parse_boolean_distinct_ff() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun x () F)
            (declare-fun y () F)
            (declare-fun z () F)
            (assert (distinct x y z))
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    #[test]
    fn parse_boolean_distinct_bool_three_is_false() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (assert (distinct a b c))
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    // ─────────────── define-fun macros ───────────────

    #[test]
    fn parse_boolean_define_fun_inlines() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun x () F)
            (define-fun double ((y F)) F (ff.add y y))
            (assert (= (double x) (as ff2 F)))
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    #[test]
    fn parse_boolean_define_fun_bool_macro() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (define-fun nand ((p Bool) (q Bool)) Bool (not (and p q)))
            (assert (nand a b))
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    // ─────────────── n-ary xor ───────────────

    #[test]
    fn parse_boolean_binary_xor() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (assert (xor a b))
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    #[test]
    fn parses_negative_ff_constant_ff_form() {
        let prime = BigUint::from(17u32);
        // ff-1 ≡ 16 mod 17
        assert_eq!(parse_ff_const("ff-1", &prime), Some(BigUint::from(16u32)));
        // ff-0 ≡ 0
        assert_eq!(parse_ff_const("ff-0", &prime), Some(BigUint::zero()));
        // ff5 ≡ 5
        assert_eq!(parse_ff_const("ff5", &prime), Some(BigUint::from(5u32)));
        // ff.add and ff.mul must NOT match
        assert_eq!(parse_ff_const("ff.add", &prime), None);
        assert_eq!(parse_ff_const("ff.mul", &prime), None);
    }

    #[test]
    fn parses_negative_ff_constant_hash_form() {
        let prime = BigUint::from(17u32);
        // #f-1m17 ≡ 16
        assert_eq!(parse_ff_const("#f-1m17", &prime), Some(BigUint::from(16u32)));
        // #f3m17 ≡ 3
        assert_eq!(parse_ff_const("#f3m17", &prime), Some(BigUint::from(3u32)));
    }

    #[test]
    fn parse_boolean_ff_bitsum() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun a () (_ FiniteField 3))
            (declare-fun b () (_ FiniteField 3))
            (declare-fun c () (_ FiniteField 3))
            (assert (= (ff.bitsum a b c) #f0m3))
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    #[test]
    fn parse_boolean_nary_xor() {
        let src = r#"
            (set-logic QF_FF)
            (define-sort F () (_ FiniteField 7))
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (assert (xor a b c))
            (check-sat)
        "#;
        parse_boolean(src).expect("parse");
    }

    // ─────────────────────────── SmtSession ─────────────────────────

    #[test]
    fn session_check_sat_returns_sat_for_satisfiable() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f3m7))
            (check-sat)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert_eq!(outs.len(), 1);
        assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Sat)));
    }

    #[test]
    fn session_check_sat_returns_unsat() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f2m7))
            (assert (= x #f3m7))
            (check-sat)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert_eq!(outs.len(), 1);
        assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Unsat)));
    }

    #[test]
    fn session_get_model_prints_assignment() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (declare-fun b () Bool)
            (assert (= x #f3m7))
            (assert b)
            (check-sat)
            (get-model)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert_eq!(outs.len(), 2);
        assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Sat)));
        let model_text = match &outs[1] {
            SessionOutput::Model(s) => s.clone(),
            other => panic!("expected Model, got {:?}", other),
        };
        assert!(
            model_text.contains("(define-fun x () (_ FiniteField 7) #f3m7)"),
            "missing x; model:\n{}",
            model_text
        );
        assert!(
            model_text.contains("(define-fun b () Bool true)"),
            "missing b=true; model:\n{}",
            model_text
        );
    }

    #[test]
    fn session_get_value_prints_requested() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (declare-fun b () Bool)
            (assert (= x #f3m7))
            (assert (not b))
            (check-sat)
            (get-value (x b))
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert_eq!(outs.len(), 2);
        let values = match &outs[1] {
            SessionOutput::Values(v) => v.clone(),
            other => panic!("expected Values, got {:?}", other),
        };
        assert_eq!(values.len(), 2);
        assert_eq!(values[0], ("x".into(), "#f3m7".into()));
        assert_eq!(values[1], ("b".into(), "false".into()));
    }

    #[test]
    fn session_push_pop_isolates_asserts() {
        // Stack: base (sat) → push (add contradicting assert → unsat)
        // → pop (sat again).
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f3m7))
            (check-sat)
            (push 1)
            (assert (= x #f5m7))
            (check-sat)
            (pop 1)
            (check-sat)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        let verdicts: Vec<SessionVerdict> = outs
            .iter()
            .filter_map(|o| if let SessionOutput::CheckSat(v) = o { Some(*v) } else { None })
            .collect();
        assert_eq!(
            verdicts,
            vec![SessionVerdict::Sat, SessionVerdict::Unsat, SessionVerdict::Sat]
        );
    }

    #[test]
    fn session_pop_drops_declared_vars() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (push 1)
            (declare-fun y () (_ FiniteField 7))
            (assert (= y #f4m7))
            (pop 1)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert!(sess.vars.contains_key("x"));
        assert!(!sess.vars.contains_key("y"), "y must be dropped after pop");
        assert_eq!(sess.formulas.len(), 0, "y's assert must be dropped");
    }

    #[test]
    fn session_multiple_check_sat_independent() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f3m7))
            (check-sat)
            (check-sat)
            (check-sat)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert_eq!(outs.len(), 3);
        for o in &outs {
            assert!(matches!(o, SessionOutput::CheckSat(SessionVerdict::Sat)));
        }
    }

    #[test]
    fn session_to_smtlib_formats_verdicts() {
        assert_eq!(
            SessionOutput::CheckSat(SessionVerdict::Sat).to_smtlib(),
            "sat"
        );
        assert_eq!(
            SessionOutput::CheckSat(SessionVerdict::Unsat).to_smtlib(),
            "unsat"
        );
        assert_eq!(
            SessionOutput::CheckSat(SessionVerdict::Unknown).to_smtlib(),
            "unknown"
        );
    }

    #[test]
    fn session_named_assert_strips_annotation() {
        // `(assert (! (= x #f5m7) :named foo))` must behave exactly
        // like `(assert (= x #f5m7))` for the purposes of solving.
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (! (= x #f5m7) :named foo))
            (check-sat)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Sat)));
    }

    #[test]
    fn session_get_unsat_core_reports_named_asserts() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (! (= x #f2m7) :named a))
            (assert (! (= x #f3m7) :named b))
            (check-sat)
            (get-unsat-core)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert_eq!(outs.len(), 2);
        assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Unsat)));
        match &outs[1] {
            SessionOutput::UnsatCore(names) => {
                assert!(names.contains(&"a".to_string()) && names.contains(&"b".to_string()),
                    "core must include both named asserts; got {:?}", names);
            }
            other => panic!("expected UnsatCore, got {:?}", other),
        }
    }

    #[test]
    fn session_get_unsat_core_empty_on_sat() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (! (= x #f5m7) :named foo))
            (check-sat)
            (get-unsat-core)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        match &outs[1] {
            SessionOutput::UnsatCore(names) => assert!(
                names.is_empty(),
                "SAT verdict ⇒ empty core; got {:?}",
                names
            ),
            other => panic!("expected UnsatCore, got {:?}", other),
        }
    }

    #[test]
    fn session_unnamed_asserts_excluded_from_core() {
        // Only the `:named` asserts should appear in the core.
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f2m7))
            (assert (! (= x #f3m7) :named conflict))
            (check-sat)
            (get-unsat-core)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        match &outs[1] {
            SessionOutput::UnsatCore(names) => {
                assert_eq!(names, &vec!["conflict".to_string()]);
            }
            other => panic!("expected UnsatCore, got {:?}", other),
        }
    }

    #[test]
    fn session_set_option_tlimit_per_is_recorded() {
        // The session records `:tlimit-per` so it can pass a
        // CancelToken with that timeout to each `(check-sat)`.
        let src = r#"
            (set-option :tlimit-per 5000)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert_eq!(sess.tlimit_per_ms, Some(5000));
    }

    #[test]
    fn session_tlimit_per_zero_disables_timeout() {
        let src = r#"
            (set-option :tlimit-per 0)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert_eq!(sess.tlimit_per_ms, None);
    }

    // ─── Edge cases: queries-before-check, exit, reset variants ───

    #[test]
    fn session_get_model_before_check_sat_returns_empty_model() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (get-model)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert_eq!(outs.len(), 1);
        match &outs[0] {
            // No check-sat ran ⇒ no model recorded ⇒ empty block.
            SessionOutput::Model(s) => {
                assert!(!s.contains("define-fun"), "no defs expected; got {:?}", s);
            }
            other => panic!("expected Model, got {:?}", other),
        }
    }

    #[test]
    fn session_get_value_before_check_sat_returns_empty() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (get-value (x))
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        match &outs[0] {
            SessionOutput::Values(v) => assert!(v.is_empty()),
            other => panic!("expected Values, got {:?}", other),
        }
    }

    #[test]
    fn session_get_value_skips_undeclared_name() {
        // Querying an undeclared name must skip it rather than
        // fabricate a zero value.
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f3m7))
            (check-sat)
            (get-value (x undeclared))
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        let values = match &outs[1] {
            SessionOutput::Values(v) => v.clone(),
            other => panic!("expected Values, got {:?}", other),
        };
        assert_eq!(values.len(), 1, "undeclared name must be skipped: {:?}", values);
        assert_eq!(values[0].0, "x");
    }

    #[test]
    fn session_get_unsat_core_before_check_sat_is_empty() {
        let src = r#"
            (set-logic QF_FF)
            (get-unsat-core)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        match &outs[0] {
            SessionOutput::UnsatCore(v) => assert!(v.is_empty()),
            other => panic!("expected UnsatCore, got {:?}", other),
        }
    }

    #[test]
    fn session_exit_stops_eval_script() {
        // Commands after `(exit)` must not be evaluated.
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f3m7))
            (check-sat)
            (exit)
            (assert (= x #f4m7))
            (check-sat)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        // Exactly one (check-sat) before (exit) — the trailing one is skipped.
        let verdicts: Vec<_> = outs
            .iter()
            .filter_map(|o| if let SessionOutput::CheckSat(v) = o { Some(*v) } else { None })
            .collect();
        assert_eq!(verdicts, vec![SessionVerdict::Sat]);
        // The trailing assert was never applied to session state.
        assert_eq!(sess.formulas.len(), 1);
    }

    #[test]
    fn session_reset_clears_everything() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (set-option :tlimit-per 5000)
            (assert (= x #f3m7))
            (reset)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert!(sess.vars.is_empty());
        assert!(sess.formulas.is_empty());
        assert!(sess.prime.is_none());
        assert_eq!(sess.tlimit_per_ms, None);
    }

    #[test]
    fn session_reset_assertions_keeps_declarations() {
        // SMT-LIB v2 §4.2.1: (reset-assertions) clears asserts and
        // the push trail but keeps the logic, declarations, macros,
        // and options.
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (define-fun is_three ((y (_ FiniteField 7))) Bool (= y #f3m7))
            (set-option :tlimit-per 4000)
            (assert (is_three x))
            (reset-assertions)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert!(sess.vars.contains_key("x"), "declarations must survive reset-assertions");
        assert!(sess.macros.contains_key("is_three"), "macros must survive");
        assert_eq!(sess.prime, Some(BigUint::from(7u32)));
        assert_eq!(sess.tlimit_per_ms, Some(4000));
        assert!(sess.formulas.is_empty(), "asserts must be cleared");
        assert!(sess.levels.is_empty(), "push trail must be cleared");
    }

    // ─── Edge cases: push/pop ───

    #[test]
    fn session_push_n_pop_n_balance() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (push 3)
            (assert (= x #f1m7))
            (push 2)
            (assert (= x #f2m7))
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert_eq!(sess.decision_level(), 5);
        assert_eq!(sess.formulas.len(), 2);
        // Pop 4 of 5 levels — the top 4 came after the second assert
        // and the first one — both should be cleared.
        sess.eval_script("(pop 4)").expect("eval");
        assert_eq!(sess.decision_level(), 1);
        assert_eq!(sess.formulas.len(), 0);
    }

    #[test]
    fn session_pop_past_root_is_best_effort() {
        // Popping more levels than exist must not panic; remaining
        // requests are no-ops.
        let src = r#"
            (push 2)
            (pop 5)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert_eq!(sess.decision_level(), 0);
    }

    // ─── Edge cases: macros / declarations across push/pop ───

    #[test]
    fn session_macro_introduced_inside_push_is_dropped_on_pop() {
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (push 1)
            (define-fun is_one ((y (_ FiniteField 7))) Bool (= y #f1m7))
            (assert (is_one x))
            (pop 1)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert!(!sess.macros.contains_key("is_one"), "macro must be dropped");
        assert!(sess.formulas.is_empty(), "assert using macro must be dropped");
    }

    #[test]
    fn session_pop_restores_ite_skolem_counter() {
        // A term-level (ite ...) inside an assert allocates a
        // __ite_N skolem and emits side constraints. After pop, the
        // counter must reset so a new ite re-uses the same name.
        let src_push = r#"
            (set-logic QF_FF)
            (declare-fun c () Bool)
            (declare-fun x () (_ FiniteField 101))
            (push 1)
            (assert (= (ite c x #f0m101) #f5m101))
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src_push).expect("eval");
        let counter_after_assert = sess.next_ite_skolem;
        assert!(counter_after_assert >= 1, "an ite must allocate a skolem");
        sess.eval_script("(pop 1)").expect("eval");
        assert_eq!(
            sess.next_ite_skolem, 0,
            "pop must restore the ite counter to its pre-push value"
        );
        assert!(sess.side_constraints.is_empty(),
            "ite side constraints must be dropped with the push level");
    }

    // ─── Bool-var iteration determinism ───

    #[test]
    fn session_bool_constraints_use_declaration_order() {
        // The order of the auto-emitted `b*b = b` constraints is
        // tied to declaration order, not HashMap iteration order.
        // Re-running the same script must produce the same verdict
        // deterministically.
        let src = r#"
            (set-logic QF_FF)
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
            (declare-fun e () Bool)
            (assert (or a b c d e))
            (check-sat)
        "#;
        for _ in 0..3 {
            let mut sess = SmtSession::new();
            let outs = sess.eval_script(src).expect("eval");
            assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Sat)));
        }
    }

    // ─── to_smtlib formatter ───

    #[test]
    fn session_to_smtlib_formats_values_and_core() {
        let v = SessionOutput::Values(vec![
            ("x".into(), "#f3m7".into()),
            ("b".into(), "true".into()),
        ]);
        let s = v.to_smtlib();
        assert!(s.contains("(x #f3m7)"));
        assert!(s.contains("(b true)"));

        let c = SessionOutput::UnsatCore(vec!["a".into(), "b".into()]);
        assert_eq!(c.to_smtlib(), "(a b)");

        let empty = SessionOutput::UnsatCore(Vec::new());
        assert_eq!(empty.to_smtlib(), "()");
    }

    #[test]
    fn session_silent_to_smtlib_is_empty_string() {
        assert!(SessionOutput::Silent.to_smtlib().is_empty());
    }

    // ─── (! ... :named ...) edge cases ───

    #[test]
    fn session_named_annotation_with_other_attrs_is_stripped() {
        // `(! formula :pattern (...) :named foo :weight 3)` — generic
        // attributes are ignored, but `:named` is captured wherever
        // it appears in the attribute list.
        let src = r#"
            (set-logic QF_FF)
            (declare-fun x () (_ FiniteField 7))
            (assert (! (= x #f2m7) :weight 3 :named foo))
            (assert (! (= x #f3m7) :named bar))
            (check-sat)
            (get-unsat-core)
        "#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        let core = match &outs[1] {
            SessionOutput::UnsatCore(v) => v.clone(),
            other => panic!("expected UnsatCore, got {:?}", other),
        };
        assert!(core.contains(&"foo".to_string()));
        assert!(core.contains(&"bar".to_string()));
    }

    // ─── set-option misuse ───

    #[test]
    fn session_set_option_non_numeric_tlimit_is_ignored() {
        // A non-numeric value silently leaves the existing setting
        // (None) unchanged — no parse error, no spurious timeout.
        let src = r#"
            (set-option :tlimit-per abc)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert_eq!(sess.tlimit_per_ms, None);
    }

    #[test]
    fn session_set_option_tlimit_per_can_be_overwritten() {
        let src = r#"
            (set-option :tlimit-per 1000)
            (set-option :tlimit-per 2000)
        "#;
        let mut sess = SmtSession::new();
        sess.eval_script(src).expect("eval");
        assert_eq!(sess.tlimit_per_ms, Some(2000));
    }

    #[test]
    fn session_echo_is_passed_through() {
        let src = r#"(echo "hello")"#;
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert_eq!(outs.len(), 1);
        match &outs[0] {
            SessionOutput::Echo(s) => assert_eq!(s, "\"hello\""),
            other => panic!("expected Echo, got {:?}", other),
        }
    }
}
