//! SMT-LIB v2 input parser for QF_FF problems.
//!
//! Supported subset:
//! - `(set-logic QF_FF)`, `(define-sort F () (_ FiniteField N))`
//! - `(declare-fun x () F)`, `(declare-const x F)`,
//!   `(declare-fun x () (_ FiniteField N))`
//! - `(assert (= a b))` and `(assert (not (= a b)))`
//! - Field expressions: `ff.add`, `ff.mul`, `ff.neg`, `(as ffN F)`
//! - Field constants: `ffN`, `#fNmP`
//! - Decimal integer literals (reduced mod the active prime)
//!
//! Boolean operators (`and`, `or`, `=>`, `ite`) inside `(assert ...)`
//! return [`ParseError::BooleanInAssert`].
//!
//! [`parse`] returns a [`ConstraintSystem`] consumable by
//! [`crate::encoder::encode`].

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

/// Parse `ffN` or `#fNmP` constant; returns `Some(N mod prime)` on match.
fn parse_ff_const(sym: &str, prime: &BigUint) -> Option<BigUint> {
    if let Some(rest) = sym.strip_prefix("ff") {
        return rest.parse::<BigUint>().ok().map(|v| v % prime);
    }
    if let Some(rest) = sym.strip_prefix("#f") {
        let mut split = rest.splitn(2, 'm');
        let n = split.next()?.parse::<BigUint>().ok()?;
        let _ = split.next()?;
        return Some(n % prime);
    }
    None
}

fn build_poly(
    s: &Sexpr,
    prime: &BigUint,
    vars: &HashMap<String, ()>,
) -> Result<Polynomial, ParseError> {
    match s {
        Sexpr::Atom(a) => {
            if let Some(c) = parse_ff_const(a, prime) {
                return Ok(vec![PolyTerm { coeff: c, vars: vec![] }]);
            }
            if let Ok(c) = a.parse::<BigUint>() {
                return Ok(vec![PolyTerm { coeff: c % prime, vars: vec![] }]);
            }
            if !vars.contains_key(a) {
                return Err(ParseError::UnknownSymbol(a.clone()));
            }
            Ok(vec![PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![a.clone()],
            }])
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
    vars: &HashMap<String, ()>,
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
    let mut vars: HashMap<String, ()> = HashMap::new();
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
                // (declare-fun x () F)        | (declare-const x F)
                // (declare-fun x () (_ FiniteField N))
                if list.len() < 2 {
                    continue;
                }
                if let Sexpr::Atom(name) = &list[1] {
                    vars.insert(name.clone(), ());
                }
                // Adopt an inline (_ FiniteField N) as the active prime
                // if `define-sort` hasn't fixed one yet.
                let sort_sexpr = if head == "declare-fun" {
                    list.get(3)
                } else {
                    list.get(2)
                };
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

    Ok(ConstraintSystem {
        prime,
        equalities,
        disequalities: diseqs,
        assignments,
        add_field_polys: false,
        bitsums: vec![],
    })
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
}
