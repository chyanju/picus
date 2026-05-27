//! SMT-LIB v2 tokenizer and S-expression parser.
//!
//! - [`tokenize`] turns a UTF-8 source string into a stream of [`Tok`].
//! - [`parse_sexprs`] turns a token stream into a vector of [`Sexpr`] trees.
//!
//! Comments (`; ...`) are dropped during tokenization; quoted symbols
//! (`|sym|`) are unquoted.

use super::ParseError;

/// Maximum S-expression nesting depth accepted by [`parse_one`]. Bounds
/// the depth of every produced [`Sexpr`] tree, which transitively bounds
/// the recursion of all downstream tree-walkers (`build_poly`,
/// `assert_to_formula`, …) that descend into sub-expressions. Adversarial
/// input with deeper nesting is rejected as malformed rather than
/// overflowing the stack (an abort `catch_unwind` cannot intercept). The
/// limit is far above any realistic SMT-LIB term and chosen to stay within
/// a worker thread's default stack even for the heaviest walker frame.
pub(super) const MAX_SEXPR_DEPTH: usize = 1024;

#[derive(Debug, Clone, PartialEq)]
pub(super) enum Tok {
    LParen,
    RParen,
    Sym(String),
}

pub(super) fn tokenize(src: &str) -> Vec<Tok> {
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

#[derive(Debug, Clone)]
pub(super) enum Sexpr {
    Atom(String),
    List(Vec<Sexpr>),
}

pub(super) fn parse_sexprs(toks: &[Tok]) -> Result<Vec<Sexpr>, ParseError> {
    let mut i = 0;
    let mut out = Vec::new();
    while i < toks.len() {
        let (s, ni) = parse_one(toks, i, 0)?;
        out.push(s);
        i = ni;
    }
    Ok(out)
}

pub(super) fn parse_one(toks: &[Tok], i: usize, depth: usize) -> Result<(Sexpr, usize), ParseError> {
    if depth > MAX_SEXPR_DEPTH {
        return Err(ParseError::Malformed(format!(
            "S-expression nesting exceeds depth {}",
            MAX_SEXPR_DEPTH
        )));
    }
    let tok = toks
        .get(i)
        .ok_or_else(|| ParseError::Malformed("unexpected end of input".into()))?;
    match tok {
        Tok::LParen => {
            let mut j = i + 1;
            let mut children = Vec::new();
            while j < toks.len() && toks[j] != Tok::RParen {
                let (s, nj) = parse_one(toks, j, depth + 1)?;
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
