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

#[cfg(test)]
mod tests {
    use super::*;

    fn syms(toks: &[Tok]) -> Vec<&str> {
        toks.iter()
            .filter_map(|t| match t {
                Tok::Sym(s) => Some(s.as_str()),
                _ => None,
            })
            .collect()
    }

    // ────────── tokenize ──────────

    #[test]
    fn tokenize_empty_yields_no_tokens() {
        assert!(tokenize("").is_empty());
        assert!(tokenize("   \n\t  ").is_empty());
    }

    #[test]
    fn tokenize_parens_only() {
        let t = tokenize("()");
        assert_eq!(t, vec![Tok::LParen, Tok::RParen]);
    }

    #[test]
    fn tokenize_atom_separator_runs() {
        let t = tokenize("foo  bar\tbaz");
        assert_eq!(syms(&t), vec!["foo", "bar", "baz"]);
    }

    #[test]
    fn tokenize_paren_breaks_atom() {
        let t = tokenize("foo(bar)baz");
        assert_eq!(t.len(), 5);
        assert_eq!(syms(&t), vec!["foo", "bar", "baz"]);
    }

    #[test]
    fn tokenize_drops_comments_to_eol() {
        let t = tokenize("a ; this is a comment\nb");
        assert_eq!(syms(&t), vec!["a", "b"]);
    }

    #[test]
    fn tokenize_comment_at_eof_is_dropped() {
        let t = tokenize("foo ; trailing comment no newline");
        assert_eq!(syms(&t), vec!["foo"]);
    }

    #[test]
    fn tokenize_quoted_symbol_strips_pipes() {
        let t = tokenize("|hello world|");
        assert_eq!(syms(&t), vec!["hello world"]);
    }

    #[test]
    fn tokenize_quoted_symbol_with_parens_inside_is_one_atom() {
        let t = tokenize("|f(x)|");
        assert_eq!(syms(&t), vec!["f(x)"]);
    }

    #[test]
    fn tokenize_keeps_strings_as_atoms() {
        // SMT-LIB strings come through as bracketed atoms (the lexer
        // doesn't treat `"` specially — `parse_ff_const` and friends do).
        let t = tokenize(r#"(echo "hi")"#);
        assert_eq!(syms(&t), vec!["echo", "\"hi\""]);
    }

    // ────────── parse_sexprs ──────────

    #[test]
    fn parse_atom_returns_atom() {
        let toks = tokenize("hello");
        let out = parse_sexprs(&toks).expect("parse ok");
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], Sexpr::Atom(s) if s == "hello"));
    }

    #[test]
    fn parse_empty_list() {
        let toks = tokenize("()");
        let out = parse_sexprs(&toks).expect("parse ok");
        assert_eq!(out.len(), 1);
        match &out[0] {
            Sexpr::List(v) => assert!(v.is_empty()),
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_nested_list() {
        let toks = tokenize("(a (b c) d)");
        let out = parse_sexprs(&toks).expect("parse ok");
        assert_eq!(out.len(), 1);
        match &out[0] {
            Sexpr::List(v) => {
                assert_eq!(v.len(), 3);
                assert!(matches!(&v[0], Sexpr::Atom(s) if s == "a"));
                assert!(matches!(&v[1], Sexpr::List(_)));
                assert!(matches!(&v[2], Sexpr::Atom(s) if s == "d"));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_multiple_top_level_forms() {
        let toks = tokenize("(a) (b) c");
        let out = parse_sexprs(&toks).expect("parse ok");
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn parse_unclosed_list_errors() {
        let toks = tokenize("(a (b c)");
        let err = parse_sexprs(&toks).unwrap_err();
        assert!(matches!(err, ParseError::Malformed(_)));
    }

    #[test]
    fn parse_unexpected_close_paren_errors() {
        let toks = tokenize(")");
        let err = parse_sexprs(&toks).unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedToken(_)));
    }

    #[test]
    fn parse_depth_cap_rejects_deep_nesting() {
        // Build N+2 open-parens, all closed — that exceeds the depth cap.
        let n = MAX_SEXPR_DEPTH + 2;
        let mut src = String::new();
        for _ in 0..n {
            src.push('(');
        }
        for _ in 0..n {
            src.push(')');
        }
        let toks = tokenize(&src);
        let err = parse_sexprs(&toks).unwrap_err();
        match err {
            ParseError::Malformed(msg) => assert!(msg.contains("depth")),
            other => panic!("expected depth-cap Malformed, got {:?}", other),
        }
    }

    #[test]
    fn parse_truncated_input_errors() {
        // parse_one on an empty token slice (or past-end index) returns
        // the "unexpected end of input" error.
        let err = parse_sexprs(&[]).expect("empty toks parse ok");
        assert!(err.is_empty());
        // Open paren at end with no contents and no close.
        let toks = tokenize("(");
        let err = parse_sexprs(&toks).unwrap_err();
        assert!(matches!(err, ParseError::Malformed(_)));
    }
}
