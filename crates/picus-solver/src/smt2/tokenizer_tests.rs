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
