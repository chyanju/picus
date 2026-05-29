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
fn tokenize_paren_breaks_atom() {
    let t = tokenize("foo(bar)baz");
    assert_eq!(t.len(), 5);
    assert_eq!(syms(&t), vec!["foo", "bar", "baz"]);
}

#[test]
fn tokenize_comment_at_eof_is_dropped() {
    let t = tokenize("foo ; trailing comment no newline");
    assert_eq!(syms(&t), vec!["foo"]);
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

// ────────── SPEC-DRIVEN property tests ──────────
//
// Each property below is derived from the SMT-LIB v2 lexical/syntactic
// spec OR a self-evident algebraic identity of `tokenize` /
// `parse_sexprs`, not from inspecting the source.

/// PROPERTY: Adding any pure-whitespace prefix/suffix/inter-token
/// padding leaves the SMT-LIB token sequence invariant. (Whitespace is
/// purely a separator per SMT-LIB v2 §3.1.)
#[test]
fn prop_tokenize_is_whitespace_invariant() {
    let cases = [
        "foo bar baz",
        "(a (b c) d)",
        "(declare-fun x () F) (assert (= x ff0))",
    ];
    for raw in cases {
        let base = tokenize(raw);
        // Add a leading newline, a trailing tab, and double every ASCII
        // space — purely cosmetic. Tokens must be identical.
        let padded = format!("\n\t   {}   \n", raw.replace(' ', "  "));
        let pad_toks = tokenize(&padded);
        assert_eq!(base, pad_toks, "ws padding changed tokens for {:?}", raw);
    }
}

/// PROPERTY: A single-line comment from `;` to the next `\n` is
/// equivalent to nothing (lexically dropped). Equivalently, replacing
/// the comment text by an empty string must yield the same tokens.
/// (SMT-LIB v2 §3.1 comments.)
#[test]
fn prop_tokenize_comments_are_equivalent_to_empty() {
    let with_comments = "a ; the quick brown fox\nb ; another one\nc";
    let without = "a \nb \nc";
    assert_eq!(tokenize(with_comments), tokenize(without));
}

/// PROPERTY: Two comments on the SAME line collapse to one. The first
/// `;` swallows everything to the next `\n`, so a comment-inside-comment
/// cannot exist at the lexical layer.
#[test]
fn prop_tokenize_comment_swallows_to_eol() {
    // `;` covers `;`s within the same physical line.
    let src = "a ; outer ; still in same comment\nb";
    let toks = tokenize(src);
    assert_eq!(syms(&toks), vec!["a", "b"]);
}

/// PROPERTY: Tokens partition the source into a sequence of `(`, `)`,
/// and atoms; concatenating the lexeme-length of each token equals the
/// number of non-whitespace, non-comment bytes. (Bijectivity at the
/// lexeme→source-bytes level.) We sidestep |..| / "..." escape
/// subtleties by using only plain ASCII atoms.
#[test]
fn prop_tokenize_count_matches_simple_atom_input() {
    // 3 atoms, 2 parens, 8 whitespace bytes.
    let src = "(  foo  bar  baz  )";
    let toks = tokenize(src);
    // SMT-LIB syntax: parens are single bytes, atoms are contiguous
    // non-whitespace non-paren runs. So the token count must be 5.
    assert_eq!(toks.len(), 5);
    // And the parens flank the atoms.
    assert_eq!(toks.first(), Some(&Tok::LParen));
    assert_eq!(toks.last(), Some(&Tok::RParen));
}

/// PROPERTY: For every balanced source `s`, the number of `LParen`
/// tokens equals the number of `RParen` tokens. (Trivial counting
/// identity that holds for any well-formed S-expression input.)
#[test]
fn prop_tokenize_paren_count_balanced_for_balanced_input() {
    let cases = [
        "()",
        "(a)",
        "(a b)",
        "((a) (b) (c))",
        "(define-sort F () (_ FiniteField 7))",
    ];
    for s in cases {
        let toks = tokenize(s);
        let lp = toks.iter().filter(|t| matches!(t, Tok::LParen)).count();
        let rp = toks.iter().filter(|t| matches!(t, Tok::RParen)).count();
        assert_eq!(lp, rp, "paren imbalance in {:?}", s);
    }
}

/// PROPERTY: For any non-empty atom `a` containing no whitespace, no
/// `(`, `)`, `;`, or `|`, `tokenize(a)` is a single `Tok::Sym(a)` and
/// `parse_sexprs` recovers `Sexpr::Atom(a)`. (Round-trip identity for
/// the atom subset.)
#[test]
fn prop_atom_round_trip_under_tokenize_then_parse() {
    let atoms = [
        "x", "x_1", "ff.add", "ff.mul", "#f3m7", "ff-1", "ff15",
        "FiniteField", "_", "declare-fun", "=>", "<=",
    ];
    for a in atoms {
        let toks = tokenize(a);
        assert_eq!(toks.len(), 1, "atom {:?} produced != 1 token", a);
        match &toks[0] {
            Tok::Sym(s) => assert_eq!(s, a),
            other => panic!("atom {:?} not Sym; got {:?}", a, other),
        }
        let sexprs = parse_sexprs(&toks).expect("parse");
        assert_eq!(sexprs.len(), 1);
        match &sexprs[0] {
            Sexpr::Atom(s) => assert_eq!(s, a),
            other => panic!("expected Atom, got {:?}", other),
        }
    }
}

/// PROPERTY: `parse_sexprs` is the inverse of a manually rendered
/// S-expression up to leaf-name equality. For any tree `t` over the
/// `Atom(s)`/`List(...)` algebra (with paren-safe atoms), rendering `t`
/// with spaces between children and re-parsing recovers a tree with the
/// same shape and leaves. (Round-trip property of the parser.)
#[test]
fn prop_sexpr_render_then_reparse_recovers_shape() {
    fn render(s: &Sexpr) -> String {
        match s {
            Sexpr::Atom(a) => a.clone(),
            Sexpr::List(elts) => {
                let parts: Vec<String> = elts.iter().map(render).collect();
                format!("({})", parts.join(" "))
            }
        }
    }
    fn shape_eq(a: &Sexpr, b: &Sexpr) -> bool {
        match (a, b) {
            (Sexpr::Atom(x), Sexpr::Atom(y)) => x == y,
            (Sexpr::List(xs), Sexpr::List(ys)) => {
                xs.len() == ys.len()
                    && xs.iter().zip(ys.iter()).all(|(a, b)| shape_eq(a, b))
            }
            _ => false,
        }
    }
    // Hand-built trees over paren-safe atoms.
    let trees = vec![
        Sexpr::Atom("foo".into()),
        Sexpr::List(vec![]),
        Sexpr::List(vec![Sexpr::Atom("a".into()), Sexpr::Atom("b".into())]),
        Sexpr::List(vec![
            Sexpr::Atom("define-sort".into()),
            Sexpr::Atom("F".into()),
            Sexpr::List(vec![]),
            Sexpr::List(vec![
                Sexpr::Atom("_".into()),
                Sexpr::Atom("FiniteField".into()),
                Sexpr::Atom("7".into()),
            ]),
        ]),
    ];
    for t in trees {
        let rendered = render(&t);
        let toks = tokenize(&rendered);
        let parsed = parse_sexprs(&toks).expect("parse");
        assert_eq!(parsed.len(), 1, "render {:?} parsed wrong arity", rendered);
        assert!(
            shape_eq(&t, &parsed[0]),
            "round-trip lost shape for {:?}",
            rendered
        );
    }
}

/// PROPERTY: Concatenating two independent S-expression scripts yields
/// `parse_sexprs` output that is the concatenation of the per-script
/// outputs. (Top-level forms are independent — distributivity of
/// parse over `++`.)
#[test]
fn prop_parse_sexprs_distributes_over_concat() {
    let parts = ["(a b c)", "x", "(define-sort F () (_ FiniteField 7))"];
    let combined = parts.join(" ");
    let combined_parsed = parse_sexprs(&tokenize(&combined)).expect("parse");
    let mut concat: Vec<Sexpr> = Vec::new();
    for p in parts {
        let mut piece = parse_sexprs(&tokenize(p)).expect("parse");
        concat.append(&mut piece);
    }
    assert_eq!(concat.len(), combined_parsed.len());
    // Compare shape-wise (Debug strings carry no float / nondeterminism).
    for (a, b) in concat.iter().zip(combined_parsed.iter()) {
        assert_eq!(format!("{:?}", a), format!("{:?}", b));
    }
}

/// PROPERTY: `parse_sexprs(toks) == Ok(empty)` iff `toks` is empty —
/// modulo a sole comment or whitespace source. (Vacuous-input identity.)
#[test]
fn prop_empty_or_whitespace_only_input_parses_to_empty_vec() {
    for src in ["", "   ", "\n\n\n", ";just a comment\n", "  ;c1\n;c2\n  "] {
        let parsed = parse_sexprs(&tokenize(src)).expect("parse");
        assert!(parsed.is_empty(), "expected empty parse for {:?}", src);
    }
}

