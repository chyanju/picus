//! SMT-LIB v2 QF_FF source builders for benches and the `cvc5_compare`
//! binary. Each builder returns a self-contained SMT-LIB script.
//! All builders target GF(101).

pub const HEADER_P101: &str = "(set-logic QF_FF)\n(define-sort F () (_ FiniteField 101))\n";
pub const FOOTER: &str = "(check-sat)\n";

pub fn conjunction(n: usize) -> String {
    let mut s = String::from(HEADER_P101);
    for i in 0..n {
        s.push_str(&format!("(declare-fun a{} () F)\n", i));
    }
    for i in 0..n {
        s.push_str(&format!("(assert (= a{} (as ff{} F)))\n", i, i % 100));
    }
    s.push_str(FOOTER);
    s
}

pub fn single_or(k: usize) -> String {
    let mut s = String::from(HEADER_P101);
    s.push_str("(declare-fun x () F)\n");
    s.push_str("(assert (or");
    for i in 0..k {
        s.push_str(&format!(" (= x (as ff{} F))", i));
    }
    s.push_str("))\n");
    s.push_str(FOOTER);
    s
}

pub fn disj_bit(n: usize) -> String {
    let mut s = String::from(HEADER_P101);
    for i in 0..n {
        s.push_str(&format!("(declare-fun x{} () F)\n", i));
    }
    for i in 0..n {
        s.push_str(&format!(
            "(assert (or (= x{} (as ff0 F)) (= x{} (as ff1 F))))\n",
            i, i,
        ));
    }
    s.push_str(FOOTER);
    s
}

pub fn and_of_ors_sat(n: usize) -> String {
    let mut s = String::from(HEADER_P101);
    for i in 0..n {
        s.push_str(&format!("(declare-fun a{} () F)\n", i));
    }
    for i in 0..n {
        s.push_str(&format!(
            "(assert (or (= a{} (as ff0 F)) (= a{} (as ff1 F))))\n",
            i, i,
        ));
    }
    s.push_str(FOOTER);
    s
}

pub fn and_of_ors_unsat(n: usize) -> String {
    let mut s = String::from(HEADER_P101);
    for i in 0..n {
        s.push_str(&format!("(declare-fun a{} () F)\n", i));
    }
    for i in 0..n {
        s.push_str(&format!(
            "(assert (or (= a{} (as ff0 F)) (= a{} (as ff1 F))))\n",
            i, i,
        ));
    }
    s.push_str("(assert (= a0 (as ff2 F)))\n");
    s.push_str(FOOTER);
    s
}

pub fn implies_chain_unsat(depth: usize) -> String {
    let mut s = String::from(HEADER_P101);
    for i in 0..=depth {
        s.push_str(&format!("(declare-fun x{} () F)\n", i));
    }
    s.push_str("(assert (= x0 (as ff0 F)))\n");
    for i in 0..depth {
        s.push_str(&format!(
            "(assert (=> (= x{} (as ff0 F)) (= x{} (as ff0 F))))\n",
            i,
            i + 1,
        ));
    }
    s.push_str(&format!("(assert (not (= x{} (as ff0 F))))\n", depth));
    s.push_str(FOOTER);
    s
}

pub fn bit_sum(n: usize, target: u64) -> String {
    let mut s = String::from(HEADER_P101);
    for i in 0..n {
        s.push_str(&format!("(declare-fun a{} () F)\n", i));
    }
    for i in 0..n {
        s.push_str(&format!(
            "(assert (or (= a{} (as ff0 F)) (= a{} (as ff1 F))))\n",
            i, i,
        ));
    }
    s.push_str("(assert (= (ff.add ");
    for i in 0..n {
        s.push_str(&format!("a{} ", i));
    }
    s.push_str(&format!(") (as ff{} F)))\n", target));
    s.push_str(FOOTER);
    s
}

pub fn random_3cnf(n_vars: usize, n_clauses: usize, seed: u64) -> String {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut s = String::from(HEADER_P101);
    for i in 0..n_vars {
        s.push_str(&format!("(declare-fun x{} () F)\n", i));
    }
    for _ in 0..n_clauses {
        s.push_str("(assert (or");
        for _ in 0..3 {
            let v = (next() as usize) % n_vars;
            let neg = next() & 1 == 1;
            let lit = format!(" (= x{} (as ff{} F))", v, v % 100);
            if neg {
                s.push_str(" (not");
                s.push_str(&lit);
                s.push(')');
            } else {
                s.push_str(&lit);
            }
        }
        s.push_str("))\n");
    }
    s.push_str(FOOTER);
    s
}

pub fn or_of_ands(n: usize) -> String {
    let mut s = String::from(HEADER_P101);
    for i in 0..(2 * n) {
        s.push_str(&format!("(declare-fun y{} () F)\n", i));
    }
    s.push_str("(assert (or");
    for i in 0..n {
        s.push_str(&format!(
            " (and (= y{} (as ff{} F)) (= y{} (as ff{} F)))",
            2 * i,
            i % 100,
            2 * i + 1,
            (i + 1) % 100,
        ));
    }
    s.push_str("))\n");
    s.push_str(FOOTER);
    s
}

/// Bounded-cost subset of [`corpus`] (drops `random_3cnf` cases with
/// `vars >= 8`, which without theory propagation can take many
/// seconds in CDCL(T) and add multi-minute wall to a comparison
/// sweep). Use this from the `cvc5_compare` binary.
pub fn corpus_bounded() -> Vec<(&'static str, String, String)> {
    corpus()
        .into_iter()
        .filter(|(family, label, _)| {
            !(*family == "random_3cnf"
                && (label.starts_with("vars=8") || label.starts_with("vars=10")))
        })
        .collect()
}

/// Full bench corpus as `(family, label, source)` triples.
pub fn corpus() -> Vec<(&'static str, String, String)> {
    let mut out: Vec<(&'static str, String, String)> = Vec::new();

    for n in [1usize, 3, 6, 10] {
        out.push(("conjunction", format!("n={}", n), conjunction(n)));
    }
    for k in [2usize, 4, 8, 16] {
        out.push(("single_or", format!("k={}", k), single_or(k)));
    }
    for n in [1usize, 4, 8, 16] {
        out.push(("disj_bit", format!("n={}", n), disj_bit(n)));
    }
    for n in [3usize, 5, 7, 9] {
        let l = format!("n={}_dnf={}", n, 1usize << n);
        out.push(("and_of_ors_sat", l, and_of_ors_sat(n)));
    }
    for n in [3usize, 5, 7, 9, 11] {
        let l = format!("n={}_dnf={}", n, 1usize << n);
        out.push(("and_of_ors_unsat", l, and_of_ors_unsat(n)));
    }
    for d in [1usize, 3, 6, 10] {
        out.push((
            "implies_chain_unsat",
            format!("depth={}", d),
            implies_chain_unsat(d),
        ));
    }
    for &(n, t, sat) in &[
        (4usize, 2u64, true),
        (4, 99, false),
        (6, 3, true),
        (6, 99, false),
        (8, 4, true),
        (8, 99, false),
    ] {
        let kind = if sat { "sat" } else { "unsat" };
        out.push((
            "bit_sum",
            format!("n={}_t={}_{}", n, t, kind),
            bit_sum(n, t),
        ));
    }
    for &(nv, nc) in &[(4usize, 8usize), (6, 12), (8, 16), (10, 30)] {
        out.push((
            "random_3cnf",
            format!("vars={}_clauses={}", nv, nc),
            random_3cnf(nv, nc, 0xCAFEBABE),
        ));
    }
    for n in [2usize, 4, 8] {
        out.push(("or_of_ands_sat", format!("n={}", n), or_of_ands(n)));
    }
    out
}
