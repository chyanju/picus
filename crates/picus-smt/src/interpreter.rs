//! SMT-LIB string generation from R1CS AST — interpreter for z3, cvc4, and cvc5.

use picus_r1cs::grammar::*;
use picus_r1cs::bn128_prime;

use crate::SolverKind;

/// Interpret an RCmds AST into an SMT-LIB2 string.
pub fn interpret_r1cs(cmds: &RCmds, solver: SolverKind) -> String {
    let mut out = String::new();
    for cmd in &cmds.commands {
        let s = interpret_cmd(cmd, solver);
        if !s.is_empty() {
            out.push_str(&s);
            out.push('\n');
        }
    }
    out
}

fn interpret_cmd(cmd: &RCmd, solver: SolverKind) -> String {
    match cmd {
        RCmd::Raw(s) => s.clone(),
        RCmd::Logic(s) => format!("(set-logic {})", s),
        RCmd::Def { var, typ } => format!("(declare-const {} {})", var, typ),
        RCmd::Assert(expr) => format!("(assert {})", interpret_expr(expr, solver)),
        RCmd::Comment(s) => format!("; {}", s),
        RCmd::Solve => "(check-sat)\n(get-model)".to_string(),
    }
}

fn interpret_expr(expr: &RExpr, solver: SolverKind) -> String {
    match solver {
        SolverKind::Z3 => interpret_expr_z3(expr),
        SolverKind::Cvc4 => interpret_expr_cvc4(expr),
        SolverKind::Cvc5 => interpret_expr_cvc5(expr),
    }
}

// ========================= Z3 interpreter =========================

fn interpret_expr_z3(expr: &RExpr) -> String {
    match expr {
        RExpr::Int(v) => v.to_string(),
        RExpr::Var(v) => v.clone(),
        RExpr::Eq(l, r) => format!("(= {} {})", interpret_expr_z3(l), interpret_expr_z3(r)),
        RExpr::Neq(l, r) => format!(
            "(not (= {} {}))",
            interpret_expr_z3(l),
            interpret_expr_z3(r)
        ),
        RExpr::Leq(l, r) => format!("(<= {} {})", interpret_expr_z3(l), interpret_expr_z3(r)),
        RExpr::Lt(l, r) => format!("(< {} {})", interpret_expr_z3(l), interpret_expr_z3(r)),
        RExpr::Geq(l, r) => format!("(>= {} {})", interpret_expr_z3(l), interpret_expr_z3(r)),
        RExpr::Gt(l, r) => format!("(> {} {})", interpret_expr_z3(l), interpret_expr_z3(r)),
        RExpr::And(vs) => fold_op("and", vs, SolverKind::Z3),
        RExpr::Or(vs) => fold_op("or", vs, SolverKind::Z3),
        RExpr::Imp(l, r) => format!("(=> {} {})", interpret_expr_z3(l), interpret_expr_z3(r)),
        RExpr::Add(vs) => fold_op("+", vs, SolverKind::Z3),
        RExpr::Sub(vs) => fold_op("-", vs, SolverKind::Z3),
        RExpr::Mul(vs) => fold_op("*", vs, SolverKind::Z3),
        RExpr::Neg(v) => format!("(- {})", interpret_expr_z3(v)),
        RExpr::Mod(v, m) => format!("(rem {} {})", interpret_expr_z3(v), interpret_expr_z3(m)),
    }
}

// ========================= CVC4 interpreter =========================

fn interpret_expr_cvc4(expr: &RExpr) -> String {
    match expr {
        RExpr::Mod(v, m) => format!("(mod {} {})", interpret_expr_cvc4(v), interpret_expr_cvc4(m)),
        // Everything else same as z3
        RExpr::Int(v) => v.to_string(),
        RExpr::Var(v) => v.clone(),
        RExpr::Eq(l, r) => format!("(= {} {})", interpret_expr_cvc4(l), interpret_expr_cvc4(r)),
        RExpr::Neq(l, r) => format!(
            "(not (= {} {}))",
            interpret_expr_cvc4(l),
            interpret_expr_cvc4(r)
        ),
        RExpr::Leq(l, r) => format!("(<= {} {})", interpret_expr_cvc4(l), interpret_expr_cvc4(r)),
        RExpr::Lt(l, r) => format!("(< {} {})", interpret_expr_cvc4(l), interpret_expr_cvc4(r)),
        RExpr::Geq(l, r) => format!("(>= {} {})", interpret_expr_cvc4(l), interpret_expr_cvc4(r)),
        RExpr::Gt(l, r) => format!("(> {} {})", interpret_expr_cvc4(l), interpret_expr_cvc4(r)),
        RExpr::And(vs) => fold_op("and", vs, SolverKind::Cvc4),
        RExpr::Or(vs) => fold_op("or", vs, SolverKind::Cvc4),
        RExpr::Imp(l, r) => format!("(=> {} {})", interpret_expr_cvc4(l), interpret_expr_cvc4(r)),
        RExpr::Add(vs) => fold_op("+", vs, SolverKind::Cvc4),
        RExpr::Sub(vs) => fold_op("-", vs, SolverKind::Cvc4),
        RExpr::Mul(vs) => fold_op("*", vs, SolverKind::Cvc4),
        RExpr::Neg(v) => format!("(- {})", interpret_expr_cvc4(v)),
    }
}

// ========================= CVC5 interpreter =========================

fn interpret_expr_cvc5(expr: &RExpr) -> String {
    let p = bn128_prime();
    match expr {
        RExpr::Int(v) => format!("#f{}m{}", v, p),
        RExpr::Var(v) => v.clone(),
        RExpr::Eq(l, r) => format!("(= {} {})", interpret_expr_cvc5(l), interpret_expr_cvc5(r)),
        RExpr::Neq(l, r) => format!(
            "(not (= {} {}))",
            interpret_expr_cvc5(l),
            interpret_expr_cvc5(r)
        ),
        RExpr::And(vs) => fold_op("and", vs, SolverKind::Cvc5),
        RExpr::Or(vs) => fold_op("or", vs, SolverKind::Cvc5),
        RExpr::Imp(l, r) => format!("(=> {} {})", interpret_expr_cvc5(l), interpret_expr_cvc5(r)),
        RExpr::Add(vs) => fold_op("ff.add", vs, SolverKind::Cvc5),
        RExpr::Mul(vs) => fold_op("ff.mul", vs, SolverKind::Cvc5),
        _ => panic!("CVC5 interpreter does not support: {:?}", expr),
    }
}

// ========================= Helpers =========================

/// Fold a list of expressions into nested binary applications: `(op (op a b) c)`.
fn fold_op(op: &str, vs: &[RExpr], solver: SolverKind) -> String {
    if vs.is_empty() {
        return String::new();
    }
    if vs.len() == 1 {
        return interpret_expr(&vs[0], solver);
    }

    let mut result = interpret_expr(&vs[0], solver);
    for v in &vs[1..] {
        let right = interpret_expr(v, solver);
        result = format!("({} {} {})", op, result, right);
    }
    result
}
