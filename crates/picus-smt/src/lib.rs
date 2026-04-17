pub mod interpreter;
pub mod optimizer;
pub mod solver;
pub mod r1cs_parser;

/// Solver backend selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverKind {
    Z3,
    Cvc4,
    Cvc5,
}

impl std::str::FromStr for SolverKind {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "z3" => Ok(SolverKind::Z3),
            "cvc4" => Ok(SolverKind::Cvc4),
            "cvc5" => Ok(SolverKind::Cvc5),
            _ => Err(format!("unknown solver: {}", s)),
        }
    }
}
