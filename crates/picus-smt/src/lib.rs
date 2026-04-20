pub mod backends;
pub mod query;
pub mod r1cs_parser;
pub mod optimizer;

/// Solver backend selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverKind {
    Z3,
    Cvc5,
    /// No solver — propagation only.
    None,
}

/// Theory selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Theory {
    /// QF_FF: native finite field arithmetic (cvc5 only).
    Ff,
    /// QF_NIA: nonlinear integer arithmetic with mod p.
    Nia,
}

impl std::str::FromStr for SolverKind {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "z3" => Ok(SolverKind::Z3),
            "cvc5" => Ok(SolverKind::Cvc5),
            "none" => Ok(SolverKind::None),
            _ => Err(format!("unknown solver: '{}'. Use 'z3', 'cvc5', or 'none'.", s)),
        }
    }
}

impl std::str::FromStr for Theory {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "ff" => Ok(Theory::Ff),
            "nia" => Ok(Theory::Nia),
            _ => Err(format!("unknown theory: '{}'. Use 'ff' or 'nia'.", s)),
        }
    }
}

/// Check if a solver+theory combination is valid.
pub fn validate_combination(solver: SolverKind, theory: Theory) -> Result<(), String> {
    match (solver, theory) {
        (SolverKind::Z3, Theory::Ff) => {
            Err("z3 does not support finite field theory (QF_FF). Use --theory nia, or switch to --solver cvc5.".into())
        }
        (SolverKind::None, _) => Ok(()),
        _ => Ok(()),
    }
}

/// Create the appropriate solver backend for a solver+theory combination.
/// Returns `None` for `SolverKind::None` (propagation-only mode).
pub fn create_backend(
    solver: SolverKind,
    theory: Theory,
) -> Result<Option<Box<dyn backends::SolverBackend>>, String> {
    validate_combination(solver, theory)?;
    match (solver, theory) {
        (SolverKind::Z3, Theory::Nia) => Ok(Some(Box::new(backends::z3_nia::Z3NiaBackend::new()))),
        (SolverKind::Cvc5, Theory::Ff) => Ok(Some(Box::new(backends::cvc5_ff::Cvc5FfBackend::new()))),
        (SolverKind::Cvc5, Theory::Nia) => Ok(Some(Box::new(backends::cvc5_nia::Cvc5NiaBackend::new()))),
        (SolverKind::None, _) => Ok(None),
        _ => Err(format!("unsupported combination: {:?} + {:?}", solver, theory)),
    }
}
