pub mod backends;
pub mod poly_ir;

/// Reserved variable names for field constants the witness post-
/// processor must filter out of solver-produced models. `p` is the
/// field prime; `ps1`..`ps5` are `p-1`..`p-5`; `zero` and `one` are
/// the obvious field elements.
pub const SUBP_CONSTANT_NAMES: &[&str] =
    &["p", "ps1", "ps2", "ps3", "ps4", "ps5", "zero", "one"];

/// Solver backend selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverKind {
    Z3,
    Cvc5,
    /// Native Rust finite field solver (Groebner basis).
    Native,
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

impl SolverKind {
    /// Canonical lowercase name. Matches the `name` field on the
    /// backend's `inventory::submit!`'d [`backends::SolverBackendDescriptor`]
    /// (except `None`, which never has a descriptor — it's the
    /// propagation-only sentinel).
    pub fn as_str(self) -> &'static str {
        match self {
            SolverKind::Z3 => "z3",
            SolverKind::Cvc5 => "cvc5",
            SolverKind::Native => "native",
            SolverKind::None => "none",
        }
    }
}

impl std::str::FromStr for SolverKind {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "z3" => Ok(SolverKind::Z3),
            "cvc5" => Ok(SolverKind::Cvc5),
            "native" => Ok(SolverKind::Native),
            "none" => Ok(SolverKind::None),
            _ => {
                // Surface every backend the inventory registry knows
                // about — if a downstream crate added one, the error
                // message includes it without manual maintenance.
                let mut known: Vec<&'static str> = backends::all_backend_descriptors()
                    .iter()
                    .map(|d| d.name)
                    .collect();
                known.sort();
                known.dedup();
                if !known.iter().any(|n| *n == "none") {
                    known.insert(0, "none");
                }
                Err(format!(
                    "unknown solver: '{}'. Known backends: {}",
                    s,
                    known.join(", ")
                ))
            }
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
        (SolverKind::Native, Theory::Nia) => {
            Err("native solver only supports finite field theory (QF_FF). Use --theory ff.".into())
        }
        (SolverKind::None, _) => Ok(()),
        _ => Ok(()),
    }
}

/// Create the appropriate solver backend for a solver+theory combination.
/// Returns `None` for `SolverKind::None` (propagation-only mode).
///
/// Dispatch is via the inventory registry of
/// [`backends::SolverBackendDescriptor`] entries: adding a new
/// `(name, theory)` pair is a new `inventory::submit!` block in the
/// new backend's file — no edits to this function required.
pub fn create_backend(
    solver: SolverKind,
    theory: Theory,
) -> Result<Option<Box<dyn backends::SolverBackend>>, String> {
    validate_combination(solver, theory)?;
    if solver == SolverKind::None {
        return Ok(None);
    }
    match backends::create_backend_by_name(solver.as_str(), theory) {
        Some(b) => Ok(Some(b)),
        None => Err(format!(
            "no registered backend for {:?} + {:?}",
            solver, theory
        )),
    }
}
