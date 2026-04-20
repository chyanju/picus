//! # cvc5
//!
//! Safe, high-level Rust bindings for the [cvc5](https://cvc5.github.io/) SMT solver.
//!
//! # Example
//!
//! ```rust
//! use cvc5_ff::{TermManager, Solver, Kind};
//!
//! let tm = TermManager::new();
//! let mut solver = Solver::new(&tm);
//!
//! solver.set_logic("QF_LIA");
//! solver.set_option("produce-models", "true");
//!
//! let int_sort = tm.integer_sort();
//! let x = tm.mk_const(int_sort, "x");
//! let zero = tm.mk_integer(0);
//!
//! let gt = tm.mk_term(Kind::Gt, &[x.clone(), zero]);
//! solver.assert_formula(gt);
//!
//! let result = solver.check_sat();
//! assert!(result.is_sat());
//!
//! let x_val = solver.get_value(x);
//! println!("x = {x_val}");
//! ```

mod datatype;
mod grammar;
mod op;
#[cfg(feature = "parser")]
mod parser;
mod proof;
mod result;
mod solver;
mod sort;
mod statistics;
mod synth_result;
mod term;
mod term_manager;

// Reexport enums
pub use cvc5_ff_sys::{
    BlockModelsMode, FindSynthTarget, Kind, LearnedLitType, OptionCategory, Plugin, ProofComponent,
    ProofFormat, ProofRewriteRule, ProofRule, RoundingMode, SkolemId, SortKind, UnknownExplanation,
};

pub use datatype::{
    Datatype, DatatypeConstructor, DatatypeConstructorDecl, DatatypeDecl, DatatypeSelector,
};
pub use grammar::Grammar;
pub use op::Op;
pub use proof::Proof;
pub use result::Result;
pub use solver::{OptionInfo, OptionInfoKind, Solver};
pub use sort::Sort;
pub use statistics::{Stat, Statistics};
pub use synth_result::SynthResult;
pub use term::Term;
pub use term_manager::TermManager;

#[cfg(feature = "parser")]
pub use cvc5_ff_sys::InputLanguage;
#[cfg(feature = "parser")]
pub use parser::{Command, InputParser, SymbolManager};

// Re-export PhantomData-related marker so users don't need to import it
// (the lifetime is inferred automatically in most cases)

/// Get a string representation of an [`InputLanguage`].
#[cfg(feature = "parser")]
pub fn input_language_to_string(lang: InputLanguage) -> String {
    unsafe {
        std::ffi::CStr::from_ptr(cvc5_ff_sys::modes_input_language_to_string(lang))
            .to_string_lossy()
            .into_owned()
    }
}

// ---------------------------------------------------------------------------
// String conversion helpers for re-exported enums
// ---------------------------------------------------------------------------

macro_rules! enum_to_string_fn {
    ($(#[$meta:meta])* $fn_name:ident, $ty:ty, $c_fn:path) => {
        $(#[$meta])*
        pub fn $fn_name(val: $ty) -> String {
            unsafe {
                std::ffi::CStr::from_ptr($c_fn(val))
                    .to_string_lossy()
                    .into_owned()
            }
        }
    };
}

enum_to_string_fn!(
    /// Get a string representation of a [`Kind`].
    kind_to_string, Kind, cvc5_ff_sys::kind_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`SortKind`].
    sort_kind_to_string, SortKind, cvc5_ff_sys::sort_kind_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`ProofRule`].
    proof_rule_to_string, ProofRule, cvc5_ff_sys::proof_rule_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`ProofRewriteRule`].
    proof_rewrite_rule_to_string, ProofRewriteRule, cvc5_ff_sys::proof_rewrite_rule_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`RoundingMode`].
    rounding_mode_to_string, RoundingMode, cvc5_ff_sys::rm_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`SkolemId`].
    skolem_id_to_string, SkolemId, cvc5_ff_sys::skolem_id_to_string
);
enum_to_string_fn!(
    /// Get a string representation of an [`UnknownExplanation`].
    unknown_explanation_to_string, UnknownExplanation, cvc5_ff_sys::unknown_explanation_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`BlockModelsMode`].
    block_models_mode_to_string, BlockModelsMode, cvc5_ff_sys::modes_block_models_mode_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`LearnedLitType`].
    learned_lit_type_to_string, LearnedLitType, cvc5_ff_sys::modes_learned_lit_type_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`ProofComponent`].
    proof_component_to_string, ProofComponent, cvc5_ff_sys::modes_proof_component_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`ProofFormat`].
    proof_format_to_string, ProofFormat, cvc5_ff_sys::modes_proof_format_to_string
);
enum_to_string_fn!(
    /// Get a string representation of a [`FindSynthTarget`].
    find_synth_target_to_string, FindSynthTarget, cvc5_ff_sys::modes_find_synth_target_to_string
);
