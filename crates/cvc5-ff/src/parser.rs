//! Safe wrappers for the cvc5 parser API.
//!
//! This module is only available when the `parser` feature is enabled.
//!
//! # Example
//!
//! ```rust
//! use cvc5::{TermManager, Solver, InputParser, SymbolManager, InputLanguage};
//!
//! let tm = TermManager::new();
//! let solver = Solver::new(&tm);
//! let mut sm = SymbolManager::new(&tm);
//!
//! let mut parser = InputParser::new(solver, Some(&sm));
//! parser.set_str_input(
//!     InputLanguage::SmtLib26,
//!     "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(check-sat)",
//!     "example",
//! );
//!
//! while !parser.done() {
//!     match parser.next_command() {
//!         Ok(Some(cmd)) => { cmd.invoke(parser.get_solver(), &mut sm); }
//!         Ok(None) => break,
//!         Err(e) => panic!("parse error: {e}"),
//!     }
//! }
//! ```

use cvc5_ff_sys::InputLanguage;
use cvc5_ff_sys::parser::*;
use std::ffi::CString;
use std::fmt;
use std::rc::Rc;

use crate::{Solver, Sort, Term, TermManager};

struct RawSymbolManager(*mut cvc5_ff_sys::parser::SymbolManager);
impl RawSymbolManager {
    fn new(tm: *mut cvc5_ff_sys::TermManager) -> Self {
        Self(unsafe { symbol_manager_new(tm) })
    }
}

impl Drop for RawSymbolManager {
    fn drop(&mut self) {
        unsafe { symbol_manager_delete(self.0) };
    }
}

// ---------------------------------------------------------------------------
// SymbolManager
// ---------------------------------------------------------------------------

/// Manages symbols for the parser.
///
/// Internally tracks a symbol table and meta-information from SMT-LIB inputs
/// (named assertions, declared functions/sorts, etc.).
///
/// A `SymbolManager` can be shared with an [`InputParser`] so that parsed
/// commands update the same symbol table.
#[derive(Clone)]
pub struct SymbolManager {
    inner: Rc<RawSymbolManager>,
    tm: TermManager,
}

impl SymbolManager {
    /// Create a new symbol manager associated with the given term manager.
    pub fn new(tm: impl std::borrow::Borrow<TermManager>) -> Self {
        let tm = tm.borrow().clone();
        Self {
            inner: Rc::new(RawSymbolManager::new(tm.ptr())),
            tm,
        }
    }

    pub(crate) fn ptr(&self) -> *mut cvc5_ff_sys::parser::SymbolManager {
        self.inner.0
    }

    /// Return the underlying term manager
    pub fn term_manager(&self) -> TermManager {
        self.tm.clone()
    }

    /// Return whether the logic has been set.
    pub fn is_logic_set(&self) -> bool {
        unsafe { sm_is_logic_set(self.ptr()) }
    }

    /// Get the logic string (e.g. `"QF_LIA"`).
    ///
    /// # Panics
    ///
    /// The underlying C API asserts that the logic has been set.
    pub fn get_logic(&self) -> &str {
        unsafe {
            let s = sm_get_logic(self.ptr());
            std::ffi::CStr::from_ptr(s).to_str().unwrap_or("")
        }
    }

    /// Get the sorts declared via `declare-sort` commands.
    ///
    /// These are the sorts printed as part of a `get-model` response.
    pub fn get_declared_sorts(&self) -> Vec<Sort<'_>> {
        let mut size = 0usize;
        let ptr = unsafe { sm_get_declared_sorts(self.ptr(), &mut size) };
        (0..size)
            .map(|i| Sort::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Get the terms declared via `declare-fun` and `declare-const` commands.
    ///
    /// These are the terms printed in a `get-model` response.
    pub fn get_declared_terms(&self) -> Vec<Term<'_>> {
        let mut size = 0usize;
        let ptr = unsafe { sm_get_declared_terms(self.ptr(), &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Get terms that have been given names via the `:named` attribute.
    ///
    /// Returns a list of `(term, name)` pairs.
    pub fn get_named_terms(&self) -> Vec<(Term<'_>, String)> {
        let mut size = 0usize;
        let mut terms: *mut cvc5_ff_sys::Term = std::ptr::null_mut();
        let mut names: *mut *const std::os::raw::c_char = std::ptr::null_mut();
        unsafe { sm_get_named_terms(self.ptr(), &mut size, &mut terms, &mut names) };
        (0..size)
            .map(|i| unsafe {
                let t = Term::from_raw(*terms.add(i));
                let n = std::ffi::CStr::from_ptr(*names.add(i))
                    .to_string_lossy()
                    .into_owned();
                (t, n)
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Command
// ---------------------------------------------------------------------------

/// A parsed command (e.g. `assert`, `check-sat`, `declare-const`).
///
/// Commands are produced by [`InputParser::next_command`] and can be executed
/// on a solver and symbol manager via [`Command::invoke`].
pub struct Command {
    pub(crate) inner: cvc5_ff_sys::parser::Command,
}

impl Command {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::parser::Command) -> Self {
        Self { inner: raw }
    }

    /// Return `true` if this is a null (empty) command.
    pub fn is_null(&self) -> bool {
        self.inner.is_null()
    }

    /// Execute this command on the given solver and symbol manager.
    ///
    /// Returns any output produced by the command (e.g. `sat`, `unsat`,
    /// model output, etc.).
    pub fn invoke(&self, solver: &mut Solver<'_>, sm: &mut SymbolManager) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(cmd_invoke(self.inner, solver.inner, sm.ptr()))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Get the name of this command (e.g. `"assert"`, `"check-sat"`).
    pub fn name(&self) -> &str {
        unsafe {
            let s = cmd_get_name(self.inner);
            std::ffi::CStr::from_ptr(s).to_str().unwrap_or("")
        }
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { cmd_to_string(self.inner) };
        let cs = unsafe { std::ffi::CStr::from_ptr(s) };
        write!(f, "{}", cs.to_string_lossy())
    }
}

impl fmt::Debug for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Command({self})")
    }
}

// ---------------------------------------------------------------------------
// InputParser
// ---------------------------------------------------------------------------

/// Parses SMT-LIB or SyGuS input into commands and terms.
///
/// After construction, configure an input source with one of:
/// - [`set_file_input`](InputParser::set_file_input) — read from a file
/// - [`set_str_input`](InputParser::set_str_input) — read from a string
/// - [`set_inc_str_input`](InputParser::set_inc_str_input) +
///   [`append_inc_str_input`](InputParser::append_inc_str_input) — incremental string feeding
///
/// Then call [`next_command`](InputParser::next_command) or
/// [`next_term`](InputParser::next_term) in a loop until
/// [`done`](InputParser::done) returns `true`.
pub struct InputParser<'tm> {
    inner: *mut cvc5_ff_sys::parser::InputParser,
    /// This field is public for reclaiming the ownership of the solver
    pub solver: Solver<'tm>,
    sm: SymbolManager,
}

impl<'tm> InputParser<'tm> {
    /// Create a new input parser.
    ///
    /// - `solver` — the solver that parsed commands will target.
    /// - `sm` — an optional symbol manager. If `None`, the parser creates its
    ///   own (initially empty) symbol manager internally.
    ///
    /// If both the solver and symbol manager have their logic set, the logics
    /// must be the same.
    pub fn new(solver: Solver<'tm>, sm: Option<impl std::borrow::Borrow<SymbolManager>>) -> Self {
        let sm = sm
            .map(|sm| sm.borrow().clone())
            .unwrap_or_else(|| SymbolManager::new(&solver.tm));
        let sm_ptr = sm.ptr();
        Self {
            inner: unsafe { parser_new(solver.inner, sm_ptr) },
            solver,
            sm,
        }
    }

    /// Return a mutable reference to the solver associated with this parser.
    pub fn get_solver(&mut self) -> &mut Solver<'tm> {
        &mut self.solver
    }

    /// Get the symbol manager associated with this parser.
    ///
    /// If no symbol manager was provided at construction, the parser creates
    /// one internally and this method returns it.
    pub fn get_symbol_manager(&self) -> SymbolManager {
        self.sm.clone()
    }

    /// Configure a file as the input source.
    ///
    /// - `lang` — the input language (e.g.
    ///   [`SmtLib26`](cvc5_ff_sys::InputLanguage::SmtLib26)).
    /// - `filename` — path to the file.
    pub fn set_file_input(&mut self, lang: InputLanguage, filename: &str) {
        let f = CString::new(filename).unwrap();
        unsafe { parser_set_file_input(self.inner, lang, f.as_ptr()) }
    }

    /// Configure a concrete string as the input source.
    ///
    /// - `lang` — the input language.
    /// - `input` — the input string to parse.
    /// - `name` — a name used in error messages (e.g. `"<stdin>"`).
    pub fn set_str_input(&mut self, lang: InputLanguage, input: &str, name: &str) {
        let i = CString::new(input).unwrap();
        let n = CString::new(name).unwrap();
        unsafe { parser_set_str_input(self.inner, lang, i.as_ptr(), n.as_ptr()) }
    }

    /// Configure incremental string input mode.
    ///
    /// After calling this, feed input with
    /// [`append_inc_str_input`](InputParser::append_inc_str_input).
    ///
    /// - `lang` — the input language.
    /// - `name` — a name used in error messages.
    pub fn set_inc_str_input(&mut self, lang: InputLanguage, name: &str) {
        let n = CString::new(name).unwrap();
        unsafe { parser_set_inc_str_input(self.inner, lang, n.as_ptr()) }
    }

    /// Append a string to the incremental input stream.
    ///
    /// Must be called after [`set_inc_str_input`](InputParser::set_inc_str_input).
    pub fn append_inc_str_input(&mut self, input: &str) {
        let i = CString::new(input).unwrap();
        unsafe { parser_append_inc_str_input(self.inner, i.as_ptr()) }
    }

    /// Parse and return the next command.
    ///
    /// Returns:
    /// - `Ok(Some(cmd))` — a successfully parsed command.
    /// - `Ok(None)` — no more commands (end of input).
    /// - `Err(msg)` — a parse error with the error message.
    ///
    /// If no logic has been set, the first command that requires one will
    /// initialize the logic to `"ALL"`.
    pub fn next_command(&mut self) -> std::result::Result<Option<Command>, String> {
        let mut error_msg: *const std::os::raw::c_char = std::ptr::null();
        let cmd = unsafe { parser_next_command(self.inner, &mut error_msg) };
        if !error_msg.is_null() {
            let msg = unsafe { std::ffi::CStr::from_ptr(error_msg) }
                .to_string_lossy()
                .into_owned();
            return Err(msg);
        }
        if cmd.is_null() {
            Ok(None)
        } else {
            Ok(Some(Command::from_raw(cmd)))
        }
    }

    /// Parse and return the next term.
    ///
    /// Returns:
    /// - `Ok(Some(term))` — a successfully parsed term.
    /// - `Ok(None)` — no more terms (end of input).
    /// - `Err(msg)` — a parse error with the error message.
    ///
    /// The logic must be set before calling this method.
    pub fn next_term(&mut self) -> std::result::Result<Option<Term<'_>>, String> {
        let mut error_msg: *const std::os::raw::c_char = std::ptr::null();
        let term = unsafe { parser_next_term(self.inner, &mut error_msg) };
        if !error_msg.is_null() {
            let msg = unsafe { std::ffi::CStr::from_ptr(error_msg) }
                .to_string_lossy()
                .into_owned();
            return Err(msg);
        }
        if term.is_null() {
            Ok(None)
        } else {
            Ok(Some(Term::from_raw(term)))
        }
    }

    /// Return `true` if the parser has finished reading all input.
    pub fn done(&self) -> bool {
        unsafe { parser_done(self.inner) }
    }
}

impl Drop for InputParser<'_> {
    fn drop(&mut self) {
        unsafe { parser_delete(self.inner) }
    }
}
