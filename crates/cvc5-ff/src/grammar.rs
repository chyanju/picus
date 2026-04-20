use cvc5_ff_sys::*;
use std::fmt;
use std::marker::PhantomData;

use crate::Term;

/// A cvc5 grammar for syntax-guided synthesis (SyGuS).
///
/// Grammars constrain the space of candidate solutions in synthesis queries.
pub struct Grammar<'tm> {
    pub(crate) inner: cvc5_ff_sys::Grammar,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for Grammar<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { grammar_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for Grammar<'_> {
    fn drop(&mut self) {
        unsafe { grammar_release(self.inner) }
    }
}

impl<'tm> Grammar<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::Grammar) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Create a copy of this grammar (increments the internal reference count).
    pub fn copy(&self) -> Grammar<'tm> {
        Grammar::from_raw(unsafe { grammar_copy(self.inner) })
    }

    /// Check disequality with another grammar.
    pub fn is_disequal(&self, other: &Grammar) -> bool {
        unsafe { grammar_is_disequal(self.inner, other.inner) }
    }

    /// Add a rule to the given non-terminal symbol.
    pub fn add_rule(&mut self, symbol: Term, rule: Term) {
        unsafe { grammar_add_rule(self.inner, symbol.inner, rule.inner) }
    }

    /// Add rules to the given non-terminal symbol.
    pub fn add_rules(&mut self, symbol: Term, rules: &[Term]) {
        let raw: Vec<cvc5_ff_sys::Term> = rules.iter().map(|t| t.inner).collect();
        unsafe { grammar_add_rules(self.inner, symbol.inner, raw.len(), raw.as_ptr()) }
    }

    /// Allow the symbol to be an arbitrary constant.
    pub fn add_any_constant(&mut self, symbol: Term) {
        unsafe { grammar_add_any_constant(self.inner, symbol.inner) }
    }

    /// Allow the symbol to be any input variable.
    pub fn add_any_variable(&mut self, symbol: Term) {
        unsafe { grammar_add_any_variable(self.inner, symbol.inner) }
    }
}

impl fmt::Display for Grammar<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { grammar_to_string(self.inner) };
        let cs = unsafe { std::ffi::CStr::from_ptr(s) };
        write!(f, "{}", cs.to_string_lossy())
    }
}

impl PartialEq for Grammar<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { grammar_is_equal(self.inner, other.inner) }
    }
}

impl Eq for Grammar<'_> {}

impl std::hash::Hash for Grammar<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { grammar_hash(self.inner) }.hash(state);
    }
}

impl fmt::Debug for Grammar<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Grammar({self})")
    }
}
