use cvc5_ff_sys::*;
use std::fmt;
use std::marker::PhantomData;

/// The result of a satisfiability check.
pub struct Result<'tm> {
    pub(crate) inner: cvc5_ff_sys::Result,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for Result<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { result_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for Result<'_> {
    fn drop(&mut self) {
        unsafe { result_release(self.inner) }
    }
}

impl<'tm> Result<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::Result) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Return `true` if this is a null (uninitialized) result.
    pub fn is_null(&self) -> bool {
        unsafe { result_is_null(self.inner) }
    }

    /// Create a copy of this result (increments the internal reference count).
    pub fn copy(&self) -> Result<'tm> {
        Result::from_raw(unsafe { result_copy(self.inner) })
    }

    /// Check disequality with another result.
    pub fn is_disequal(&self, other: &Result) -> bool {
        unsafe { result_is_disequal(self.inner, other.inner) }
    }

    /// Return `true` if the query was satisfiable.
    pub fn is_sat(&self) -> bool {
        unsafe { result_is_sat(self.inner) }
    }

    /// Return `true` if the query was unsatisfiable.
    pub fn is_unsat(&self) -> bool {
        unsafe { result_is_unsat(self.inner) }
    }

    /// Return `true` if the result is unknown.
    pub fn is_unknown(&self) -> bool {
        unsafe { result_is_unknown(self.inner) }
    }

    /// Get the explanation for an unknown result.
    pub fn unknown_explanation(&self) -> cvc5_ff_sys::UnknownExplanation {
        unsafe { result_get_unknown_explanation(self.inner) }
    }
}

impl fmt::Display for Result<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { result_to_string(self.inner) };
        let cs = unsafe { std::ffi::CStr::from_ptr(s) };
        write!(f, "{}", cs.to_string_lossy())
    }
}

impl fmt::Debug for Result<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Result({self})")
    }
}

impl PartialEq for Result<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { result_is_equal(self.inner, other.inner) }
    }
}

impl Eq for Result<'_> {}

impl std::hash::Hash for Result<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { result_hash(self.inner) }.hash(state);
    }
}
