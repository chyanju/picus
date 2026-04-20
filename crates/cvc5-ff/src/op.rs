use cvc5_ff_sys::*;
use std::fmt;
use std::marker::PhantomData;

use crate::Term;

/// A cvc5 operator (indexed operator).
///
/// Operators are used to create terms with parameterized kinds, such as
/// bit-vector extract with specific indices.
pub struct Op<'tm> {
    pub(crate) inner: cvc5_ff_sys::Op,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for Op<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { op_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for Op<'_> {
    fn drop(&mut self) {
        unsafe { op_release(self.inner) }
    }
}

impl<'tm> Op<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::Op) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Get the kind of this operator.
    pub fn kind(&self) -> cvc5_ff_sys::Kind {
        unsafe { op_get_kind(self.inner) }
    }

    /// Create a copy of this operator (increments the internal reference count).
    pub fn copy(&self) -> Op<'tm> {
        Op::from_raw(unsafe { op_copy(self.inner) })
    }

    /// Check disequality with another operator.
    pub fn is_disequal(&self, other: &Op) -> bool {
        unsafe { op_is_disequal(self.inner, other.inner) }
    }

    /// Return `true` if this operator is indexed.
    pub fn is_indexed(&self) -> bool {
        unsafe { op_is_indexed(self.inner) }
    }

    /// Get the number of indices of this operator.
    pub fn num_indices(&self) -> usize {
        unsafe { op_get_num_indices(self.inner) }
    }

    /// Get the index at position `i` as a term.
    pub fn index(&self, i: usize) -> Term<'tm> {
        Term::from_raw(unsafe { op_get_index(self.inner, i) })
    }
}

impl fmt::Display for Op<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { op_to_string(self.inner) };
        let cs = unsafe { std::ffi::CStr::from_ptr(s) };
        write!(f, "{}", cs.to_string_lossy())
    }
}

impl fmt::Debug for Op<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Op({self})")
    }
}

impl PartialEq for Op<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { op_is_equal(self.inner, other.inner) }
    }
}

impl Eq for Op<'_> {}

impl std::hash::Hash for Op<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { op_hash(self.inner) }.hash(state);
    }
}
