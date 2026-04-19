use cvc5_ff_sys::*;
use std::fmt;
use std::marker::PhantomData;

/// The result of a synthesis query (SyGuS).
pub struct SynthResult<'tm> {
    pub(crate) inner: cvc5_ff_sys::SynthResult,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for SynthResult<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { synth_result_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for SynthResult<'_> {
    fn drop(&mut self) {
        unsafe { synth_result_release(self.inner) }
    }
}

impl<'tm> SynthResult<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::SynthResult) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Return `true` if this is a null (uninitialized) synthesis result.
    pub fn is_null(&self) -> bool {
        unsafe { synth_result_is_null(self.inner) }
    }

    /// Create a copy of this synthesis result (increments the internal reference count).
    pub fn copy(&self) -> SynthResult<'tm> {
        SynthResult::from_raw(unsafe { synth_result_copy(self.inner) })
    }

    /// Check disequality with another synthesis result.
    pub fn is_disequal(&self, other: &SynthResult) -> bool {
        unsafe { synth_result_is_disequal(self.inner, other.inner) }
    }

    /// Return `true` if a solution was found.
    pub fn has_solution(&self) -> bool {
        unsafe { synth_result_has_solution(self.inner) }
    }

    /// Return `true` if it was determined that no solution exists.
    pub fn has_no_solution(&self) -> bool {
        unsafe { synth_result_has_no_solution(self.inner) }
    }

    /// Return `true` if the synthesis result is unknown.
    pub fn is_unknown(&self) -> bool {
        unsafe { synth_result_is_unknown(self.inner) }
    }
}

impl fmt::Display for SynthResult<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { synth_result_to_string(self.inner) };
        let cs = unsafe { std::ffi::CStr::from_ptr(s) };
        write!(f, "{}", cs.to_string_lossy())
    }
}

impl PartialEq for SynthResult<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { synth_result_is_equal(self.inner, other.inner) }
    }
}

impl Eq for SynthResult<'_> {}

impl std::hash::Hash for SynthResult<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { synth_result_hash(self.inner) }.hash(state);
    }
}

impl fmt::Debug for SynthResult<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SynthResult({self})")
    }
}
