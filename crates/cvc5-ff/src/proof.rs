use cvc5_ff_sys::*;
use std::fmt;
use std::marker::PhantomData;

use crate::Term;

/// A cvc5 proof object.
///
/// Proofs are produced when the solver is configured with
/// `set_option("produce-proofs", "true")` and a query returns unsat.
pub struct Proof<'tm> {
    pub(crate) inner: cvc5_ff_sys::Proof,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for Proof<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { proof_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for Proof<'_> {
    fn drop(&mut self) {
        unsafe { proof_release(self.inner) }
    }
}

impl<'tm> Proof<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::Proof) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Get the proof rule used at the root of this proof node.
    pub fn rule(&self) -> cvc5_ff_sys::ProofRule {
        unsafe { proof_get_rule(self.inner) }
    }

    /// Create a copy of this proof (increments the internal reference count).
    pub fn copy(&self) -> Proof<'tm> {
        Proof::from_raw(unsafe { proof_copy(self.inner) })
    }

    /// Check disequality with another proof.
    pub fn is_disequal(&self, other: &Proof) -> bool {
        unsafe { proof_is_disequal(self.inner, other.inner) }
    }

    /// Get the rewrite rule used at the root of this proof node.
    pub fn rewrite_rule(&self) -> cvc5_ff_sys::ProofRewriteRule {
        unsafe { proof_get_rewrite_rule(self.inner) }
    }

    /// Get the conclusion (result) of this proof node as a term.
    pub fn result(&self) -> Term<'tm> {
        Term::from_raw(unsafe { proof_get_result(self.inner) })
    }

    /// Get the child proof nodes.
    pub fn children(&self) -> Vec<Proof<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { proof_get_children(self.inner, &mut size) };
        (0..size)
            .map(|i| Proof::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Get the arguments of this proof node as terms.
    pub fn arguments(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { proof_get_arguments(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }
}

impl PartialEq for Proof<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { proof_is_equal(self.inner, other.inner) }
    }
}

impl Eq for Proof<'_> {}

impl std::hash::Hash for Proof<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { proof_hash(self.inner) }.hash(state);
    }
}

impl fmt::Debug for Proof<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Proof({:?})", self.rule())
    }
}
