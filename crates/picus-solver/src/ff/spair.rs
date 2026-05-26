//! S-pair representation for the Buchberger algorithm.

use super::divmask::DivMask;
use super::monomial::Monomial;

/// A critical S-pair to be processed in Buchberger's algorithm.
#[derive(Clone, Debug)]
pub struct SPair {
    pub i: usize,
    pub j: usize,
    pub sugar: u32,
    pub lcm: Monomial,
    pub lcm_divmask: DivMask,
    pub lcm_deg: u32,
    pub age: u64,
    /// Generation tag for incremental support — see `IncrementalGB`.
    pub generation: u32,
    /// True iff `LM(i)` and `LM(j)` are coprime; the S-polynomial then
    /// reduces to zero by Buchberger's product criterion. Coprime pairs
    /// are kept in the queue during the M-criterion walk so they can
    /// dominate non-coprime pairs, and are filtered out before the
    /// queue is merged into `open` so the reduction loop never sees
    /// them.
    pub is_coprime: bool,
}

impl SPair {
    /// Tuple used for ordering in the priority queue: `(sugar, lcm_deg, age)`.
    /// Smaller is better (so `BinaryHeap` users wrap with `Reverse`).
    #[inline]
    pub fn ordering_key(&self) -> (u32, u32, u64) {
        (self.sugar, self.lcm_deg, self.age)
    }
}

impl PartialEq for SPair {
    fn eq(&self, other: &Self) -> bool {
        self.ordering_key() == other.ordering_key()
    }
}

impl Eq for SPair {}

impl PartialOrd for SPair {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SPair {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.ordering_key().cmp(&other.ordering_key())
    }
}

impl super::spair_criteria::CriterionPair for SPair {
    type Mono = Monomial;
    fn lcm(&self) -> &Monomial {
        &self.lcm
    }
    fn lcm_divmask(&self) -> DivMask {
        self.lcm_divmask
    }
    fn is_coprime(&self) -> bool {
        self.is_coprime
    }
    fn parents(&self) -> (usize, usize) {
        (self.i, self.j)
    }
    fn cmp_key(&self) -> (u32, u32, u64) {
        self.ordering_key()
    }
}
