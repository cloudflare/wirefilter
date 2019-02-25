use std::cmp::Ordering;

/// Strict version of PartialOrd that can define different enum items as
/// incomparable.
pub trait StrictPartialOrd<Rhs: ?Sized = Self>: PartialOrd<Rhs> {
    fn strict_partial_cmp(&self, other: &Rhs) -> Option<Ordering> {
        self.partial_cmp(other)
    }
}
