use std::{borrow::Borrow, iter::FromIterator, ops::RangeInclusive};

// RangeSet provides a set-like interface that allows to search for items while
// being constructed from and storing inclusive ranges in a compact fashion.
pub struct RangeSet<T> {
    ranges: Vec<RangeInclusive<T>>,
}

impl<T> From<Vec<RangeInclusive<T>>> for RangeSet<T> {
    fn from(ranges: Vec<RangeInclusive<T>>) -> Self {
        RangeSet { ranges }
    }
}

impl<T> FromIterator<RangeInclusive<T>> for RangeSet<T> {
    fn from_iter<I: IntoIterator<Item = RangeInclusive<T>>>(ranges: I) -> Self {
        Vec::from_iter(ranges).into()
    }
}

impl<T> RangeSet<T> {
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.ranges
            .iter()
            .any(|range| range.start().borrow() <= value && value <= range.end().borrow())
    }
}
