use std::{borrow::Borrow, cmp::Ordering, iter::FromIterator, ops::RangeInclusive};

/// RangeSet provides a set-like interface that allows to search for items while
/// being constructed from and storing inclusive ranges in a compact fashion.
pub struct RangeSet<T> {
    ranges: Vec<RangeInclusive<T>>,
}

impl<T: Ord + Copy> From<Vec<RangeInclusive<T>>> for RangeSet<T> {
    // Convert from vector and prepare for binary search.
    fn from(mut ranges: Vec<RangeInclusive<T>>) -> Self {
        ranges.sort_unstable_by_key(|range| *range.start());
        // `dedup_by` invokes callback with mutable references, which allows not only
        // to remove same consecutive items, but also to provide custom merging
        // implementation which is exactly what we want for overlapping ranges.
        ranges.dedup_by(|b, a| {
            if b.start() <= a.end() {
                if b.end() > a.end() {
                    *a = *a.start()..=*b.end();
                }
                true
            } else {
                false
            }
        });
        RangeSet { ranges }
    }
}

impl<T: Ord + Copy> FromIterator<RangeInclusive<T>> for RangeSet<T> {
    fn from_iter<I: IntoIterator<Item = RangeInclusive<T>>>(ranges: I) -> Self {
        Vec::from_iter(ranges).into()
    }
}

impl<T> RangeSet<T> {
    /// Like [`HashSet::contains`](std::collections::HashSet::contains),
    /// checks whether any compatible type is in the set.
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.ranges
            .binary_search_by(|range| {
                if range.start().borrow() > value {
                    Ordering::Greater
                } else if range.end().borrow() >= value {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            })
            .is_ok()
    }
}
