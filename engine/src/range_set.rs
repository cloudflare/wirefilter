use std::borrow::Borrow;
use std::cmp::Ordering;
use std::iter::FromIterator;
use std::ops::RangeInclusive;

/// RangeSet provides a set-like interface that allows to search for items while
/// being constructed from and storing inclusive ranges in a compact fashion.
pub struct RangeSet<T> {
    // Only endpoints are needed for lookup, not RangeInclusive's iterator state.
    ranges: Box<[(T, T)]>,
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
        RangeSet {
            ranges: ranges.into_iter().map(RangeInclusive::into_inner).collect(),
        }
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
            .binary_search_by(|(start, end)| {
                if start.borrow() > value {
                    Ordering::Greater
                } else if end.borrow() >= value {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            })
            .is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::RangeSet;

    #[test]
    fn merges_overlapping_ranges_and_preserves_gaps() {
        let ranges = [8..=10, 2..=4, 3..=6, 2..=3, 9..=9];
        let set: RangeSet<_> = ranges.clone().into_iter().collect();

        assert_eq!(&*set.ranges, &[(2, 6), (8, 10)]);
        for value in 0..=12 {
            assert_eq!(
                set.contains(&value),
                ranges.iter().any(|range| range.contains(&value)),
                "membership of {value}"
            );
        }
    }

    #[test]
    fn includes_singletons_and_integer_limits() {
        let set: RangeSet<_> = [i64::MIN..=i64::MIN, 0..=0, i64::MAX..=i64::MAX]
            .into_iter()
            .collect();

        for value in [i64::MIN, 0, i64::MAX] {
            assert!(set.contains(&value));
        }
        for value in [i64::MIN + 1, -1, 1, i64::MAX - 1] {
            assert!(!set.contains(&value));
        }
        let empty: RangeSet<i64> = [].into_iter().collect();
        assert!(!empty.contains(&0));
    }
}
