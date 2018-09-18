use fnv::FnvBuildHasher;
use indexmap::IndexSet;
use std::{
    borrow::Borrow,
    fmt::{self, Debug, Formatter},
    hash::Hash,
    iter::FromIterator,
};

// VecSet encapsulates a list of items, providing set-like interface.
//
// The actual internal representation might change in future, but what's
// important is that, unlike `Vec::contains`, it allows to search not only for
// actual item type, but also for any of it `Borrow` implementations, just like
// `HashSet::contains` and `BTreeSet::contains`.
#[derive(Clone, Serialize)]
#[serde(transparent)]
pub struct VecSet<T: Hash + Eq> {
    items: IndexSet<T, FnvBuildHasher>,
}

impl<T: Hash + Eq> PartialEq for VecSet<T> {
    fn eq(&self, other: &Self) -> bool {
        // compare sets as ordered item lists
        self.items.iter().eq(&other.items)
    }
}

impl<T: Hash + Eq> Eq for VecSet<T> {}

impl<T: Hash + Eq + Debug> Debug for VecSet<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.items.fmt(f)
    }
}

impl<T: Hash + Eq> From<Vec<T>> for VecSet<T> {
    fn from(items: Vec<T>) -> Self {
        Self::from_iter(items)
    }
}

impl<T: Hash + Eq> FromIterator<T> for VecSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(items: I) -> Self {
        VecSet {
            items: IndexSet::from_iter(items),
        }
    }
}

impl<T: Hash + Eq> VecSet<T> {
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.items.contains(value)
    }
}
