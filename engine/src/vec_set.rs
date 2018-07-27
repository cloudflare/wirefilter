use std::{
    borrow::Borrow,
    fmt::{self, Debug, Formatter},
    iter::FromIterator,
};

// VecSet encapsulates a list of items, providing set-like interface.
//
// The actual internal representation might change in future, but what's
// important is that, unlike `Vec::contains`, it allows to search not only for
// actual item type, but also for any of it `Borrow` implementations, just like
// `HashSet::contains` and `BTreeSet::contains`.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct VecSet<T> {
    items: Vec<T>,
}

impl<T: Eq + Debug> Debug for VecSet<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_set().entries(&self.items).finish()
    }
}

impl<T> From<Vec<T>> for VecSet<T> {
    fn from(items: Vec<T>) -> Self {
        VecSet { items }
    }
}

impl<T> FromIterator<T> for VecSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(items: I) -> Self {
        Vec::from_iter(items).into()
    }
}

impl<T> VecSet<T> {
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.items.iter().any(|item| item.borrow() == value)
    }
}
