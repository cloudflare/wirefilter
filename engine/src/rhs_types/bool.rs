use crate::lex::{Lex, LexResult};
use crate::strict_partial_ord::StrictPartialOrd;
use serde::Serialize;
use std::borrow::Borrow;
use std::cmp::Ordering;

/// [Uninhabited / empty type](https://doc.rust-lang.org/nomicon/exotic-sizes.html#empty-types)
/// for `bool` with traits we need for literal values.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
pub enum UninhabitedBool {}

impl Borrow<bool> for UninhabitedBool {
    fn borrow(&self) -> &bool {
        match *self {}
    }
}

impl PartialEq<UninhabitedBool> for bool {
    fn eq(&self, other: &UninhabitedBool) -> bool {
        match *other {}
    }
}

impl PartialOrd<UninhabitedBool> for bool {
    fn partial_cmp(&self, other: &UninhabitedBool) -> Option<Ordering> {
        match *other {}
    }
}

impl StrictPartialOrd<UninhabitedBool> for bool {}

impl Lex<'_> for UninhabitedBool {
    fn lex(_input: &str) -> LexResult<'_, Self> {
        unreachable!()
    }
}
