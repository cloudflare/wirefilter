use crate::{
    lex::{Lex, LexResult},
    strict_partial_ord::StrictPartialOrd,
};
use serde::Serialize;
use std::{borrow::Borrow, cmp::Ordering};

/// [Uninhabited / empty type](https://doc.rust-lang.org/nomicon/exotic-sizes.html#empty-types)
/// for `bool` with traits we need for RHS values.
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

impl<'i> Lex<'i> for UninhabitedBool {
    fn lex(_input: &str) -> LexResult<'_, Self> {
        unreachable!()
    }
}
