use crate::{
    lex::{Lex, LexResult},
    lhs_types::Map,
    strict_partial_ord::StrictPartialOrd,
    types::{GetType, Type},
};
use serde::Serialize;
use std::{borrow::Borrow, cmp::Ordering};

/// [Uninhabited / empty type](https://doc.rust-lang.org/nomicon/exotic-sizes.html#empty-types)
/// for `map` with traits we need for RHS values.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
pub enum UninhabitedMap {}

impl<'a> Borrow<Map<'a>> for UninhabitedMap {
    fn borrow(&self) -> &Map<'a> {
        match *self {}
    }
}

impl PartialEq<UninhabitedMap> for Map<'_> {
    fn eq(&self, other: &UninhabitedMap) -> bool {
        match *other {}
    }
}

impl PartialOrd<UninhabitedMap> for Map<'_> {
    fn partial_cmp(&self, other: &UninhabitedMap) -> Option<Ordering> {
        match *other {}
    }
}

impl StrictPartialOrd<UninhabitedMap> for Map<'_> {}

impl Lex<'_> for UninhabitedMap {
    fn lex(_input: &str) -> LexResult<'_, Self> {
        unreachable!()
    }
}

impl GetType for UninhabitedMap {
    fn get_type(&self) -> Type {
        unreachable!()
    }
}

impl GetType for Vec<UninhabitedMap> {
    fn get_type(&self) -> Type {
        unreachable!()
    }
}
