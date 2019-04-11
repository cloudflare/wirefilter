use crate::{
    lex::{Lex, LexResult},
    strict_partial_ord::StrictPartialOrd,
    types::{GetType, Map, Type},
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

impl<'a> PartialEq<UninhabitedMap> for Map<'a> {
    fn eq(&self, other: &UninhabitedMap) -> bool {
        match *other {}
    }
}

impl<'a> PartialOrd<UninhabitedMap> for Map<'a> {
    fn partial_cmp(&self, other: &UninhabitedMap) -> Option<Ordering> {
        match *other {}
    }
}

impl<'a> StrictPartialOrd<UninhabitedMap> for Map<'a> {}

impl<'i> Lex<'i> for UninhabitedMap {
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
