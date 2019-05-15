use crate::{
    lex::{Lex, LexResult},
    strict_partial_ord::StrictPartialOrd,
    types::{Array, GetType, Type},
};
use serde::Serialize;
use std::{borrow::Borrow, cmp::Ordering};

/// [Uninhabited / empty type](https://doc.rust-lang.org/nomicon/exotic-sizes.html#empty-types)
/// for `array` with traits we need for RHS values.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
pub enum UninhabitedArray {}

impl<'a> Borrow<Array<'a>> for UninhabitedArray {
    fn borrow(&self) -> &Array<'a> {
        match *self {}
    }
}

impl<'a> PartialEq<UninhabitedArray> for Array<'a> {
    fn eq(&self, other: &UninhabitedArray) -> bool {
        match *other {}
    }
}

impl<'a> PartialOrd<UninhabitedArray> for Array<'a> {
    fn partial_cmp(&self, other: &UninhabitedArray) -> Option<Ordering> {
        match *other {}
    }
}

impl<'a> StrictPartialOrd<UninhabitedArray> for Array<'a> {}

impl<'i> Lex<'i> for UninhabitedArray {
    fn lex(_input: &str) -> LexResult<'_, Self> {
        unreachable!()
    }
}

impl GetType for UninhabitedArray {
    fn get_type(&self) -> Type {
        unreachable!()
    }
}

impl GetType for Vec<UninhabitedArray> {
    fn get_type(&self) -> Type {
        unreachable!()
    }
}
