use super::filter::SchemeMismatchError;
use crate::TypeMismatchError;

#[derive(Debug)]
pub enum Error {
    SchemaMismatch(SchemeMismatchError),
    TypeMismatchError(TypeMismatchError)
}