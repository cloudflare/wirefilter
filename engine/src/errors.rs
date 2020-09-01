use super::filter::SchemeMismatchError;
#[derive(Debug)]
pub enum Error {
    SchemaMismatch(SchemeMismatchError)
}