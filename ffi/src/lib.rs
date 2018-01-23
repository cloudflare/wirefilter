extern crate libc;
extern crate wirefilter;

mod arrays;

use wirefilter::lex::LexErrorKind;
use libc::size_t;
use std::str::Utf8Error;
use wirefilter::types::Type;
use wirefilter::Context;
use std::string::ToString;
use std::error::Error as StdError;
use std::fmt::Display;
use arrays::{Array, Str};

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Field<'a, V> {
    key: Str<'a>,
    value: V,
}

pub type Fields<'a, V> = Array<'a, Field<'a, V>>;

#[repr(C)]
pub struct Error {
    msg: Str<'static>,
    span_start: size_t,
    span_len: size_t,
}

impl Error {
    pub fn new<E: Display>(err: E, span_start: size_t, span_len: size_t) -> Self {
        Error {
            msg: Str::from(err.to_string()),
            span_start,
            span_len,
        }
    }

    pub fn new_lex(input: &str, (err, span): (LexErrorKind, &str)) -> Self {
        Error::new(
            err,
            span.as_ptr() as usize - input.as_ptr() as usize,
            span.len(),
        )
    }
}

impl Default for Error {
    fn default() -> Self {
        Error::new("", 0, 0)
    }
}

impl<E: StdError> From<E> for Error {
    fn from(err: E) -> Self {
        Error::new(err, 0, 0)
    }
}

fn create_parsing_context(fields: Fields<Type>) -> Result<Context<&str, Type>, Utf8Error> {
    fields
        .as_slice()
        .iter()
        .map(|field| Ok((field.key.as_str()?, field.value)))
        .collect()
}

pub type ParsingContext<'a> = *mut Context<&'a str, Type>;

pub unsafe extern "C" fn wirefilter_create_parsing_context(fields: Fields<Type>) -> ParsingContext {
    Box::into_raw(Box::new(
        create_parsing_context(fields).unwrap(),
    ))
}

pub unsafe extern "C" fn wirefilter_free_parsing_context(context: ParsingContext) {
    Box::from_raw(context);
}

pub type ExecContext<'a> = *mut Context<&'a str, LhsValue>;

pub unsafe extern "C" fn wirefilter_create_exec_context(values: Fields<LhsValue>) -> ExecContext {
    Box::into_raw(Box::new(
        create_parsing_context(fields).unwrap(),
    ))
}

pub unsafe extern fn wirefilter_free_exec_context(context: ExecContext) {
    Box::from_raw(context);
}

fn validate(fields: Fields<Type>, filter: Str) -> Result<(), Error> {
    let filter = filter.as_str()?;

    create_parsing_context(fields)?
        .parse(filter)
        .map_err(|err| Error::new_lex(filter, err))?;

    Ok(())
}

pub unsafe extern "C" fn wirefilter_validate(fields: Fields<Type>, filter: Str) -> Error {
    match validate(fields, filter) {
        Ok(()) => Error::default(),
        Err(err) => err,
    }
}

pub unsafe extern "C" fn wirefilter_free_error(error: Error) {
    error.msg.free();
}
