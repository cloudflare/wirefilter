extern crate libc;
extern crate wirefilter;

mod arrays;

use arrays::{Array, Str};
use libc::size_t;
use std::error::Error as StdError;
use std::fmt::Display;
use std::str::Utf8Error;
use std::string::ToString;
use wirefilter::Context;
use wirefilter::lex::LexErrorKind;
use wirefilter::types::{LhsValue, Type};

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

fn create_context<T: Clone>(fields: Fields<T>) -> Result<Context<&str, T>, Utf8Error> {
    fields
        .as_slice()
        .iter()
        .map(|field| Ok((field.key.as_str()?, field.value.clone())))
        .collect()
}

pub type ParsingContext<'a> = *mut Context<&'a str, Type>;

#[no_mangle]
pub unsafe extern "C" fn wirefilter_create_parsing_context(fields: Fields<Type>) -> ParsingContext {
    Box::into_raw(Box::new(create_context(fields).unwrap()))
}

#[no_mangle]
pub unsafe extern "C" fn wirefilter_free_parsing_context(context: ParsingContext) {
    Box::from_raw(context);
}

pub type ExecContext<'a> = *mut Context<&'a str, LhsValue<'a>>;

#[no_mangle]
pub unsafe extern "C" fn wirefilter_create_exec_context<'a>(values: Fields<'a, LhsValue<'a>>) -> ExecContext<'a> {
    Box::into_raw(Box::new(create_context(values).unwrap()))
}

#[no_mangle]
pub unsafe extern "C" fn wirefilter_free_exec_context(context: ExecContext) {
    Box::from_raw(context);
}

fn validate(fields: Fields<Type>, filter: Str) -> Result<(), Error> {
    let filter = filter.as_str()?;

    create_context(fields)?
        .parse(filter)
        .map_err(|err| Error::new_lex(filter, err))?;

    Ok(())
}

#[no_mangle]
pub unsafe extern "C" fn wirefilter_validate(fields: Fields<Type>, filter: Str) -> Error {
    match validate(fields, filter) {
        Ok(()) => Error::default(),
        Err(err) => err,
    }
}

#[no_mangle]
pub unsafe extern "C" fn wirefilter_free_error(error: Error) {
    error.msg.free();
}
