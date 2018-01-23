extern crate libc;
extern crate wirefilter;

use wirefilter::lex::LexErrorKind;
use libc::size_t;
use std::{slice, str};
use wirefilter::types::Type;
use wirefilter::Context;
use std::string::ToString;
use std::error::Error as StdError;
use std::fmt::Display;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Array<'a, T: 'a> {
    data: &'a T,
    length: size_t,
}

impl<'a, T: 'a> Array<'a, T> {
    pub fn as_slice(self) -> &'a [T] {
        unsafe { slice::from_raw_parts(self.data, self.length) }
    }
}

pub type Str<'a> = Array<'a, u8>;

impl<'a> Str<'a> {
    pub fn as_str(self) -> Result<&'a str, str::Utf8Error> {
        str::from_utf8(self.as_slice())
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Field<'a, V> {
    key: Str<'a>,
    value: V,
}

pub type Fields<'a, V> = Array<'a, Field<'a, V>>;

#[repr(C)]
pub struct Error {
    msg_data: *mut u8,
    msg_len: size_t,
    span_start: size_t,
    span_len: size_t,
}

impl Error {
    pub fn new<E: Display>(err: E, span_start: size_t, span_len: size_t) -> Self {
        let msg = Box::into_raw(err.to_string().into_boxed_str().into_boxed_bytes());
        Error {
            msg_data: unsafe { (*msg).as_mut_ptr() },
            msg_len: unsafe { (*msg).len() },
            span_start,
            span_len,
        }
    }

    pub fn new_lex(input: &str, (err, span): (LexErrorKind, &str)) -> Self {
        Error::new(
            err,
            span.as_ptr() as size_t - input.as_ptr() as size_t,
            span.len() as size_t,
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

fn create_parsing_context(fields: Fields<Type>) -> Result<Context<&str, Type>, str::Utf8Error> {
    fields
        .as_slice()
        .iter()
        .map(|field| Ok((field.key.as_str()?, field.value)))
        .collect()
}

pub type ParsingContext = *mut Context<&str, Type>;

pub unsafe extern "C" fn wirefilter_create_parsing_context(
    fields: Fields<Type>,
) -> ParsingContext {
    Box::into_raw(Box::new(
        create_parsing_context(fields).expect("Could not create a context"),
    ))
}

pub unsafe extern "C" fn wirefilter_free_parsing_context(context: ParsingContext) {
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

pub unsafe extern "C" fn wirefilter_free_error<'a>(error: Error) {
    Box::from_raw(slice::from_raw_parts_mut(error.msg_data, error.msg_len));
}
