extern crate libc;
extern crate wirefilter;

use libc::size_t;
use std::{slice, str};
use wirefilter::types::Type;
use wirefilter::Context;
use std::string::ToString;
use std::ptr::null_mut;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Array<'a, T: 'a> {
    data: &'a T,
    length: size_t,
}

impl<'a, T: 'a> Array<'a, T> {
    pub unsafe fn as_slice(self) -> &'a [T] {
        slice::from_raw_parts(self.data, self.length)
    }
}

pub type Str<'a> = Array<'a, u8>;

impl<'a> Str<'a> {
    pub unsafe fn as_str(self) -> Result<&'a str, String> {
        str::from_utf8(self.as_slice()).map_err(|err| err.to_string())
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

pub unsafe extern "C" fn wirefilter_validate<'a>(
    fields: Fields<'a, Type>,
    filter: Str<'a>,
) -> Error {
    let res = fields
        .as_slice()
        .iter()
        .map(|field| Ok((field.key.as_str()?, field.value)))
        .collect::<Result<Context<_, _>, _>>()
        .and_then(|context| {
            match context.parse(filter.as_str()?) {
                Ok(_) => Ok(()),
                Err((err, _)) => Err(err.to_string())
            }
        });

    match res {
        Ok(_) => Error {
            msg_data: null_mut(),
            msg_len: 0,
            span_start: 0,
            span_len: 0,
        },
        Err(err) => {
            let msg = Box::into_raw(err.to_string().into_boxed_str().into_boxed_bytes());
            Error {
                msg_data: (*msg).as_mut_ptr(),
                msg_len: (*msg).len(),
                span_start: 0,
                span_len: 0
            }
        }
    }
}

pub unsafe extern "C" fn wirefilter_free_error<'a>(error: Error) {
    Box::from_raw(slice::from_raw_parts_mut(
        error.msg_data,
        error.msg_len,
    ));
}
