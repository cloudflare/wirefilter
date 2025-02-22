#![allow(clippy::not_unsafe_ptr_arg_deref)]
#![warn(rust_2018_idioms)]

mod cstring;
pub mod panic;

use crate::cstring::CString;
use fnv::FnvHasher;
use libc::c_char;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use serde::de::DeserializeSeed;
use std::cell::RefCell;
use std::ops::{Deref, DerefMut};
use std::{
    convert::TryFrom,
    hash::Hasher,
    io::{self, Write},
    net::IpAddr,
};
use wirefilter::{AlwaysList, LhsValue, NeverList, Type, catch_panic};

const VERSION: &str = env!("CARGO_PKG_VERSION");

thread_local! {
    /// Thread local error string.
    pub static LAST_ERROR: RefCell<CString> = const { RefCell::new(CString::new()) };
}

/// Helper macro to write an error.
#[macro_export]
macro_rules! write_last_error {
    ($($arg:tt)*) => {
        $crate::LAST_ERROR.with_borrow_mut(|last_error| {
            last_error.clear();
            write!(last_error, $($arg)*).unwrap();
        })
    };
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum CPrimitiveType {
    Ip = 1u8,
    Bytes = 2u8,
    Int = 3u8,
    Bool = 4u8,
}

enum Layer {
    Array,
    Map,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct CType {
    pub layers: u32,
    pub len: u8,
    pub primitive: u8,
}

impl CType {
    const fn push(mut self, layer: Layer) -> CType {
        let layer = match layer {
            Layer::Array => 0,
            Layer::Map => 1,
        };
        self.layers = (self.layers << 1) | layer;
        self.len += 1;
        self
    }

    const fn pop(mut self) -> (Self, Option<Layer>) {
        if self.len > 0 {
            // Maybe use (trailing/leading)_(ones/zeros) instead
            let layer = (self.layers & 1) == 0;
            self.layers >>= 1;
            self.len -= 1;
            if layer {
                (self, Some(Layer::Array))
            } else {
                (self, Some(Layer::Map))
            }
        } else {
            (self, None)
        }
    }
}

impl From<CType> for Type {
    fn from(cty: CType) -> Self {
        let (ty, layer) = cty.pop();
        match layer {
            Some(Layer::Array) => Type::Array(Type::from(ty).into()),
            Some(Layer::Map) => Type::Map(Type::from(ty).into()),
            None => match CPrimitiveType::try_from(cty.primitive).unwrap() {
                CPrimitiveType::Bool => Type::Bool,
                CPrimitiveType::Bytes => Type::Bytes,
                CPrimitiveType::Int => Type::Int,
                CPrimitiveType::Ip => Type::Ip,
            },
        }
    }
}

impl From<Type> for CType {
    fn from(ty: Type) -> Self {
        match ty {
            Type::Ip => CType {
                len: 0,
                layers: 0,
                primitive: CPrimitiveType::Ip.into(),
            },
            Type::Bytes => CType {
                len: 0,
                layers: 0,
                primitive: CPrimitiveType::Bytes.into(),
            },
            Type::Int => CType {
                len: 0,
                layers: 0,
                primitive: CPrimitiveType::Int.into(),
            },
            Type::Bool => CType {
                len: 0,
                layers: 0,
                primitive: CPrimitiveType::Bool.into(),
            },
            Type::Array(arr) => Self::from(Type::from(arr)).push(Layer::Array),
            Type::Map(map) => Self::from(Type::from(map)).push(Layer::Map),
        }
    }
}

macro_rules! wrap_type {
    ($rust:ident $(<$rust_lt:lifetime>)? => $ffi:ident $(<$ffi_lt:lifetime>)?) => {
        impl$(<$ffi_lt>)? Deref for $ffi$(<$ffi_lt>)? {
            type Target = wirefilter::$rust$(<$rust_lt>)?;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl$(<$ffi_lt>)? DerefMut for $ffi$(<$ffi_lt>)? {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }

        impl$(<$ffi_lt>)? AsRef<wirefilter::$rust$(<$rust_lt>)?> for $ffi$(<$ffi_lt>)? {
            fn as_ref(&self) -> &wirefilter::$rust$(<$rust_lt>)? {
                &self.0
            }
        }

        impl$(<$ffi_lt>)? From<wirefilter::$rust$(<$rust_lt>)?> for $ffi$(<$ffi_lt>)? {
            fn from(value: wirefilter::$rust$(<$rust_lt>)?) -> Self {
                Self(value)
            }
        }

        impl$(<$rust_lt>)? From<$ffi$(<$ffi_lt>)?> for wirefilter::$rust$(<$rust_lt>)? {
            fn from(value: $ffi$(<$ffi_lt>)?) -> Self {
                value.0
            }
        }
    };

    ($rust:ident $(<$rust_lt:lifetime>)?) => {
        wrap_type!($rust $(<$rust_lt>)? => $rust $(<$rust_lt>)?);
    };
}

/* Wrapper types needed by cbindgen to forward declare opaque structs */

#[derive(Debug, Default)]
#[repr(Rust)]
pub struct SchemeBuilder(wirefilter::SchemeBuilder);

wrap_type!(SchemeBuilder);

#[derive(Debug, PartialEq)]
#[repr(Rust)]
pub struct Scheme(wirefilter::Scheme);

wrap_type!(Scheme);

#[derive(Debug, PartialEq)]
#[repr(Rust)]
pub struct ExecutionContext<'s>(wirefilter::ExecutionContext<'s>);

wrap_type!(ExecutionContext<'s>);

#[derive(Debug, PartialEq)]
#[repr(Rust)]
pub struct Array<'s>(wirefilter::Array<'s>);

wrap_type!(Array<'s>);

impl<'s> From<Array<'s>> for LhsValue<'s> {
    fn from(array: Array<'s>) -> Self {
        Self::Array(array.into())
    }
}

#[derive(Debug, PartialEq)]
#[repr(Rust)]
pub struct Map<'s>(wirefilter::Map<'s>);

wrap_type!(Map<'s>);

impl<'s> From<Map<'s>> for LhsValue<'s> {
    fn from(map: Map<'s>) -> Self {
        Self::Map(map.into())
    }
}

#[derive(Debug, PartialEq)]
#[repr(Rust)]
pub struct FilterAst(wirefilter::FilterAst);

wrap_type!(FilterAst);

#[derive(Debug)]
#[repr(Rust)]
pub struct Filter(wirefilter::Filter<()>);

wrap_type!(Filter);

/// Represents the status of an operation.
#[derive(Debug, PartialEq)]
#[repr(C)]
pub enum Status {
    /// Operation succeeded.
    Success = 0,
    /// Operation encountered an error.
    ///
    /// Use [`wirefilter_get_last_error`] to retrieve the error message.
    Error,
    /// Operation has triggered a panic.
    ///
    /// Use [`wirefilter_get_last_error`] to retrieve the panic information.
    Panic,
}

/// Returns a pointer to the last error string if there was one or NULL.
#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_get_last_error() -> *const c_char {
    crate::LAST_ERROR.with_borrow(|last_error| last_error.as_c_str())
}

/// Clears the last error string if there was one.
///
/// Further calls to `wirefilter_get_last_error` will return NULL,
/// until another error is written to it.
#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_clear_last_error() {
    crate::LAST_ERROR.with_borrow_mut(|last_error| {
        last_error.clear();
    });
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_create_scheme_builder() -> Box<SchemeBuilder> {
    Box::default()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_free_scheme_builder(scheme: Box<SchemeBuilder>) {
    drop(scheme);
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_create_primitive_type(ty: CPrimitiveType) -> CType {
    CType {
        layers: 0,
        len: 0,
        primitive: ty.into(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_create_map_type(ty: CType) -> CType {
    ty.push(Layer::Map)
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_create_array_type(ty: CType) -> CType {
    ty.push(Layer::Array)
}

#[inline(always)]
fn cast_c_char(ptr: *const c_char) -> *const u8 {
    ptr.cast()
}

macro_rules! to_str {
    ($ptr:ident, $len:ident, $ret:expr) => {{
        assert!(!$ptr.is_null());
        match std::str::from_utf8(unsafe { std::slice::from_raw_parts(cast_c_char($ptr), $len) }) {
            Ok(s) => s,
            Err(err) => {
                write_last_error!("{}", err);
                return $ret;
            }
        }
    }};
    ($ptr:ident, $len:ident) => {
        to_str!($ptr, $len, false)
    };
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_type_field_to_scheme(
    builder: &mut SchemeBuilder,
    name_ptr: *const c_char,
    name_len: usize,
    ty: CType,
) -> bool {
    let name = to_str!(name_ptr, name_len);
    builder.add_field(name, ty.into()).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_always_list_to_scheme(
    builder: &mut SchemeBuilder,
    ty: CType,
) -> bool {
    builder.add_list(ty.into(), AlwaysList {}).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_never_list_to_scheme(
    builder: &mut SchemeBuilder,
    ty: CType,
) -> bool {
    builder.add_list(ty.into(), NeverList {}).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_build_scheme(builder: Box<SchemeBuilder>) -> Box<Scheme> {
    Box::new(Scheme(builder.0.build()))
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_free_scheme(scheme: Box<Scheme>) {
    drop(scheme);
}

#[derive(Debug, PartialEq)]
#[repr(C)]
pub struct RustAllocatedString {
    pub ptr: *mut c_char,
    pub len: usize,
}

impl Default for RustAllocatedString {
    fn default() -> Self {
        Self {
            ptr: std::ptr::null_mut(),
            len: 0,
        }
    }
}

impl From<String> for RustAllocatedString {
    fn from(s: String) -> Self {
        let bytes = s.into_boxed_str().into_boxed_bytes();
        let len = bytes.len();
        let ptr = Box::into_raw(bytes).cast::<c_char>();
        Self { ptr, len }
    }
}

impl Drop for RustAllocatedString {
    fn drop(&mut self) {
        if self.ptr.is_null() {
            assert_eq!(self.len, 0);
        } else {
            let slice = unsafe { std::slice::from_raw_parts_mut(self.ptr.cast::<u8>(), self.len) };
            drop(unsafe { Box::from_raw(slice as *mut _) });
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_free_string(s: RustAllocatedString) {
    drop(s);
}

#[derive(Debug, PartialEq)]
#[repr(C)]
pub struct ParsingResult {
    pub status: Status,
    pub ast: Option<Box<FilterAst>>,
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_parse_filter(
    scheme: &Scheme,
    input_ptr: *const c_char,
    input_len: usize,
) -> ParsingResult {
    let input = to_str!(
        input_ptr,
        input_len,
        ParsingResult {
            status: Status::Error,
            ast: None,
        }
    );
    match catch_panic(std::panic::AssertUnwindSafe(|| scheme.parse(input))) {
        Ok(Ok(ast)) => ParsingResult {
            status: Status::Success,
            ast: Some(Box::new(FilterAst(ast))),
        },
        Ok(Err(err)) => {
            write_last_error!("{}", err);
            ParsingResult {
                status: Status::Error,
                ast: None,
            }
        }
        Err(err) => {
            write_last_error!("{}", err);
            ParsingResult {
                status: Status::Panic,
                ast: None,
            }
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_free_parsed_filter(ast: Box<FilterAst>) {
    drop(ast);
}

/// Wrapper for Hasher that allows using Write API (e.g. with serializer).
#[derive(Default)]
struct HasherWrite<H: Hasher>(H);

impl<H: Hasher> Write for HasherWrite<H> {
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.0.write(buf);
        Ok(())
    }

    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.write_all(buf)?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[derive(Debug, PartialEq)]
#[repr(C)]
pub struct HashingResult {
    pub status: Status,
    pub hash: u64,
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_get_filter_hash(filter_ast: &FilterAst) -> HashingResult {
    let mut hasher = FnvHasher::default();
    // Serialize JSON to our Write-compatible wrapper around FnvHasher,
    // effectively calculating a hash for our filter in a streaming fashion
    // that is as stable as the JSON representation itself
    // (instead of relying on #[derive(Hash)] which would be tied to impl details).
    match serde_json::to_writer(HasherWrite(&mut hasher), filter_ast.deref()) {
        Ok(()) => HashingResult {
            status: Status::Success,
            hash: hasher.finish(),
        },
        Err(err) => {
            write_last_error!("{}", err);
            HashingResult {
                status: Status::Error,
                hash: 0,
            }
        }
    }
}

#[derive(Debug, PartialEq)]
#[repr(C)]
pub struct SerializingResult {
    pub status: Status,
    pub json: RustAllocatedString,
}

impl From<Result<String, serde_json::Error>> for SerializingResult {
    fn from(result: Result<String, serde_json::Error>) -> Self {
        match result {
            Ok(ok) => SerializingResult {
                status: Status::Success,
                json: ok.into(),
            },
            Err(err) => {
                write_last_error!("{}", err);
                SerializingResult {
                    status: Status::Error,
                    json: RustAllocatedString::default(),
                }
            }
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_serialize_filter_to_json(filter_ast: &FilterAst) -> SerializingResult {
    serde_json::to_string(filter_ast.deref()).into()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_serialize_scheme_to_json(scheme: &Scheme) -> SerializingResult {
    serde_json::to_string(scheme.deref()).into()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_serialize_type_to_json(ty: CType) -> SerializingResult {
    serde_json::to_string(&Type::from(ty)).into()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_create_execution_context<'e, 's: 'e>(
    scheme: &'s Scheme,
) -> Box<ExecutionContext<'e>> {
    Box::new(ExecutionContext(wirefilter::ExecutionContext::new(scheme)))
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_serialize_execution_context_to_json(
    exec_context: &mut ExecutionContext<'_>,
) -> SerializingResult {
    serde_json::to_string(exec_context.as_ref()).into()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_deserialize_json_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    json_ptr: *const u8,
    json_len: usize,
) -> bool {
    assert!(!json_ptr.is_null());
    let json = unsafe { std::slice::from_raw_parts(json_ptr, json_len) };
    let mut deserializer = serde_json::Deserializer::from_slice(json);
    match exec_context.deserialize(&mut deserializer) {
        Ok(_) => true,
        Err(err) => {
            write_last_error!("{}", err);
            false
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_free_execution_context(exec_context: Box<ExecutionContext<'_>>) {
    drop(exec_context);
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_int_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name_ptr: *const c_char,
    name_len: usize,
    value: i64,
) -> bool {
    let name = to_str!(name_ptr, name_len);
    exec_context.set_field_value_from_name(name, value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_bytes_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name_ptr: *const c_char,
    name_len: usize,
    value_ptr: *const u8,
    value_len: usize,
) -> bool {
    let name = to_str!(name_ptr, name_len);
    assert!(!value_ptr.is_null());
    let value = unsafe { std::slice::from_raw_parts(value_ptr, value_len) };
    exec_context.set_field_value_from_name(name, value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_ipv6_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name_ptr: *const c_char,
    name_len: usize,
    value: &[u8; 16],
) -> bool {
    let name = to_str!(name_ptr, name_len);
    exec_context
        .set_field_value_from_name(name, IpAddr::from(*value))
        .is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_ipv4_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name_ptr: *const c_char,
    name_len: usize,
    value: &[u8; 4],
) -> bool {
    let name = to_str!(name_ptr, name_len);
    exec_context
        .set_field_value_from_name(name, IpAddr::from(*value))
        .is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_bool_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name_ptr: *const c_char,
    name_len: usize,
    value: bool,
) -> bool {
    let name = to_str!(name_ptr, name_len);
    exec_context.set_field_value_from_name(name, value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_map_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name_ptr: *const c_char,
    name_len: usize,
    value: Box<Map<'a>>,
) -> bool {
    let name = to_str!(name_ptr, name_len);
    exec_context.set_field_value_from_name(name, *value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_array_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name_ptr: *const c_char,
    name_len: usize,
    value: Box<Array<'a>>,
) -> bool {
    let name = to_str!(name_ptr, name_len);
    exec_context.set_field_value_from_name(name, *value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_create_map<'a>(ty: CType) -> Box<Map<'a>> {
    Box::new(Map(wirefilter::Map::new(Type::from(ty))))
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_int_value_to_map(
    map: &mut Map<'_>,
    name_ptr: *const u8,
    name_len: usize,
    value: i64,
) -> bool {
    assert!(!name_ptr.is_null());
    let name = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
    map.insert(name, value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_bytes_value_to_map(
    map: &mut Map<'_>,
    name_ptr: *const u8,
    name_len: usize,
    value_ptr: *const u8,
    value_len: usize,
) -> bool {
    assert!(!name_ptr.is_null());
    let name = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
    assert!(!value_ptr.is_null());
    let value = unsafe { std::slice::from_raw_parts(value_ptr, value_len) };
    map.insert(name, value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_ipv6_value_to_map(
    map: &mut Map<'_>,
    name_ptr: *const u8,
    name_len: usize,
    value: &[u8; 16],
) -> bool {
    assert!(!name_ptr.is_null());
    let name = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
    let value = IpAddr::from(*value);
    map.insert(name, value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_ipv4_value_to_map(
    map: &mut Map<'_>,
    name_ptr: *const u8,
    name_len: usize,
    value: &[u8; 4],
) -> bool {
    assert!(!name_ptr.is_null());
    let name = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
    let value = IpAddr::from(*value);
    map.insert(name, value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_bool_value_to_map(
    map: &mut Map<'_>,
    name_ptr: *const u8,
    name_len: usize,
    value: bool,
) -> bool {
    assert!(!name_ptr.is_null());
    let name = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
    map.insert(name, value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_map_value_to_map<'a>(
    map: &mut Map<'a>,
    name_ptr: *const u8,
    name_len: usize,
    value: Box<Map<'a>>,
) -> bool {
    assert!(!name_ptr.is_null());
    let name = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
    map.insert(name, *value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_array_value_to_map<'a>(
    map: &mut Map<'a>,
    name_ptr: *const u8,
    name_len: usize,
    value: Box<Array<'a>>,
) -> bool {
    assert!(!name_ptr.is_null());
    let name = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
    map.insert(name, *value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_free_map(map: Box<Map<'_>>) {
    drop(map)
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_create_array<'a>(ty: CType) -> Box<Array<'a>> {
    Box::new(Array(wirefilter::Array::new(Type::from(ty))))
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_int_value_to_array(
    array: &mut Array<'_>,
    index: u32,
    value: i64,
) -> bool {
    array.insert(index.try_into().unwrap(), value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_bytes_value_to_array(
    array: &mut Array<'_>,
    index: u32,
    value_ptr: *const u8,
    value_len: usize,
) -> bool {
    assert!(!value_ptr.is_null());
    let value = unsafe { std::slice::from_raw_parts(value_ptr, value_len) };
    array.insert(index.try_into().unwrap(), value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_ipv6_value_to_array(
    array: &mut Array<'_>,
    index: u32,
    value: &[u8; 16],
) -> bool {
    let value = IpAddr::from(*value);
    array.insert(index.try_into().unwrap(), value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_ipv4_value_to_array(
    array: &mut Array<'_>,
    index: u32,
    value: &[u8; 4],
) -> bool {
    let value = IpAddr::from(*value);
    array.insert(index.try_into().unwrap(), value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_bool_value_to_array(
    array: &mut Array<'_>,
    index: u32,
    value: bool,
) -> bool {
    array.insert(index.try_into().unwrap(), value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_map_value_to_array<'a>(
    array: &mut Array<'a>,
    index: u32,
    value: Box<Map<'a>>,
) -> bool {
    array.insert(index.try_into().unwrap(), *value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_add_array_value_to_array<'a>(
    array: &mut Array<'a>,
    index: u32,
    value: Box<Array<'a>>,
) -> bool {
    array.insert(index.try_into().unwrap(), *value).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_free_array(array: Box<Array<'_>>) {
    drop(array)
}

#[derive(Debug)]
#[repr(C)]
pub struct CompilingResult {
    pub status: Status,
    pub filter: Option<Box<Filter>>,
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_compile_filter(filter_ast: Box<FilterAst>) -> CompilingResult {
    match catch_panic(std::panic::AssertUnwindSafe(|| {
        wirefilter::FilterAst::from(*filter_ast).compile()
    })) {
        Ok(filter) => CompilingResult {
            status: Status::Success,
            filter: Some(Box::new(Filter(filter))),
        },
        Err(err) => {
            write_last_error!("{}", err);
            CompilingResult {
                status: Status::Panic,
                filter: None,
            }
        }
    }
}

#[derive(Debug, PartialEq)]
#[repr(C)]
pub struct MatchingResult {
    pub status: Status,
    pub matched: bool,
}

impl MatchingResult {
    #[cfg(test)]
    const MISSED: Self = Self {
        status: Status::Success,
        matched: false,
    };
    #[cfg(test)]
    const MATCHED: Self = Self {
        status: Status::Success,
        matched: true,
    };
    const ERROR: Self = Self {
        status: Status::Error,
        matched: false,
    };
    const PANIC: Self = Self {
        status: Status::Panic,
        matched: false,
    };
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_match(
    filter: &Filter,
    exec_context: &ExecutionContext<'_>,
) -> MatchingResult {
    match catch_panic(std::panic::AssertUnwindSafe(|| {
        filter.execute(exec_context)
    })) {
        Ok(Ok(matched)) => MatchingResult {
            status: Status::Success,
            matched,
        },
        Ok(Err(err)) => {
            write_last_error!("{}", err);
            MatchingResult::ERROR
        }
        Err(err) => {
            write_last_error!("{}", err);
            MatchingResult::PANIC
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_free_compiled_filter(filter: Box<Filter>) {
    drop(filter);
}

#[derive(Debug, PartialEq)]
#[repr(C)]
pub struct UsingResult {
    pub status: Status,
    pub used: bool,
}

impl UsingResult {
    #[cfg(test)]
    const UNUSED: Self = Self {
        status: Status::Success,
        used: false,
    };
    #[cfg(test)]
    const USED: Self = Self {
        status: Status::Success,
        used: true,
    };
    const ERROR: Self = Self {
        status: Status::Error,
        used: false,
    };
    const PANIC: Self = Self {
        status: Status::Error,
        used: false,
    };
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_filter_uses(
    filter_ast: &FilterAst,
    field_name_ptr: *const c_char,
    field_name_len: usize,
) -> UsingResult {
    let field_name = to_str!(field_name_ptr, field_name_len, UsingResult::ERROR);
    match catch_panic(std::panic::AssertUnwindSafe(|| filter_ast.uses(field_name))) {
        Ok(Ok(used)) => UsingResult {
            status: Status::Success,
            used,
        },
        Ok(Err(err)) => {
            write_last_error!("{}", err);
            UsingResult::ERROR
        }
        Err(err) => {
            write_last_error!("{}", err);
            UsingResult::PANIC
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_filter_uses_list(
    filter_ast: &FilterAst,
    field_name_ptr: *const c_char,
    field_name_len: usize,
) -> UsingResult {
    let field_name = to_str!(
        field_name_ptr,
        field_name_len,
        UsingResult {
            status: Status::Error,
            used: false
        }
    );
    match catch_panic(std::panic::AssertUnwindSafe(|| {
        filter_ast.uses_list(field_name)
    })) {
        Ok(Ok(used)) => UsingResult {
            status: Status::Success,
            used,
        },
        Ok(Err(err)) => {
            write_last_error!("{}", err);
            UsingResult {
                status: Status::Error,
                used: false,
            }
        }
        Err(err) => {
            write_last_error!("{}", err);
            UsingResult {
                status: Status::Panic,
                used: false,
            }
        }
    }
}

#[derive(Debug, PartialEq)]
#[repr(C)]
pub struct StaticRustAllocatedString {
    pub ptr: *const c_char,
    pub len: usize,
}

impl From<&'static str> for StaticRustAllocatedString {
    fn from(s: &'static str) -> Self {
        let bytes = s.as_bytes();
        let ptr = bytes.as_ptr().cast::<c_char>();
        let len = bytes.len();
        Self { ptr, len }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_get_version() -> StaticRustAllocatedString {
    StaticRustAllocatedString::from(VERSION)
}

#[cfg(test)]
#[allow(clippy::bool_assert_comparison)]
mod ffi_test {
    use super::*;
    use regex_automata::meta::Regex;
    use std::ffi::CStr;

    impl RustAllocatedString {
        pub fn as_bytes(&self) -> Option<&[u8]> {
            if self.ptr.is_null() {
                None
            } else {
                Some(unsafe { std::slice::from_raw_parts(self.ptr.cast(), self.len) })
            }
        }
    }

    impl StaticRustAllocatedString {
        pub fn as_bytes(&self) -> &[u8] {
            assert!(!self.ptr.is_null());
            unsafe { std::slice::from_raw_parts(self.ptr.cast(), self.len) }
        }
    }

    fn create_scheme() -> Box<Scheme> {
        let mut builder = wirefilter_create_scheme_builder();

        macro_rules! add_field {
            ($builder:ident, $field:literal, $ty:expr) => {
                assert!(wirefilter_add_type_field_to_scheme(
                    &mut $builder,
                    $field.as_ptr().cast(),
                    $field.len(),
                    $ty.into(),
                ));
            };
        }

        add_field!(builder, "ip1", Type::Ip);
        add_field!(builder, "ip2", Type::Ip);

        add_field!(builder, "str1", Type::Bytes);
        add_field!(builder, "str2", Type::Bytes);

        add_field!(builder, "num1", Type::Int);
        add_field!(builder, "num2", Type::Int);

        add_field!(
            builder,
            "map1",
            wirefilter_create_map_type(Type::Int.into())
        );
        add_field!(
            builder,
            "map2",
            wirefilter_create_map_type(Type::Bytes.into())
        );

        wirefilter_add_always_list_to_scheme(&mut builder, Type::Int.into());

        wirefilter_build_scheme(builder)
    }

    fn create_execution_context<'e, 's: 'e>(scheme: &'s Scheme) -> Box<ExecutionContext<'e>> {
        let mut exec_context = wirefilter_create_execution_context(scheme);
        let invalid_key = &b"\xc3\x28"[..];

        assert!(std::str::from_utf8(invalid_key).is_err());

        let field = "ip1";
        assert!(wirefilter_add_ipv4_value_to_execution_context(
            &mut exec_context,
            field.as_ptr().cast(),
            field.len(),
            &[127, 0, 0, 1],
        ));

        let field = "ip2";
        assert!(wirefilter_add_ipv6_value_to_execution_context(
            &mut exec_context,
            field.as_ptr().cast(),
            field.len(),
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xFF\xFF\xC0\xA8\x00\x01",
        ));

        let field = "str1";
        let value = "Hey";
        assert!(wirefilter_add_bytes_value_to_execution_context(
            &mut exec_context,
            field.as_ptr().cast(),
            field.len(),
            value.as_ptr(),
            value.len(),
        ));

        let field = "str2";
        let value = "yo123";
        assert!(wirefilter_add_bytes_value_to_execution_context(
            &mut exec_context,
            field.as_ptr().cast(),
            field.len(),
            value.as_ptr(),
            value.len(),
        ));

        let field = "num1";
        assert!(wirefilter_add_int_value_to_execution_context(
            &mut exec_context,
            field.as_ptr().cast(),
            field.len(),
            42,
        ));

        let field = "num2";
        assert!(wirefilter_add_int_value_to_execution_context(
            &mut exec_context,
            field.as_ptr().cast(),
            field.len(),
            1337,
        ));

        let mut map1 = wirefilter_create_map(Type::Int.into());

        let key = b"key";
        wirefilter_add_int_value_to_map(&mut map1, key.as_ptr(), key.len(), 42);

        wirefilter_add_int_value_to_map(&mut map1, invalid_key.as_ptr(), invalid_key.len(), 42);

        let field = "map1";
        wirefilter_add_map_value_to_execution_context(
            &mut exec_context,
            field.as_ptr().cast(),
            field.len(),
            map1,
        );

        let mut map2 = wirefilter_create_map(Type::Bytes.into());

        let key = b"key";
        let value = "value";
        wirefilter_add_bytes_value_to_map(
            &mut map2,
            key.as_ptr(),
            key.len(),
            value.as_ptr(),
            value.len(),
        );

        let value = "value";
        wirefilter_add_bytes_value_to_map(
            &mut map2,
            invalid_key.as_ptr(),
            invalid_key.len(),
            value.as_ptr(),
            value.len(),
        );

        let field = "map2";
        wirefilter_add_map_value_to_execution_context(
            &mut exec_context,
            field.as_ptr().cast(),
            field.len(),
            map2,
        );

        exec_context
    }

    fn parse_filter(scheme: &Scheme, input: &'static str) -> ParsingResult {
        wirefilter_parse_filter(scheme, input.as_ptr().cast(), input.len())
    }

    fn match_filter(
        input: &'static str,
        scheme: &Scheme,
        exec_context: &ExecutionContext<'_>,
    ) -> MatchingResult {
        let filter = parse_filter(scheme, input).ast.unwrap();
        let filter = wirefilter_compile_filter(filter).filter.unwrap();

        let result = wirefilter_match(&filter, exec_context);

        wirefilter_free_compiled_filter(filter);

        result
    }

    #[test]
    fn parse_error() {
        use indoc::indoc;

        let src = indoc!(
            r#"
            (
                num1 == 42
                or
                num1 == "abc"
            )
            "#
        );

        let scheme = create_scheme();

        {
            assert_eq!(
                parse_filter(&scheme, src),
                ParsingResult {
                    status: Status::Error,
                    ast: None,
                }
            );

            let msg = unsafe { CStr::from_ptr(wirefilter_get_last_error()) };
            assert_eq!(
                msg.to_str(),
                Ok(indoc!(
                    r#"
                Filter parsing error (4:13):
                    num1 == "abc"
                            ^^^^^ expected digit
                "#
                ))
            );
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn filter_parsing() {
        let scheme = create_scheme();

        {
            let filter = parse_filter(&scheme, r#"num1 > 3 && str2 == "abc""#)
                .ast
                .unwrap();

            let result = wirefilter_serialize_filter_to_json(&filter);

            assert_eq!(result.status, Status::Success);

            assert_eq!(
                std::str::from_utf8(result.json.as_bytes().unwrap()).unwrap(),
                r#"{"op":"And","items":[{"lhs":"num1","op":"GreaterThan","rhs":3},{"lhs":"str2","op":"Equal","rhs":"abc"}]}"#
            );

            wirefilter_free_string(result.json);

            wirefilter_free_parsed_filter(filter);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn scheme_serialize() {
        let scheme = create_scheme();
        let result = wirefilter_serialize_scheme_to_json(&scheme);

        assert_eq!(result.status, Status::Success);

        let expected: String = serde_json::to_string(&**scheme).unwrap();
        assert_eq!(
            std::str::from_utf8(result.json.as_bytes().unwrap()).unwrap(),
            expected,
        );

        wirefilter_free_string(result.json);

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn filter_matching() {
        let scheme = create_scheme();

        {
            let exec_context = create_execution_context(&scheme);

            assert_eq!(
                match_filter(
                    r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+" && map2["key"] == "value""#,
                    &scheme,
                    &exec_context
                ),
                MatchingResult::MATCHED
            );

            assert_eq!(
                match_filter(
                    r#"ip2 == 0:0:0:0:0:ffff:c0a8:1 && (str1 == "Hey" || str2 == "ya") && (map1["key"] == 42 || map2["key2"] == "value")"#,
                    &scheme,
                    &exec_context
                ),
                MatchingResult::MATCHED
            );

            assert_eq!(
                match_filter(
                    "ip1 == 127.0.0.1 && ip2 == 0:0:0:0:0:ffff:c0a8:2",
                    &scheme,
                    &exec_context
                ),
                MatchingResult::MISSED
            );

            wirefilter_free_execution_context(exec_context);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn filter_hash() {
        let scheme = create_scheme();

        {
            let filter1 = parse_filter(
                &scheme,
                r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+" && map1["key"] == 42"#,
            ).ast
            .unwrap();

            let filter2 = parse_filter(
                &scheme,
                r#"num1 >     41 && num2 == 1337 &&    ip1 != 192.168.0.1 and str2 ~ "yo\d+"    && map1["key"] == 42   "#,
            ).ast
            .unwrap();

            let filter3 = parse_filter(&scheme, r#"num1 > 41 && num2 == 1337"#)
                .ast
                .unwrap();

            let result1 = wirefilter_get_filter_hash(&filter1);
            assert_eq!(result1.status, Status::Success);
            let result2 = wirefilter_get_filter_hash(&filter2);
            assert_eq!(result2.status, Status::Success);
            let result3 = wirefilter_get_filter_hash(&filter3);
            assert_eq!(result3.status, Status::Success);

            assert_eq!(result1.hash, result2.hash);
            assert_ne!(result2.hash, result3.hash);

            wirefilter_free_parsed_filter(filter1);
            wirefilter_free_parsed_filter(filter2);
            wirefilter_free_parsed_filter(filter3);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn get_version() {
        let version = wirefilter_get_version();
        let re = Regex::new(r"(?-u)^\d+\.\d+\.\d+$").unwrap();

        assert!(re.is_match(std::str::from_utf8(version.as_bytes()).unwrap()));
    }

    #[test]
    fn filter_uses() {
        let scheme = create_scheme();

        {
            let filter = parse_filter(
                &scheme,
                r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+" && map1["key"] == 42"#,
            ).ast
            .unwrap();

            let field = "num1";
            assert_eq!(
                wirefilter_filter_uses(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::USED
            );

            let field = "ip1";
            assert_eq!(
                wirefilter_filter_uses(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::USED
            );

            let field = "str2";
            assert_eq!(
                wirefilter_filter_uses(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::USED
            );

            let field = "str1";
            assert_eq!(
                wirefilter_filter_uses(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::UNUSED
            );

            let field = "ip2";
            assert_eq!(
                wirefilter_filter_uses(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::UNUSED
            );

            let field = "map1";
            assert_eq!(
                wirefilter_filter_uses(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::USED
            );

            let field = "map2";
            assert_eq!(
                wirefilter_filter_uses(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::UNUSED
            );

            wirefilter_free_parsed_filter(filter);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn filter_uses_list() {
        let scheme = create_scheme();

        {
            let filter = parse_filter(
                &scheme,
                r#"num1 in $numbers && num2 == 1337 && str2 != "hi" && ip2 == 10.10.10.10"#,
            )
            .ast
            .unwrap();

            let field = "num1";
            assert_eq!(
                wirefilter_filter_uses_list(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::USED,
            );

            let field = "num2";
            assert_eq!(
                wirefilter_filter_uses_list(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::UNUSED,
            );

            let field = "str1";
            assert_eq!(
                wirefilter_filter_uses_list(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::UNUSED,
            );

            let field = "str2";
            assert_eq!(
                wirefilter_filter_uses_list(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::UNUSED,
            );

            let field = "ip1";
            assert_eq!(
                wirefilter_filter_uses_list(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::UNUSED,
            );

            let field = "ip2";
            assert_eq!(
                wirefilter_filter_uses_list(&filter, field.as_ptr().cast(), field.len()),
                UsingResult::UNUSED,
            );

            wirefilter_free_parsed_filter(filter);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn execution_context_deserialize() {
        let scheme = create_scheme();
        let exec_context = *create_execution_context(&scheme);

        let expected: String = serde_json::to_string(exec_context.as_ref()).unwrap();
        assert!(expected.len() > 3);

        let mut exec_context_c = *wirefilter_create_execution_context(&scheme);
        let res = wirefilter_deserialize_json_to_execution_context(
            &mut exec_context_c,
            expected.as_ptr(),
            expected.len(),
        );
        assert_eq!(res, true);

        let expected_c: String = serde_json::to_string(exec_context_c.as_ref()).unwrap();
        assert_eq!(expected, expected_c);
    }

    #[test]
    fn ctype_convertion() {
        let cty = CType::from(Type::Bytes);

        assert_eq!(Type::from(cty), Type::Bytes);

        let cty = wirefilter_create_array_type(cty);

        assert_eq!(cty, CType::from(Type::Array(Type::Bytes.into())));

        assert_eq!(Type::from(cty), Type::Array(Type::Bytes.into()));

        let cty = wirefilter_create_map_type(cty);

        assert_eq!(
            cty,
            CType::from(Type::Map(Type::Array(Type::Bytes.into()).into()))
        );

        assert_eq!(
            Type::from(cty),
            Type::Map(Type::Array(Type::Bytes.into()).into())
        );
    }
}
