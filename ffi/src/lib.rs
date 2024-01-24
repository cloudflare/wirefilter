#![warn(rust_2018_idioms)]

pub mod panic;
pub mod transfer_types;

use crate::panic::catch_panic;
use crate::transfer_types::{
    ExternallyAllocatedByteArr, ExternallyAllocatedStr, RustAllocatedString, RustBox,
    StaticRustAllocatedString,
};
use fnv::FnvHasher;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::{
    convert::TryFrom,
    hash::Hasher,
    io::{self, Write},
    net::IpAddr,
};
use wirefilter::{AlwaysList, AlwaysListMatcher, Array, DefaultCompiler, ExecutionContext, FieldIndex, Filter, FilterAst, FunctionArgKind, FunctionArgs, IntListStore, IpListStore, LhsValue, List, ListDefinition, Map, NeverList, NeverListMatcher, ParseError, Scheme, SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionParam, Type};

const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Debug, Eq, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum CTypeTag {
    Ip,
    Bytes,
    Int,
    Bool,
    Array,
    Map,
}

#[derive(Debug, Clone)]
#[repr(C)]
pub struct CType {
    tag: u8,
    data: Option<Box<Type>>,
}

impl From<CType> for Type {
    fn from(ty: CType) -> Self {
        match CTypeTag::try_from(ty.tag).unwrap() {
            CTypeTag::Ip => Type::Ip,
            CTypeTag::Bytes => Type::Bytes,
            CTypeTag::Int => Type::Int,
            CTypeTag::Bool => Type::Bool,
            CTypeTag::Array => Type::Array(ty.data.unwrap()),
            CTypeTag::Map => Type::Map(ty.data.unwrap()),
        }
    }
}

impl From<Type> for CType {
    fn from(ty: Type) -> Self {
        match ty {
            Type::Ip => CType {
                tag: CTypeTag::Ip.into(),
                data: None,
            },
            Type::Bytes => CType {
                tag: CTypeTag::Bytes.into(),
                data: None,
            },
            Type::Int => CType {
                tag: CTypeTag::Int.into(),
                data: None,
            },
            Type::Bool => CType {
                tag: CTypeTag::Bool.into(),
                data: None,
            },
            Type::Array(arr) => CType {
                tag: CTypeTag::Array.into(),
                data: Some(arr),
            },
            Type::Map(map) => CType {
                tag: CTypeTag::Map.into(),
                data: Some(map),
            },
        }
    }
}

#[repr(u8)]
pub enum CResult<T> {
    Err(RustAllocatedString),
    Ok(T),
}

impl<T> CResult<T> {
    pub fn unwrap(self) -> T {
        match self {
            CResult::Err(err) => panic!("{}", &err as &str),
            CResult::Ok(ok) => ok,
        }
    }

    pub fn into_result(self) -> Result<T, RustAllocatedString> {
        match self {
            CResult::Ok(ok) => Ok(ok),
            CResult::Err(err) => Err(err),
        }
    }
}

pub type ParsingResult<'s> = CResult<RustBox<FilterAst<'s>>>;

impl<'s> From<FilterAst<'s>> for ParsingResult<'s> {
    fn from(filter_ast: FilterAst<'s>) -> Self {
        ParsingResult::Ok(filter_ast.into())
    }
}

impl<'s, 'a> From<ParseError<'a>> for ParsingResult<'s> {
    fn from(err: ParseError<'a>) -> Self {
        ParsingResult::Err(RustAllocatedString::from(err.to_string()))
    }
}

type UsingResult = CResult<bool>;

type CompilingResult<'s, 'e> = CResult<RustBox<Filter<'s>>>;

type MatchingResult = CResult<bool>;

type SerializingResult = CResult<RustAllocatedString>;

type HashingResult = CResult<u64>;

use wirefilter::types::GetType;

fn len_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    match args.next()? {
        Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap())),
        Err(Type::Bytes) => None,
        _ => unreachable!(),
    }
}

fn any_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    match args.next()? {
        Ok(v) => Some(LhsValue::Bool(
            Array::try_from(v)
                .unwrap()
                .into_iter()
                .any(|lhs| bool::try_from(lhs).unwrap()),
        )),
        Err(Type::Array(ref arr)) if arr.get_type() == Type::Bool => None,
        _ => unreachable!(),
    }
}

fn all_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    match args.next()? {
        Ok(v) => Some(LhsValue::Bool(
            Array::try_from(v)
                .unwrap()
                .into_iter()
                .all(|lhs| bool::try_from(lhs).unwrap()),
        )),
        Err(Type::Array(ref arr)) if arr.get_type() == Type::Bool => None,
        _ => unreachable!(),
    }
}

fn lower_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let input = args.next()?.ok()?;
    match input {
        LhsValue::Bytes(bytes) => Some(LhsValue::Bytes(bytes.to_ascii_lowercase().into())),
        _ => panic!("Invalid type: expected Bytes, got {:?}", input),
    }
}

fn upper_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let input = args.next()?.ok()?;
    match input {
        LhsValue::Bytes(bytes) => Some(LhsValue::Bytes(bytes.to_ascii_uppercase().into())),
        _ => panic!("Invalid type: expected Bytes, got {:?}", input),
    }
}

use percent_encoding::percent_decode;

fn url_decode<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let input = args.next()?.ok()?;
    let res = match input {
        LhsValue::Bytes(bytes) => Some(LhsValue::Bytes(percent_decode(&bytes).collect())),
        _ => panic!("Invalid type: expected Bytes, got {:?}", input),
    };
    return res;
}

#[no_mangle]
pub extern "C" fn add_standard_functions(
    scheme: &mut Scheme,
) {
    scheme
        .add_function(
            "any".into(),
            SimpleFunctionDefinition {
                params: vec![SimpleFunctionParam {
                    arg_kind: FunctionArgKind::Field,
                    val_type: Type::Array(Box::new(Type::Bool)),
                }],
                opt_params: vec![],
                return_type: Type::Bool,
                implementation: SimpleFunctionImpl::new(any_function),
            },
        )
        .unwrap();
    scheme
        .add_function(
            "all".into(),
            SimpleFunctionDefinition {
                params: vec![SimpleFunctionParam {
                    arg_kind: FunctionArgKind::Field,
                    val_type: Type::Array(Box::new(Type::Bool)),
                }],
                opt_params: vec![],
                return_type: Type::Bool,
                implementation: SimpleFunctionImpl::new(all_function),
            },
        )
        .unwrap();
    scheme
        .add_function(
            "lower".into(),
            SimpleFunctionDefinition {
                params: vec![SimpleFunctionParam {
                    arg_kind: FunctionArgKind::Field,
                    val_type: Type::Bytes,
                }],
                opt_params: vec![],
                return_type: Type::Bytes,
                implementation: SimpleFunctionImpl::new(lower_function),
            },
        )
        .unwrap();
    scheme
        .add_function(
            "upper".into(),
            SimpleFunctionDefinition {
                params: vec![SimpleFunctionParam {
                    arg_kind: FunctionArgKind::Field,
                    val_type: Type::Bytes,
                }],
                opt_params: vec![],
                return_type: Type::Bytes,
                implementation: SimpleFunctionImpl::new(upper_function),
            },
        )
        .unwrap();
    scheme
        .add_function(
            "len".into(),
            SimpleFunctionDefinition {
                params: vec![SimpleFunctionParam {
                    arg_kind: FunctionArgKind::Field,
                    val_type: Type::Bytes,
                }],
                opt_params: vec![],
                return_type: Type::Int,
                implementation: SimpleFunctionImpl::new(len_function),
            },
        )
        .unwrap();
    scheme
        .add_function(
            "url_decode".into(),
            SimpleFunctionDefinition {
                params: vec![SimpleFunctionParam {
                    arg_kind: FunctionArgKind::Field,
                    val_type: Type::Bytes,
                }],
                opt_params: vec![],
                return_type: Type::Bytes,
                implementation: SimpleFunctionImpl::new(url_decode),
            },
        )
        .unwrap();

    scheme
        .add_list(Type::Int.into(),  Box::new(IntListStore::new()))
        .unwrap();
    scheme
        .add_list(Type::Ip.into(),  Box::new(IpListStore::new()))
        .unwrap();
    scheme
        .add_list(Type::Bytes.into(),  Box::new(NeverList::default()))
        .unwrap();
}

#[no_mangle]
pub extern "C" fn set_all_lists_to_nevermatch(
    exec_context: &mut ExecutionContext<'_>,
) -> bool {
    let list = exec_context.scheme().get_list(&Type::Bytes).unwrap();
    exec_context.set_list_matcher(list, NeverListMatcher {}).unwrap();
    return true;
}


#[no_mangle]
pub extern "C" fn wirefilter_setup_int_lists(
    exec_context: &mut ExecutionContext<'_>,
    int_map: RustBox<LhsValue<'_>>
) {
    let list = exec_context.scheme().get_list(&Type::Int).unwrap();
    let mut int_lists = IntListStore::new();
    if let LhsValue::Map(map) = *int_map.into_real_box() {
        for (key, maybe_int_arr) in map.into_iter() {
            let list_name = std::str::from_utf8(&(*key)).unwrap();
            if let LhsValue::Array(ints) = maybe_int_arr {
                for value in ints {
                    if let LhsValue::Int(i) = value {
                        int_lists.add_value(&list_name, i)
                    }
                }
            }
        }
    }
    exec_context.set_list_matcher(list, int_lists).unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_setup_ip_lists(
    exec_context: &mut ExecutionContext<'_>,
    ip_map: RustBox<LhsValue<'_>>
) {
    let list = exec_context.scheme().get_list(&Type::Ip).unwrap();
    let mut ip_lists = IpListStore::new();
    if let LhsValue::Map(map) = *ip_map.into_real_box() {
        for (key, maybe_ip_arr) in map.into_iter() {
            let list_name = std::str::from_utf8(&(*key)).unwrap();
            if let LhsValue::Array(ints) = maybe_ip_arr {
                for value in ints {
                    if let LhsValue::Ip(addr) = value {
                        ip_lists.add_ip_value(&list_name, addr)
                    }
                }
            }
        }
    }
    exec_context.set_list_matcher(list, ip_lists).unwrap();
}



#[no_mangle]
pub extern "C" fn wirefilter_create_scheme() -> RustBox<Scheme> {
    Default::default()
}

#[no_mangle]
pub extern "C" fn wirefilter_free_scheme(scheme: RustBox<Scheme>) {
    drop(scheme);
}

#[no_mangle]
pub extern "C" fn wirefilter_create_map_type(ty: CType) -> CType {
    CType {
        tag: CTypeTag::Map.into(),
        data: Some(Box::new(Type::from(ty))),
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_create_array_type(ty: CType) -> CType {
    CType {
        tag: CTypeTag::Array.into(),
        data: Some(Box::new(Type::from(ty))),
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_add_type_field_to_scheme(
    scheme: &mut Scheme,
    name: ExternallyAllocatedStr<'_>,
    ty: CType,
) -> bool {
    scheme
        .add_field(name.into_ref().to_owned(), ty.into())
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_create_always_list() -> *mut Box<dyn ListDefinition> {
    Box::into_raw(Box::new(Box::new(AlwaysList::default())))
}

#[no_mangle]
pub extern "C" fn wirefilter_create_never_list() -> *mut Box<dyn ListDefinition> {
    Box::into_raw(Box::new(Box::new(NeverList::default())))
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[no_mangle]
pub extern "C" fn wirefilter_add_type_list_to_scheme(
    scheme: &mut Scheme,
    ty: CType,
    list: *mut Box<dyn ListDefinition>,
) -> bool {
    scheme
        .add_list(ty.into(), *unsafe { Box::from_raw(list) })
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_free_parsed_filter(filter_ast: RustBox<FilterAst<'_>>) {
    drop(filter_ast);
}

#[no_mangle]
pub extern "C" fn wirefilter_free_string(s: RustAllocatedString) {
    drop(s);
}

#[no_mangle]
pub extern "C" fn wirefilter_parse_filter<'s, 'i>(
    scheme: &'s Scheme,
    input: ExternallyAllocatedStr<'i>,
) -> ParsingResult<'s> {
    catch_panic(std::panic::AssertUnwindSafe(|| {
        match scheme.parse(input.into_ref()) {
            Ok(filter) => ParsingResult::from(filter),
            Err(err) => ParsingResult::from(err),
        }
    }))
}

#[no_mangle]
pub extern "C" fn wirefilter_free_filter_ast(ast: RustBox<FilterAst<'_>>) {
    drop(ast);
}

#[no_mangle]
pub extern "C" fn wirefilter_free_parsing_result(r: ParsingResult<'_>) {
    drop(r);
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

#[no_mangle]
pub extern "C" fn wirefilter_get_filter_hash(filter_ast: &FilterAst<'_>) -> HashingResult {
    let mut hasher = FnvHasher::default();
    // Serialize JSON to our Write-compatible wrapper around FnvHasher,
    // effectively calculating a hash for our filter in a streaming fashion
    // that is as stable as the JSON representation itself
    // (instead of relying on #[derive(Hash)] which would be tied to impl details).
    match serde_json::to_writer(HasherWrite(&mut hasher), filter_ast) {
        Ok(_) => HashingResult::Ok(hasher.finish()),
        Err(err) => {
            HashingResult::Err(format!("{} while serializing filter {:#?}", err, filter_ast).into())
        }
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_free_hashing_result(r: HashingResult) {
    drop(r);
}

#[no_mangle]
pub extern "C" fn wirefilter_serialize_filter_to_json(
    filter_ast: &FilterAst<'_>,
) -> SerializingResult {
    match serde_json::to_string(filter_ast) {
        Ok(ok) => SerializingResult::Ok(ok.into()),
        Err(err) => SerializingResult::Err(
            format!("{} while serializing filter {:#?}", err, filter_ast).into(),
        ),
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_serialize_scheme_to_json(scheme: &Scheme) -> SerializingResult {
    match serde_json::to_string(scheme) {
        Ok(ok) => SerializingResult::Ok(ok.into()),
        Err(err) => {
            SerializingResult::Err(format!("{} while serializing scheme {:#?}", err, scheme).into())
        }
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_serialize_type_to_json(ty: &CType) -> SerializingResult {
    match serde_json::to_string(&Type::from(ty.clone())) {
        Ok(ok) => SerializingResult::Ok(ok.into()),
        Err(err) => {
            SerializingResult::Err(format!("{} while serializing type {:#?}", err, ty).into())
        }
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_free_serializing_result(r: SerializingResult) {
    drop(r);
}

#[no_mangle]
pub extern "C" fn wirefilter_create_execution_context<'e, 's: 'e>(
    scheme: &'s Scheme,
) -> RustBox<ExecutionContext<'e>> {
    ExecutionContext::new(scheme).into()
}

#[no_mangle]
pub extern "C" fn wirefilter_serialize_execution_context_to_json<'a>(
    exec_context: &mut ExecutionContext<'a>,
) -> SerializingResult {
    match serde_json::to_string(exec_context) {
        Ok(ok) => SerializingResult::Ok(ok.into()),
        Err(err) => SerializingResult::Err(
            format!(
                "{} while serializing execution context {:#?}",
                err, exec_context
            )
            .into(),
        ),
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_free_execution_context(exec_context: RustBox<ExecutionContext<'_>>) {
    drop(exec_context);
}

#[no_mangle]
pub extern "C" fn wirefilter_add_int_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: i32,
) -> bool {
    let field = match exec_context.scheme().get_field(name.into_ref()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    exec_context.set_field_value(field, value).is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bytes_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: ExternallyAllocatedByteArr<'a>,
) -> bool {
    let slice: &[u8] = value.into_ref();
    let field = match exec_context.scheme().get_field(name.into_ref()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    exec_context.set_field_value(field, slice).is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv6_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: &[u8; 16],
) -> bool {
    let field = match exec_context.scheme().get_field(name.into_ref()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    exec_context
        .set_field_value(field, IpAddr::from(*value))
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv4_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: &[u8; 4],
) -> bool {
    let field = match exec_context.scheme().get_field(name.into_ref()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    exec_context
        .set_field_value(field, IpAddr::from(*value))
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bool_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: bool,
) -> bool {
    let field = match exec_context.scheme().get_field(name.into_ref()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    exec_context.set_field_value(field, value).is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_map_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: RustBox<LhsValue<'a>>,
) -> bool {
    let field = match exec_context.scheme().get_field(name.into_ref()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    exec_context
        .set_field_value(field, *value.into_real_box())
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_array_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: RustBox<LhsValue<'a>>,
) -> bool {
    let field = match exec_context.scheme().get_field(name.into_ref()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    exec_context
        .set_field_value(field, *value.into_real_box())
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_create_map<'a>(ty: CType) -> RustBox<LhsValue<'a>> {
    let map = Box::new(LhsValue::Map(Map::new(ty.into())));
    map.into()
}

// TODO: store a Box<[u8] inside FieldIndex::MapKey instead of String
// and call map.set(FieldIndex::MapKey(key), value.into()) directly
macro_rules! map_insert {
    ($map:ident, $name:ident, $value:ident) => {
        match $map {
            LhsValue::Map(map) => map.insert($name.into_ref(), $value.into()).is_ok(),
            _ => unreachable!(),
        }
    };
}

#[no_mangle]
pub extern "C" fn wirefilter_add_int_value_to_map(
    map: &mut LhsValue<'_>,
    name: ExternallyAllocatedByteArr<'_>,
    value: i32,
) -> bool {
    map_insert!(map, name, value)
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bytes_value_to_map<'a>(
    map: &mut LhsValue<'a>,
    name: ExternallyAllocatedByteArr<'_>,
    value: ExternallyAllocatedByteArr<'a>,
) -> bool {
    let slice: &[u8] = value.into_ref();
    map_insert!(map, name, slice)
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv6_value_to_map(
    map: &mut LhsValue<'_>,
    name: ExternallyAllocatedByteArr<'_>,
    value: &[u8; 16],
) -> bool {
    let value = IpAddr::from(*value);
    map_insert!(map, name, value)
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv4_value_to_map(
    map: &mut LhsValue<'_>,
    name: ExternallyAllocatedByteArr<'_>,
    value: &[u8; 4],
) -> bool {
    let value = IpAddr::from(*value);
    map_insert!(map, name, value)
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bool_value_to_map(
    map: &mut LhsValue<'_>,
    name: ExternallyAllocatedByteArr<'_>,
    value: bool,
) -> bool {
    map_insert!(map, name, value)
}

#[no_mangle]
pub extern "C" fn wirefilter_add_map_value_to_map<'a>(
    map: &mut LhsValue<'a>,
    name: ExternallyAllocatedByteArr<'_>,
    value: RustBox<LhsValue<'a>>,
) -> bool {
    let value = *value.into_real_box();
    map_insert!(map, name, value)
}

#[no_mangle]
pub extern "C" fn wirefilter_add_array_value_to_map<'a>(
    map: &mut LhsValue<'a>,
    name: ExternallyAllocatedByteArr<'_>,
    value: RustBox<LhsValue<'a>>,
) -> bool {
    let value = *value.into_real_box();
    map_insert!(map, name, value)
}

#[no_mangle]
pub extern "C" fn wirefilter_free_map(map: RustBox<LhsValue<'_>>) {
    drop(map)
}

#[no_mangle]
pub extern "C" fn wirefilter_create_array<'a>(ty: CType) -> RustBox<LhsValue<'a>> {
    let arr = Box::new(LhsValue::Array(Array::new(ty.into())));
    arr.into()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_int_value_to_array(
    array: &mut LhsValue<'_>,
    index: u32,
    value: i32,
) -> bool {
    array.set(FieldIndex::ArrayIndex(index), value).is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bytes_value_to_array<'a>(
    array: &mut LhsValue<'a>,
    index: u32,
    value: ExternallyAllocatedByteArr<'a>,
) -> bool {
    let slice: &[u8] = value.into_ref();
    array.set(FieldIndex::ArrayIndex(index), slice).is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv6_value_to_array(
    array: &mut LhsValue<'_>,
    index: u32,
    value: &[u8; 16],
) -> bool {
    array
        .set(FieldIndex::ArrayIndex(index), IpAddr::from(*value))
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv4_value_to_array(
    array: &mut LhsValue<'_>,
    index: u32,
    value: &[u8; 4],
) -> bool {
    array
        .set(FieldIndex::ArrayIndex(index), IpAddr::from(*value))
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bool_value_to_array(
    array: &mut LhsValue<'_>,
    index: u32,
    value: bool,
) -> bool {
    array.set(FieldIndex::ArrayIndex(index), value).is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_map_value_to_array<'a>(
    array: &mut LhsValue<'a>,
    index: u32,
    value: RustBox<LhsValue<'a>>,
) -> bool {
    array
        .set(FieldIndex::ArrayIndex(index), *value.into_real_box())
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_array_value_to_array<'a>(
    array: &mut LhsValue<'a>,
    index: u32,
    value: RustBox<LhsValue<'a>>,
) -> bool {
    array
        .set(FieldIndex::ArrayIndex(index), *value.into_real_box())
        .is_ok()
}

#[no_mangle]
pub extern "C" fn wirefilter_free_array(array: RustBox<LhsValue<'_>>) {
    drop(array)
}

#[no_mangle]
pub extern "C" fn wirefilter_compile_filter<'s>(
    filter_ast: RustBox<FilterAst<'s>>,
) -> CompilingResult<'_, '_> {
    catch_panic(std::panic::AssertUnwindSafe(|| {
        let filter_ast = filter_ast.into_real_box();
        CompilingResult::Ok(filter_ast.compile().into())
    }))
}

#[no_mangle]
pub extern "C" fn wirefilter_free_compiling_result(r: CompilingResult<'_, '_>) {
    drop(r);
}

#[no_mangle]
pub extern "C" fn wirefilter_match<'e, 's: 'e>(
    filter: &Filter<'s>,
    exec_context: &ExecutionContext<'e>,
) -> MatchingResult {
    catch_panic(std::panic::AssertUnwindSafe(|| {
        match filter.execute(exec_context) {
            Ok(ok) => MatchingResult::Ok(ok),
            Err(err) => MatchingResult::Err(RustAllocatedString::from(err.to_string())),
        }
    }))
}

#[no_mangle]
pub extern "C" fn wirefilter_free_matching_result(r: MatchingResult) {
    drop(r);
}

#[no_mangle]
pub extern "C" fn wirefilter_free_compiled_filter(filter: RustBox<Filter<'_>>) {
    drop(filter);
}

#[no_mangle]
pub extern "C" fn wirefilter_filter_uses(
    filter_ast: &FilterAst<'_>,
    field_name: ExternallyAllocatedStr<'_>,
) -> UsingResult {
    catch_panic(std::panic::AssertUnwindSafe(|| {
        match filter_ast.uses(field_name.into_ref()) {
            Ok(ok) => UsingResult::Ok(ok),
            Err(err) => UsingResult::Err(RustAllocatedString::from(err.to_string())),
        }
    }))
}

#[no_mangle]
pub extern "C" fn wirefilter_filter_uses_list(
    filter_ast: &FilterAst<'_>,
    field_name: ExternallyAllocatedStr<'_>,
) -> UsingResult {
    catch_panic(std::panic::AssertUnwindSafe(|| {
        match filter_ast.uses_list(field_name.into_ref()) {
            Ok(ok) => UsingResult::Ok(ok),
            Err(err) => UsingResult::Err(RustAllocatedString::from(err.to_string())),
        }
    }))
}

#[no_mangle]
pub extern "C" fn wirefilter_free_using_result(r: UsingResult) {
    drop(r);
}

#[no_mangle]
pub extern "C" fn wirefilter_get_version() -> StaticRustAllocatedString {
    StaticRustAllocatedString::from(VERSION)
}

#[cfg(test)]
mod ffi_test {
    use super::*;
    use regex::Regex;

    fn create_scheme() -> RustBox<Scheme> {
        let mut scheme = wirefilter_create_scheme();

        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("ip1"),
            Type::Ip.into(),
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("ip2"),
            Type::Ip.into(),
        );

        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("str1"),
            Type::Bytes.into(),
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("str2"),
            Type::Bytes.into(),
        );

        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("num1"),
            Type::Int.into(),
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("num2"),
            Type::Int.into(),
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("map1"),
            wirefilter_create_map_type(Type::Int.into()),
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("map2"),
            wirefilter_create_map_type(Type::Bytes.into()),
        );
        let int_list_def: Box<dyn ListDefinition> = Box::new(IntListStore::new());
        wirefilter_add_type_list_to_scheme(
            &mut scheme,
            Type::Int.into(),
            Box::into_raw(int_list_def.into()),
        );

        let ip_list_def: Box<dyn ListDefinition> = Box::new(IpListStore::new());
        wirefilter_add_type_list_to_scheme(
            &mut scheme,
            Type::Ip.into(),
            Box::into_raw(ip_list_def.into()),
        );

        scheme
    }

    fn create_execution_context<'e, 's: 'e>(scheme: &'s Scheme) -> RustBox<ExecutionContext<'e>> {
        let mut exec_context = wirefilter_create_execution_context(scheme);
        let invalid_key = &b"\xc3\x28"[..];

        assert!(std::str::from_utf8(invalid_key).is_err());

        wirefilter_add_ipv4_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("ip1"),
            &[127, 0, 0, 1],
        );

        wirefilter_add_ipv6_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("ip2"),
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xFF\xFF\xC0\xA8\x00\x01",
        );

        wirefilter_add_bytes_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("str1"),
            ExternallyAllocatedByteArr::from("Hey"),
        );

        wirefilter_add_bytes_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("str2"),
            ExternallyAllocatedByteArr::from("yo123"),
        );

        wirefilter_add_int_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("num1"),
            42,
        );

        wirefilter_add_int_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("num2"),
            1337,
        );

        let mut map1 = wirefilter_create_map(Type::Int.into());

        wirefilter_add_int_value_to_map(&mut map1, ExternallyAllocatedByteArr::from("key"), 42);

        wirefilter_add_int_value_to_map(
            &mut map1,
            ExternallyAllocatedByteArr::from(invalid_key),
            42,
        );

        wirefilter_add_map_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("map1"),
            map1,
        );

        let mut map2 = wirefilter_create_map(Type::Bytes.into());

        wirefilter_add_bytes_value_to_map(
            &mut map2,
            ExternallyAllocatedByteArr::from("key"),
            ExternallyAllocatedByteArr::from("value"),
        );

        wirefilter_add_bytes_value_to_map(
            &mut map2,
            ExternallyAllocatedByteArr::from(invalid_key),
            ExternallyAllocatedByteArr::from("value"),
        );

        wirefilter_add_map_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("map2"),
            map2,
        );

        exec_context
    }

    fn parse_filter<'s>(scheme: &'s Scheme, input: &'static str) -> ParsingResult<'s> {
        wirefilter_parse_filter(scheme, ExternallyAllocatedStr::from(input))
    }

    fn match_filter(
        input: &'static str,
        scheme: &Scheme,
        exec_context: &ExecutionContext<'_>,
    ) -> bool {
        let filter = parse_filter(scheme, input).unwrap();
        let filter = wirefilter_compile_filter(filter).unwrap();

        let result = wirefilter_match(&filter, exec_context);

        wirefilter_free_compiled_filter(filter);

        result.unwrap()
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
            let result = parse_filter(&scheme, src);

            match result {
                ParsingResult::Ok(_) => panic!("Error expected"),
                ParsingResult::Err(err) => {
                    assert_eq!(
                        &err as &str,
                        indoc!(
                            r#"
                            Filter parsing error (4:13):
                                num1 == "abc"
                                        ^^^^^ expected digit
                            "#
                        )
                    );
                    wirefilter_free_string(err);
                }
            }
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn filter_parsing() {
        let scheme = create_scheme();

        {
            let filter = parse_filter(&scheme, r#"num1 > 3 && str2 == "abc""#).unwrap();

            let json = wirefilter_serialize_filter_to_json(&filter).unwrap();

            assert_eq!(
                &json as &str,
                r#"{"op":"And","items":[{"lhs":"num1","op":"GreaterThan","rhs":3},{"lhs":"str2","op":"Equal","rhs":"abc"}]}"#
            );

            wirefilter_free_string(json);

            wirefilter_free_parsed_filter(filter);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn scheme_serialize() {
        let scheme = create_scheme();
        let json = wirefilter_serialize_scheme_to_json(&scheme).unwrap();

        let expected: String = serde_json::to_string(&*scheme).unwrap();
        assert_eq!(&json as &str, expected);

        wirefilter_free_string(json);

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn filter_matching() {
        let scheme = create_scheme();

        {
            let exec_context = create_execution_context(&scheme);

            assert!(match_filter(
                r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+" && map2["key"] == "value""#,
                &scheme,
                &exec_context
            ));

            assert!(match_filter(
                r#"ip2 == 0:0:0:0:0:ffff:c0a8:1 && (str1 == "Hey" || str2 == "ya") && (map1["key"] == 42 || map2["key2"] == "value")"#,
                &scheme,
                &exec_context
            ));

            assert!(!match_filter(
                "ip1 == 127.0.0.1 && ip2 == 0:0:0:0:0:ffff:c0a8:2",
                &scheme,
                &exec_context
            ));

            wirefilter_free_execution_context(exec_context);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn int_list_filter_matching() {
        let scheme = create_scheme();
        {
            let mut ctx = create_execution_context(&scheme);
            let mut int_map = wirefilter_create_map(Type::Array(Box::new(Type::Int)).into());
            let mut test_list_arr = wirefilter_create_array(Type::Int.into());
            wirefilter_add_int_value_to_array(&mut test_list_arr, 0, 42);
            wirefilter_add_array_value_to_map(&mut int_map, ExternallyAllocatedByteArr::from("test_list"), test_list_arr);
            wirefilter_setup_int_lists(&mut ctx, int_map);

            assert!(match_filter(r#"num1 in $test_list"#, &scheme, &ctx));

            wirefilter_free_execution_context(ctx);
        }
        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn ip_list_filter_matching() {
        let scheme = create_scheme();
        {
            let mut ctx = create_execution_context(&scheme);
            let mut ip_map = wirefilter_create_map(Type::Array(Box::new(Type::Ip)).into());
            let mut test_list_arr = wirefilter_create_array(Type::Ip.into());
            wirefilter_add_ipv4_value_to_array(&mut test_list_arr, 0, &[127, 0, 0, 1]);
            wirefilter_add_array_value_to_map(&mut ip_map, ExternallyAllocatedByteArr::from("test_list"), test_list_arr);
            wirefilter_setup_ip_lists(&mut ctx, ip_map);

            assert!(match_filter(r#"ip1 in $test_list"#, &scheme, &ctx));

            wirefilter_free_execution_context(ctx);
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
            )
            .unwrap();

            let filter2 = parse_filter(
                &scheme,
                r#"num1 >     41 && num2 == 1337 &&    ip1 != 192.168.0.1 and str2 ~ "yo\d+"    && map1["key"] == 42   "#,
            )
            .unwrap();

            let filter3 = parse_filter(&scheme, r#"num1 > 41 && num2 == 1337"#).unwrap();

            let hash1 = wirefilter_get_filter_hash(&filter1).unwrap();
            let hash2 = wirefilter_get_filter_hash(&filter2).unwrap();
            let hash3 = wirefilter_get_filter_hash(&filter3).unwrap();

            assert_eq!(hash1, hash2);
            assert_ne!(hash2, hash3);

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

        assert!(re.is_match(version.into_ref()));
    }

    #[test]
    fn filter_uses() {
        let scheme = create_scheme();

        {
            let filter = parse_filter(
                &scheme,
                r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+" && map1["key"] == 42"#,
            )
            .unwrap();

            assert!(wirefilter_filter_uses(&filter, ExternallyAllocatedStr::from("num1")).unwrap());

            assert!(wirefilter_filter_uses(&filter, ExternallyAllocatedStr::from("ip1")).unwrap());

            assert!(wirefilter_filter_uses(&filter, ExternallyAllocatedStr::from("str2")).unwrap());

            assert!(
                !wirefilter_filter_uses(&filter, ExternallyAllocatedStr::from("str1")).unwrap()
            );

            assert!(!wirefilter_filter_uses(&filter, ExternallyAllocatedStr::from("ip2")).unwrap());

            assert!(wirefilter_filter_uses(&filter, ExternallyAllocatedStr::from("map1")).unwrap());

            assert!(
                !wirefilter_filter_uses(&filter, ExternallyAllocatedStr::from("map2")).unwrap()
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
            .unwrap();

            assert_eq!(
                wirefilter_filter_uses_list(&filter, ExternallyAllocatedStr::from("num1")).unwrap(),
                true,
            );

            assert_eq!(
                wirefilter_filter_uses_list(&filter, ExternallyAllocatedStr::from("num2")).unwrap(),
                false,
            );

            assert_eq!(
                wirefilter_filter_uses_list(&filter, ExternallyAllocatedStr::from("str1")).unwrap(),
                false
            );

            assert_eq!(
                wirefilter_filter_uses_list(&filter, ExternallyAllocatedStr::from("str2")).unwrap(),
                false,
            );

            assert_eq!(
                wirefilter_filter_uses_list(&filter, ExternallyAllocatedStr::from("ip1")).unwrap(),
                false,
            );

            assert_eq!(
                wirefilter_filter_uses_list(&filter, ExternallyAllocatedStr::from("ip2")).unwrap(),
                false,
            );

            wirefilter_free_parsed_filter(filter);
        }

        wirefilter_free_scheme(scheme);
    }
}
