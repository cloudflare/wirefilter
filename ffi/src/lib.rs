pub mod transfer_types;

use crate::transfer_types::{
    ExternallyAllocatedByteArr, ExternallyAllocatedStr, RustAllocatedString, RustBox,
    StaticRustAllocatedString,
};
use fnv::FnvHasher;
use std::{
    hash::Hasher,
    io::{self, Write},
    net::IpAddr,
};
use wirefilter::{
    Array, ExecutionContext, FieldIndex, Filter, FilterAst, LhsValue, Map, ParseError, Scheme, Type,
};

const VERSION: &str = env!("CARGO_PKG_VERSION");

#[repr(u8)]
pub enum ParsingResult<'s> {
    Err(RustAllocatedString),
    Ok(RustBox<FilterAst<'s>>),
}

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

impl<'s> ParsingResult<'s> {
    pub fn unwrap(self) -> RustBox<FilterAst<'s>> {
        match self {
            ParsingResult::Err(err) => panic!("{}", &err as &str),
            ParsingResult::Ok(filter) => filter,
        }
    }
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
pub extern "C" fn wirefilter_create_map_type(ty: Type) -> Type {
    Type::Map(Box::new(ty))
}

#[no_mangle]
pub extern "C" fn wirefilter_create_array_type(ty: Type) -> Type {
    Type::Array(Box::new(ty))
}

#[no_mangle]
pub extern "C" fn wirefilter_add_type_field_to_scheme(
    scheme: &mut Scheme,
    name: ExternallyAllocatedStr<'_>,
    ty: Type,
) {
    scheme.add_field(name.into_ref().to_owned(), ty).unwrap();
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
    match scheme.parse(input.into_ref()) {
        Ok(filter) => ParsingResult::from(filter),
        Err(err) => ParsingResult::from(err),
    }
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

fn unwrap_json_result<T>(filter_ast: &FilterAst<'_>, result: serde_json::Result<T>) -> T {
    // Filter serialisation must never fail.
    result.unwrap_or_else(|err| panic!("{} while serializing filter {:#?}", err, filter_ast))
}

#[no_mangle]
pub extern "C" fn wirefilter_get_filter_hash(filter_ast: &FilterAst<'_>) -> u64 {
    let mut hasher = FnvHasher::default();
    // Serialize JSON to our Write-compatible wrapper around FnvHasher,
    // effectively calculating a hash for our filter in a streaming fashion
    // that is as stable as the JSON representation itself
    // (instead of relying on #[derive(Hash)] which would be tied to impl details).
    let result = serde_json::to_writer(HasherWrite(&mut hasher), filter_ast);
    unwrap_json_result(filter_ast, result);
    hasher.finish()
}

#[no_mangle]
pub extern "C" fn wirefilter_serialize_filter_to_json(
    filter_ast: &FilterAst<'_>,
) -> RustAllocatedString {
    let result = serde_json::to_string(filter_ast);
    unwrap_json_result(filter_ast, result).into()
}

#[no_mangle]
pub extern "C" fn wirefilter_create_execution_context<'e, 's: 'e>(
    scheme: &'s Scheme,
) -> RustBox<ExecutionContext<'e>> {
    ExecutionContext::new(scheme).into()
}

#[no_mangle]
pub extern "C" fn wirefilter_free_execution_context(exec_context: RustBox<ExecutionContext<'_>>) {
    drop(exec_context);
}

#[no_mangle]
pub extern "C" fn wirefilter_add_int_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: i32,
) {
    exec_context
        .set_field_value(name.into_ref(), value)
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bytes_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: ExternallyAllocatedByteArr<'a>,
) {
    let slice: &[u8] = value.into_ref();
    exec_context
        .set_field_value(name.into_ref(), slice)
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv6_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: &[u8; 16],
) {
    exec_context
        .set_field_value(name.into_ref(), IpAddr::from(*value))
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv4_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: &[u8; 4],
) {
    exec_context
        .set_field_value(name.into_ref(), IpAddr::from(*value))
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bool_value_to_execution_context(
    exec_context: &mut ExecutionContext<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: bool,
) {
    exec_context
        .set_field_value(name.into_ref(), value)
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_map_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: RustBox<LhsValue<'a>>,
) {
    exec_context
        .set_field_value(name.into_ref(), *value.into_real_box())
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_array_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: RustBox<LhsValue<'a>>,
) {
    exec_context
        .set_field_value(name.into_ref(), *value.into_real_box())
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_create_map<'a>(ty: Type) -> RustBox<LhsValue<'a>> {
    let map = Box::new(LhsValue::Map(Map::new(ty)));
    map.into()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_int_value_to_map(
    map: &mut LhsValue<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: i32,
) {
    map.set(FieldIndex::MapKey(name.into_ref().to_string()), value)
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bytes_value_to_map<'a>(
    map: &mut LhsValue<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: ExternallyAllocatedByteArr<'a>,
) {
    let slice: &[u8] = value.into_ref();
    map.set(FieldIndex::MapKey(name.into_ref().to_string()), slice)
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv6_value_to_map(
    map: &mut LhsValue<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: &[u8; 16],
) {
    map.set(
        FieldIndex::MapKey(name.into_ref().to_string()),
        IpAddr::from(*value),
    )
    .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv4_value_to_map(
    map: &mut LhsValue<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: &[u8; 4],
) {
    map.set(
        FieldIndex::MapKey(name.into_ref().to_string()),
        IpAddr::from(*value),
    )
    .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bool_value_to_map(
    map: &mut LhsValue<'_>,
    name: ExternallyAllocatedStr<'_>,
    value: bool,
) {
    map.set(FieldIndex::MapKey(name.into_ref().to_string()), value)
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_map_value_to_map<'a>(
    map: &mut LhsValue<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: RustBox<LhsValue<'a>>,
) {
    map.set(
        FieldIndex::MapKey(name.into_ref().to_string()),
        *value.into_real_box(),
    )
    .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_array_value_to_map<'a>(
    map: &mut LhsValue<'a>,
    name: ExternallyAllocatedStr<'_>,
    value: RustBox<LhsValue<'a>>,
) {
    map.set(
        FieldIndex::MapKey(name.into_ref().to_string()),
        *value.into_real_box(),
    )
    .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_free_map(map: RustBox<LhsValue<'_>>) {
    drop(map)
}

#[no_mangle]
pub extern "C" fn wirefilter_create_array<'a>(ty: Type) -> RustBox<LhsValue<'a>> {
    let arr = Box::new(LhsValue::Array(Array::new(ty)));
    arr.into()
}

#[no_mangle]
pub extern "C" fn wirefilter_add_int_value_to_array(
    array: &mut LhsValue<'_>,
    index: u32,
    value: i32,
) {
    array.set(FieldIndex::ArrayIndex(index), value).unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bytes_value_to_array<'a>(
    array: &mut LhsValue<'a>,
    index: u32,
    value: ExternallyAllocatedByteArr<'a>,
) {
    let slice: &[u8] = value.into_ref();
    array.set(FieldIndex::ArrayIndex(index), slice).unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv6_value_to_array(
    array: &mut LhsValue<'_>,
    index: u32,
    value: &[u8; 16],
) {
    array
        .set(FieldIndex::ArrayIndex(index), IpAddr::from(*value))
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv4_value_to_array(
    array: &mut LhsValue<'_>,
    index: u32,
    value: &[u8; 4],
) {
    array
        .set(FieldIndex::ArrayIndex(index), IpAddr::from(*value))
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bool_value_to_array(
    array: &mut LhsValue<'_>,
    index: u32,
    value: bool,
) {
    array.set(FieldIndex::ArrayIndex(index), value).unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_map_value_to_array<'a>(
    array: &mut LhsValue<'a>,
    index: u32,
    value: RustBox<LhsValue<'a>>,
) {
    array
        .set(FieldIndex::ArrayIndex(index), *value.into_real_box())
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_add_array_value_to_array<'a>(
    array: &mut LhsValue<'a>,
    index: u32,
    value: RustBox<LhsValue<'a>>,
) {
    array
        .set(FieldIndex::ArrayIndex(index), *value.into_real_box())
        .unwrap();
}

#[no_mangle]
pub extern "C" fn wirefilter_free_array(array: RustBox<LhsValue<'_>>) {
    drop(array)
}

#[no_mangle]
pub extern "C" fn wirefilter_compile_filter<'s>(
    filter_ast: RustBox<FilterAst<'s>>,
) -> RustBox<Filter<'s>> {
    let filter_ast = filter_ast.into_real_box();
    filter_ast.compile().into()
}

#[no_mangle]
pub extern "C" fn wirefilter_match<'s>(
    filter: &Filter<'s>,
    exec_context: &ExecutionContext<'s>,
) -> bool {
    filter.execute(exec_context).unwrap()
}

#[no_mangle]
pub extern "C" fn wirefilter_free_compiled_filter(filter: RustBox<Filter<'_>>) {
    drop(filter);
}

#[no_mangle]
pub extern "C" fn wirefilter_filter_uses(
    filter_ast: &FilterAst<'_>,
    field_name: ExternallyAllocatedStr<'_>,
) -> bool {
    filter_ast.uses(field_name.into_ref()).unwrap()
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
            Type::Ip,
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("ip2"),
            Type::Ip,
        );

        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("str1"),
            Type::Bytes,
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("str2"),
            Type::Bytes,
        );

        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("num1"),
            Type::Int,
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("num2"),
            Type::Int,
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("map1"),
            wirefilter_create_map_type(Type::Int),
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedStr::from("map2"),
            wirefilter_create_map_type(Type::Bytes),
        );

        scheme
    }

    fn create_execution_context<'e, 's: 'e>(scheme: &'s Scheme) -> RustBox<ExecutionContext<'e>> {
        let mut exec_context = wirefilter_create_execution_context(scheme);

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

        let mut map1 = wirefilter_create_map(Type::Int);

        wirefilter_add_int_value_to_map(&mut map1, ExternallyAllocatedStr::from("key"), 42);

        wirefilter_add_map_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedStr::from("map1"),
            map1,
        );

        let mut map2 = wirefilter_create_map(Type::Bytes);

        wirefilter_add_bytes_value_to_map(
            &mut map2,
            ExternallyAllocatedStr::from("key"),
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
        let filter = wirefilter_compile_filter(filter);

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

            let json = wirefilter_serialize_filter_to_json(&filter);

            assert_eq!(&json as &str, r#"{"op":"And","items":[{"lhs":"num1","op":"GreaterThan","rhs":3},{"lhs":"str2","op":"Equal","rhs":"abc"}]}"#);

            wirefilter_free_string(json);

            wirefilter_free_parsed_filter(filter);
        }

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

            let hash1 = wirefilter_get_filter_hash(&filter1);
            let hash2 = wirefilter_get_filter_hash(&filter2);
            let hash3 = wirefilter_get_filter_hash(&filter3);

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

            assert!(wirefilter_filter_uses(
                &filter,
                ExternallyAllocatedStr::from("num1")
            ));

            assert!(wirefilter_filter_uses(
                &filter,
                ExternallyAllocatedStr::from("ip1")
            ));

            assert!(wirefilter_filter_uses(
                &filter,
                ExternallyAllocatedStr::from("str2")
            ));

            assert!(!wirefilter_filter_uses(
                &filter,
                ExternallyAllocatedStr::from("str1")
            ));

            assert!(!wirefilter_filter_uses(
                &filter,
                ExternallyAllocatedStr::from("ip2")
            ));

            assert!(wirefilter_filter_uses(
                &filter,
                ExternallyAllocatedStr::from("map1")
            ));

            assert!(!wirefilter_filter_uses(
                &filter,
                ExternallyAllocatedStr::from("map2")
            ));

            wirefilter_free_parsed_filter(filter);
        }

        wirefilter_free_scheme(scheme);
    }
}
