extern crate fnv;
extern crate libc;
extern crate wirefilter;

#[cfg(test)]
extern crate regex;

#[cfg(test)]
#[macro_use]
extern crate indoc;

mod transfer_types;

use fnv::FnvHasher;
use std::{
    hash::{Hash, Hasher},
    net::IpAddr,
};
use transfer_types::{
    ExternallyAllocatedByteArr, RustAllocatedString, RustBox, StaticRustAllocatedString,
};
use wirefilter::{ExecutionContext, Filter, ParseError, Scheme, Type};

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

#[repr(u8)]
pub enum ParsingResult<'s> {
    Err(RustAllocatedString),
    Ok(RustBox<Filter<'s>>),
}

impl<'s> From<Filter<'s>> for ParsingResult<'s> {
    fn from(filter: Filter<'s>) -> Self {
        ParsingResult::Ok(filter.into())
    }
}

impl<'s, 'a> From<ParseError<'a>> for ParsingResult<'s> {
    fn from(err: ParseError<'a>) -> Self {
        ParsingResult::Err(RustAllocatedString::from(err.to_string()))
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
pub extern "C" fn wirefilter_add_type_field_to_scheme(
    scheme: &mut Scheme,
    name: ExternallyAllocatedByteArr,
    ty: Type,
) {
    scheme.add_field(name.into(), ty)
}

#[no_mangle]
pub extern "C" fn wirefilter_free_parsing_result(result: ParsingResult) {
    drop(result);
}

#[no_mangle]
pub extern "C" fn wirefilter_parse_filter<'s, 'i>(
    scheme: &'s Scheme,
    input: ExternallyAllocatedByteArr<'i>,
) -> ParsingResult<'s> {
    let input = input.into();

    match scheme.parse(input) {
        Ok(filter) => ParsingResult::from(filter),
        Err(err) => ParsingResult::from(err),
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_get_filter_hash(filter: &Filter) -> u64 {
    let mut hasher = FnvHasher::default();
    filter.hash(&mut hasher);
    hasher.finish()
}

#[no_mangle]
pub extern "C" fn wirefilter_create_execution_context<'e, 's: 'e>(
    scheme: &'s Scheme,
) -> RustBox<ExecutionContext<'e>> {
    ExecutionContext::new(scheme).into()
}

#[no_mangle]
pub extern "C" fn wirefilter_free_execution_context(exec_context: RustBox<ExecutionContext>) {
    drop(exec_context);
}

#[no_mangle]
pub extern "C" fn wirefilter_add_unsigned_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: u64,
) {
    exec_context.set_field_value(name.into(), value);
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bytes_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: ExternallyAllocatedByteArr<'a>,
) {
    let slice: &'a [u8] = value.into();
    exec_context.set_field_value(name.into(), slice);
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv6_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: &[u8; 16],
) {
    exec_context.set_field_value(name.into(), IpAddr::from(*value));
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv4_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: &[u8; 4],
) {
    exec_context.set_field_value(name.into(), IpAddr::from(*value));
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bool_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: bool,
) {
    exec_context.set_field_value(name.into(), value);
}

#[no_mangle]
pub extern "C" fn wirefilter_match(filter: &Filter, exec_context: &ExecutionContext) -> bool {
    filter.execute(exec_context)
}

#[no_mangle]
pub extern "C" fn wirefilter_filter_uses(
    filter: &Filter,
    field_name: ExternallyAllocatedByteArr,
) -> bool {
    filter.uses(field_name.into()).unwrap()
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
            ExternallyAllocatedByteArr::from("ip1"),
            Type::Ip,
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedByteArr::from("ip2"),
            Type::Ip,
        );

        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedByteArr::from("str1"),
            Type::Bytes,
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedByteArr::from("str2"),
            Type::Bytes,
        );

        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedByteArr::from("num1"),
            Type::Unsigned,
        );
        wirefilter_add_type_field_to_scheme(
            &mut scheme,
            ExternallyAllocatedByteArr::from("num2"),
            Type::Unsigned,
        );

        scheme
    }

    fn create_execution_context<'e, 's: 'e>(scheme: &'s Scheme) -> RustBox<ExecutionContext<'e>> {
        let mut exec_context = wirefilter_create_execution_context(scheme);

        wirefilter_add_ipv4_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedByteArr::from("ip1"),
            &[127, 0, 0, 1],
        );

        wirefilter_add_ipv6_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedByteArr::from("ip2"),
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xFF\xFF\xC0\xA8\x00\x01",
        );

        wirefilter_add_bytes_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedByteArr::from("str1"),
            ExternallyAllocatedByteArr::from("Hey"),
        );

        wirefilter_add_bytes_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedByteArr::from("str2"),
            ExternallyAllocatedByteArr::from("yo123"),
        );

        wirefilter_add_unsigned_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedByteArr::from("num1"),
            42,
        );

        wirefilter_add_unsigned_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedByteArr::from("num2"),
            1337,
        );

        exec_context
    }

    fn parse_filter<'s>(scheme: &'s Scheme, input: &'static str) -> ParsingResult<'s> {
        wirefilter_parse_filter(scheme, ExternallyAllocatedByteArr::from(input))
    }

    fn validate_filter<'f, 's>(result: &'f ParsingResult<'s>) -> &'f Filter<'s> {
        match result {
            ParsingResult::Ok(filter) => filter,
            ParsingResult::Err(err) => panic!("{}", err.as_str()),
        }
    }

    fn match_filter(input: &'static str, scheme: &Scheme, exec_context: &ExecutionContext) -> bool {
        let parsing_result = parse_filter(scheme, input);
        let result = wirefilter_match(validate_filter(&parsing_result), exec_context);

        wirefilter_free_parsing_result(parsing_result);

        result
    }

    #[test]
    fn parse_error() {
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

            match &result {
                ParsingResult::Ok(_) => panic!("Error expected"),
                ParsingResult::Err(err) => {
                    assert_eq!(
                        err.as_str(),
                        indoc!(
                            r#"
                            Filter parsing error (4:13):
                                num1 == "abc"
                                        ^^^^^ expected digit
                            "#
                        )
                    );
                }
            }

            wirefilter_free_parsing_result(result);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn filter_parsing() {
        let scheme = create_scheme();

        {
            let parsing_result = parse_filter(&scheme, r#"num1 > 3 && str2 == "abc""#);
            validate_filter(&parsing_result);
            wirefilter_free_parsing_result(parsing_result);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn filter_matching() {
        let scheme = create_scheme();

        {
            let exec_context = create_execution_context(&scheme);

            assert!(match_filter(
                r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+""#,
                &scheme,
                &exec_context
            ));

            assert!(match_filter(
                r#"ip2 == 0:0:0:0:0:ffff:c0a8:1 && (str1 == "Hey" || str2 == "ya")"#,
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
            let parsing_result1 = parse_filter(
                &scheme,
                r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+""#,
            );
            let parsing_result2 = parse_filter(
                &scheme,
                r#"num1 >     41 && num2 == 1337 &&    ip1 != 192.168.0.1 and str2 ~ "yo\d+""#,
            );
            let parsing_result3 = parse_filter(&scheme, r#"num1 > 41 && num2 == 1337"#);

            let hash1 = wirefilter_get_filter_hash(validate_filter(&parsing_result1));
            let hash2 = wirefilter_get_filter_hash(validate_filter(&parsing_result2));
            let hash3 = wirefilter_get_filter_hash(validate_filter(&parsing_result3));

            assert_eq!(hash1, hash2);
            assert_ne!(hash2, hash3);

            wirefilter_free_parsing_result(parsing_result1);
            wirefilter_free_parsing_result(parsing_result2);
            wirefilter_free_parsing_result(parsing_result3);
        }

        wirefilter_free_scheme(scheme);
    }

    #[test]
    fn get_version() {
        let version = wirefilter_get_version();
        let re = Regex::new(r"\d+\.\d+\.\d+").unwrap();

        assert!(re.is_match(version.into()));
    }

    #[test]
    fn filter_uses() {
        let scheme = create_scheme();

        {
            let parsing_result = parse_filter(
                &scheme,
                r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+""#,
            );

            {
                let filter = validate_filter(&parsing_result);

                assert!(wirefilter_filter_uses(
                    filter,
                    ExternallyAllocatedByteArr::from("num1")
                ));

                assert!(wirefilter_filter_uses(
                    filter,
                    ExternallyAllocatedByteArr::from("ip1")
                ));

                assert!(wirefilter_filter_uses(
                    filter,
                    ExternallyAllocatedByteArr::from("str2")
                ));

                assert!(!wirefilter_filter_uses(
                    filter,
                    ExternallyAllocatedByteArr::from("str1")
                ));

                assert!(!wirefilter_filter_uses(
                    filter,
                    ExternallyAllocatedByteArr::from("ip2")
                ));
            }

            wirefilter_free_parsing_result(parsing_result);
        }

        wirefilter_free_scheme(scheme);
    }
}
