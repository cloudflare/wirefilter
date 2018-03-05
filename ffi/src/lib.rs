extern crate fnv;
extern crate libc;
extern crate wirefilter;

#[cfg(test)]
extern crate regex;

mod transfer_types;

use fnv::FnvHasher;
use libc::size_t;
use std::cmp::max;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::net::IpAddr;
use transfer_types::{ExternallyAllocatedByteArr, RustAllocatedString, StaticRustAllocatedString};
use wirefilter::{Context, Filter};
use wirefilter::lex::LexErrorKind;
use wirefilter::types::{LhsValue, Type};

#[cfg(test)]
use regex::Regex;

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

pub struct ParseError<'a> {
    msg: String,
    span_start: size_t,
    span_len: size_t,
    input: &'a str,
}

impl<'a> ParseError<'a> {
    pub fn new(input: &'a str, (err, span): (LexErrorKind, &str)) -> Self {
        ParseError {
            msg: err.to_string(),
            span_start: span.as_ptr() as usize - input.as_ptr() as usize,
            span_len: span.len(),
            input,
        }
    }
}

impl<'a> fmt::Display for ParseError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Filter parsing error:")?;
        writeln!(f, "`{}`", self.input)?;

        for _ in 0..1 + self.span_start {
            write!(f, " ")?;
        }

        for _ in 0..max(1, self.span_len) {
            write!(f, "^")?;
        }

        writeln!(f, " {}", self.msg)
    }
}

#[repr(u8)]
pub enum ParsingResult<'a> {
    Err(RustAllocatedString),
    Ok(*mut Filter<'a>),
}

impl<'a> From<Filter<'a>> for ParsingResult<'a> {
    fn from(filter: Filter<'a>) -> Self {
        ParsingResult::Ok(Box::into_raw(Box::new(filter)))
    }
}

impl<'a, 'b> From<ParseError<'b>> for ParsingResult<'a> {
    fn from(err: ParseError<'b>) -> Self {
        let msg = RustAllocatedString::from(err.to_string());
        ParsingResult::Err(msg)
    }
}

impl<'a> Drop for ParsingResult<'a> {
    fn drop(&mut self) {
        if let ParsingResult::Ok(filter) = *self {
            drop(unsafe { Box::from_raw(filter) });
        }
    }
}

pub type Scheme = Context<String, Type>;

#[no_mangle]
pub unsafe extern "C" fn wirefilter_create_scheme() -> *mut Scheme {
    Box::into_raw(Box::new(Context::default()))
}

#[no_mangle]
pub extern "C" fn wirefilter_free_scheme(scheme: *mut Scheme) {
    drop(unsafe { Box::from_raw(scheme) });
}

#[no_mangle]
pub extern "C" fn wirefilter_add_type_field_to_scheme(
    scheme: &mut Scheme,
    name: ExternallyAllocatedByteArr,
    ty: Type,
) {
    scheme.insert(name.into(), ty)
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
        Err(err) => ParsingResult::from(ParseError::new(input, err)),
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_get_filter_hash(filter: &Filter) -> u64 {
    let mut hasher = FnvHasher::default();
    filter.hash(&mut hasher);
    hasher.finish()
}

pub type ExecutionContext<'a> = Context<&'a str, LhsValue<'a>>;

// NOTE: we bind lifetime of the ExecutionContext to the Scheme here to
// get rid of unbounded lifetime.
// See: https://doc.rust-lang.org/beta/nomicon/unbounded-lifetimes.html
#[no_mangle]
pub unsafe extern "C" fn wirefilter_create_execution_context<'e, 's: 'e>(
    _scheme: &'s Scheme,
) -> *mut ExecutionContext<'e> {
    Box::into_raw(Box::new(Context::default()))
}

#[no_mangle]
pub extern "C" fn wirefilter_free_execution_context(exec_context: *mut ExecutionContext) {
    drop(unsafe { Box::from_raw(exec_context) });
}

#[no_mangle]
pub extern "C" fn wirefilter_add_unsigned_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: u64,
) {
    exec_context.insert(name.into(), LhsValue::Unsigned(value));
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bytes_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: ExternallyAllocatedByteArr<'a>,
) {
    let slice: &'a [u8] = value.into();
    exec_context.insert(name.into(), LhsValue::Bytes(slice.into()));
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv6_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: [u8; 16],
) {
    exec_context.insert(name.into(), LhsValue::Ip(IpAddr::from(value)));
}

#[no_mangle]
pub extern "C" fn wirefilter_add_ipv4_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: [u8; 4],
) {
    exec_context.insert(name.into(), LhsValue::Ip(IpAddr::from(value)));
}

#[no_mangle]
pub extern "C" fn wirefilter_add_bool_value_to_execution_context<'a>(
    exec_context: &mut ExecutionContext<'a>,
    name: ExternallyAllocatedByteArr<'a>,
    value: bool,
) {
    exec_context.insert(name.into(), LhsValue::Bool(value));
}

#[no_mangle]
pub extern "C" fn wirefilter_match(filter: &Filter, exec_context: &ExecutionContext) -> bool {
    exec_context.execute(filter)
}

#[no_mangle]
pub extern "C" fn wirefilter_get_version() -> StaticRustAllocatedString {
    StaticRustAllocatedString::from(VERSION)
}

#[cfg(test)]
mod ffi_test {
    use super::*;
    use wirefilter::{Field, FilterOp};
    use wirefilter::op::{CombiningOp, OrderingOp};
    use wirefilter::types::RhsValue;

    fn create_scheme() -> Box<Scheme> {
        let mut scheme = unsafe { Box::from_raw(wirefilter_create_scheme()) };

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

    fn create_execution_context<'e, 's: 'e>(scheme: &'s Scheme) -> Box<ExecutionContext<'e>> {
        let mut exec_context =
            unsafe { Box::from_raw(wirefilter_create_execution_context(scheme)) };

        wirefilter_add_ipv4_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedByteArr::from("ip1"),
            [127, 0, 0, 1],
        );

        wirefilter_add_ipv6_value_to_execution_context(
            &mut exec_context,
            ExternallyAllocatedByteArr::from("ip2"),
            *b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xFF\xFF\xC0\xA8\x00\x01",
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

    fn create_filter<'a>(
        scheme: &'a Scheme,
        input: &'static str,
    ) -> (&'a Filter<'a>, ParsingResult<'a>) {
        let result = wirefilter_parse_filter(scheme, ExternallyAllocatedByteArr::from(input));

        match result {
            ParsingResult::Ok(filter) => (unsafe { &*filter }, result),
            ParsingResult::Err(ref err) => panic!("{}", err.as_str()),
        }
    }

    fn match_filter(input: &'static str, scheme: &Scheme, exec_context: &ExecutionContext) -> bool {
        let (filter, parsing_result) = create_filter(scheme, input);
        let result = wirefilter_match(filter, exec_context);

        wirefilter_free_parsing_result(parsing_result);

        result
    }

    #[test]
    fn parse_error() {
        let src = r#"num1 == "abc""#;
        let scheme = create_scheme();

        {
            let result = wirefilter_parse_filter(&scheme, ExternallyAllocatedByteArr::from(src));

            match result {
                ParsingResult::Ok(_) => panic!("Error expected"),
                ParsingResult::Err(ref err) => assert_eq!(
                    err.as_str(),
                    "Filter parsing error:\n`num1 == \"abc\"`\n         ^^^^^ expected digit\n"
                ),
            }

            wirefilter_free_parsing_result(result);
        }

        wirefilter_free_scheme(Box::into_raw(scheme));
    }

    #[test]
    fn parse_filter() {
        let scheme = create_scheme();

        {
            let (filter, parsing_result) = create_filter(&scheme, r#"num1 > 3 && str2 == "abc""#);

            assert_eq!(
                *filter,
                Filter::Combine(
                    CombiningOp::And,
                    vec![
                        Filter::Op(
                            Field::new("num1"),
                            FilterOp::Ordering(OrderingOp::GreaterThan, RhsValue::Unsigned(3)),
                        ),
                        Filter::Op(
                            Field::new("str2"),
                            FilterOp::Ordering(
                                OrderingOp::Equal,
                                RhsValue::Bytes("abc".to_owned().into()),
                            ),
                        ),
                    ]
                )
            );

            wirefilter_free_parsing_result(parsing_result);
        }

        wirefilter_free_scheme(Box::into_raw(scheme));
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

            wirefilter_free_execution_context(Box::into_raw(exec_context));
        }

        wirefilter_free_scheme(Box::into_raw(scheme));
    }

    #[test]
    fn filter_hash() {
        let scheme = create_scheme();

        {
            let (filter1, parsing_result1) = create_filter(
                &scheme,
                r#"num1 > 41 && num2 == 1337 && ip1 != 192.168.0.1 && str2 ~ "yo\d+""#,
            );
            let (filter2, parsing_result2) = create_filter(
                &scheme,
                r#"num1 >     41 && num2 == 1337 &&    ip1 != 192.168.0.1 and str2 ~ "yo\d+""#,
            );
            let (filter3, parsing_result3) = create_filter(&scheme, r#"num1 > 41 && num2 == 1337"#);

            let hash1 = wirefilter_get_filter_hash(&filter1);
            let hash2 = wirefilter_get_filter_hash(&filter2);
            let hash3 = wirefilter_get_filter_hash(&filter3);

            assert_eq!(hash1, hash2);
            assert_ne!(hash2, hash3);

            wirefilter_free_parsing_result(parsing_result1);
            wirefilter_free_parsing_result(parsing_result2);
            wirefilter_free_parsing_result(parsing_result3);
        }

        wirefilter_free_scheme(Box::into_raw(scheme));
    }

    #[test]
    fn get_version() {
        let version = wirefilter_get_version();
        let re = Regex::new(r"\d+\.\d+\.\d+").unwrap();

        assert!(re.is_match(version.as_str()));
    }
}
