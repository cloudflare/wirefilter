extern crate wirefilter;

#[macro_use]
extern crate nom;

use std::borrow::Cow;
use std::net::Ipv4Addr;
use wirefilter::*;

macro_rules! assert_ok {
    ($expr:expr, $out:expr, $rest:expr) => {
        assert_eq!(Parse::parse($expr), Ok(($rest, $out)));
    };
}

macro_rules! assert_err {
    (@error $code: ident, $rest: expr) => {
        error_position!(nom::LexErrorKind::$code, $rest)
    };

    (@error $code: ident, $rest: expr, $($tt:tt)+) => {
        error_node_position!(nom::LexErrorKind::$code, $rest, assert_err!(@error $($tt)+))
    };

    ($expr:expr, $($tt:tt)+) => {
        assert_eq!($expr, Err(nom::Err::Error(assert_err!(@error $($tt)+))));
    };
}

macro_rules! assert_incomplete {
    ($expr: expr) => {
        assert_eq!($expr, Err(nom::Err::Incomplete(nom::Needed::Unknown)));
    };

    ($expr: expr, $size: expr) => {
        assert_eq!($expr, Err(nom::Err::Incomplete(nom::Needed::Size($size))));
    };
}

#[test]
fn test_comparison_operator() {
    assert_ok!("~1", ComparisonOp::Matches, "1");
    assert_ok!(">=2", ComparisonOp::GreaterThanEqual, "2");
    assert_ok!("<2", ComparisonOp::LessThan, "2");
    assert_ok!("matches x", ComparisonOp::Matches, " x");
    assert_ok!("containst", ComparisonOp::Contains, "t");
    assert_err!(ComparisonOp::parse("xyz"), Alt, "xyz");
    assert_incomplete!(ComparisonOp::parse("cont"), 8);
}

#[test]
fn test_ipv4() {
    assert_ok!("12.34.56.78;", Ipv4Addr::new(12, 34, 56, 78), ";");
    assert_err!(Ipv4Addr::parse("12.34.56.789"), MapRes, "789");
}

#[test]
fn test_value() {
    assert_ok!("0x7F;", Value::Unsigned(127), ";");
    assert_ok!("127;", Value::Unsigned(127), ";");
    assert_ok!(
        "127.0.0.1;",
        Value::Ipv4Addr(Ipv4Addr::new(127, 0, 0, 1)),
        ";"
    );
    assert_ok!("abc.def;", Value::Field(Field("abc.def")), ";");
    assert_ok!(
        "12:34:56:78:90:ab;",
        Value::EthernetAddr(EthernetAddr([0x12, 0x34, 0x56, 0x78, 0x90, 0xab])),
        ";"
    );
    assert_ok!("\"xyz\";", Value::String(Cow::Borrowed("xyz")), ";");
    assert_ok!(
        "abc.def[12:34];",
        Value::Substring(
            Box::new(Value::Field(Field("abc.def"))),
            vec![
                Range {
                    from: 12,
                    to: Some(46),
                },
            ]
        ),
        ";"
    );
    assert_ok!(
        "\"test\"[10,12];",
        Value::Substring(
            Box::new(Value::String(Cow::Borrowed("test"))),
            vec![
                Range {
                    from: 10,
                    to: Some(11),
                },
                Range {
                    from: 12,
                    to: Some(13),
                },
            ]
        ),
        ";"
    );
}
