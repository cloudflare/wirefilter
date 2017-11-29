extern crate wirefilter;

#[macro_use]
extern crate nom;

use std::borrow::Cow;
use wirefilter::*;

macro_rules! assert_ok {
    ($expr:expr, $out:expr, $rest:expr) => {
        assert_eq!($expr, nom::IResult::Done($rest, $out));
    };
}

macro_rules! assert_err {
    (@error $code: ident, $rest: expr) => {
        error_position!(nom::ErrorKind::$code, $rest)
    };

    (@error $code: ident, $rest: expr, $($tt:tt)+) => {
        error_node_position!(nom::ErrorKind::$code, $rest, assert_err!(@error $($tt)+))
    };

    ($expr:expr, $($tt:tt)+) => {
        assert_eq!($expr, nom::IResult::Error(assert_err!(@error $($tt)+)));
    };
}

macro_rules! assert_incomplete {
    ($expr: expr) => {
        assert_eq!($expr, nom::IResult::Incomplete(nom::Needed::Unknown));
    };

    ($expr: expr, $size: expr) => {
        assert_eq!($expr, nom::IResult::Incomplete(nom::Needed::Size($size)));
    };
}

#[test]
fn test_unsigned() {
    assert_ok!(parse_unsigned("0x1f5+"), 501, "+");
    assert_ok!(parse_unsigned("0123;"), 83, ";");
    assert_ok!(parse_unsigned("78!"), 78, "!");
    assert_ok!(parse_unsigned("0xefg"), 239, "g");
}

#[test]
fn test_operator() {
    assert_ok!(parse_operator("~1"), Operator::Matches, "1");
    assert_ok!(parse_operator(">=2"), Operator::GreaterThanEqual, "2");
    assert_ok!(parse_operator("<2"), Operator::LessThan, "2");
    assert_ok!(parse_operator("matches x"), Operator::Matches, " x");
    assert_ok!(parse_operator("containst"), Operator::Contains, "t");
    assert_err!(parse_operator("xyz"), Alt, "xyz");
    assert_incomplete!(parse_operator("cont"), 8);
}

#[test]
fn test_path() {
    assert_ok!(
        parse_path("xyz1"),
        "xyz",
        "1"
    );
    assert_ok!(
        parse_path("containst;"),
        "containst",
        ";"
    );
    assert_ok!(parse_path("xyz.abc1"), "xyz.abc", "1");
    assert_ok!(parse_path("xyz.;"), "xyz", ".;");
    assert_err!(parse_path("."), Alpha, ".");
    assert_err!(parse_path("123"), Alpha, "123");
}

#[test]
fn test_ethernet_addr() {
    assert_ok!(
        parse_ethernet_addr("12:34:56:78:90:abc"),
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab],
        "c"
    );
    assert_ok!(
        parse_ethernet_addr("12.34.56.78.90.abc"),
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab],
        "c"
    );
    assert_ok!(
        parse_ethernet_addr("12.34:56.78-90abc"),
        [0x12, 0x34, 0x56, 0x78, 0x90, 0xab],
        "c"
    );
    assert_err!(parse_ethernet_addr("12:34:56:7g:90:ab"), MapRes, "7g:90:ab");
    assert_err!(
        parse_ethernet_addr("12:34f:56:78:90:ab"),
        OneOf,
        "f:56:78:90:ab"
    );
}

#[test]
fn test_ipv4() {
    assert_ok!(parse_ipv4("12.34.56.78;"), [12, 34, 56, 78], ";");
    assert_err!(parse_ipv4("12.34.56.789"), MapRes, "789");
}

#[test]
fn test_string() {
    assert_ok!(
        parse_string(r#""hello, world";"#),
        Cow::Borrowed("hello, world"),
        ";"
    );
    assert_ok!(
        parse_string(r#""esca\x0a\ped\042";"#),
        Cow::Owned(String::from("esca\nped\"")),
        ";"
    );
    assert_incomplete!(parse_string("\"hello"), 7);
}
