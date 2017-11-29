extern crate wirefilter;

#[macro_use]
extern crate nom;

use std::borrow::Cow;
use std::net::Ipv4Addr;
use wirefilter::*;

macro_rules! assert_ok {
    ($expr:expr, $out:expr, $rest:expr) => {
        assert_eq!(Parse::parse($expr), nom::IResult::Done($rest, $out));
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
    assert_ok!("0x1f5+", 501u64, "+");
    assert_ok!("0123;", 83u64, ";");
    assert_ok!("78!", 78u64, "!");
    assert_ok!("0xefg", 239u64, "g");
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
fn test_field() {
    assert_ok!("xyz1", Field("xyz"), "1");
    assert_ok!("containst;", Field("containst"), ";");
    assert_ok!("xyz.abc1", Field("xyz.abc"), "1");
    assert_ok!("xyz.;", Field("xyz"), ".;");
    assert_err!(Field::parse("."), Alpha, ".");
    assert_err!(Field::parse("123"), Alpha, "123");
}

#[test]
fn test_ethernet_addr() {
    assert_ok!(
        "12:34:56:78:90:abc",
        EthernetAddr([0x12, 0x34, 0x56, 0x78, 0x90, 0xab]),
        "c"
    );
    assert_ok!(
        "12.34.56.78.90.abc",
        EthernetAddr([0x12, 0x34, 0x56, 0x78, 0x90, 0xab]),
        "c"
    );
    assert_ok!(
        "12.34:56.78-90abc",
        EthernetAddr([0x12, 0x34, 0x56, 0x78, 0x90, 0xab]),
        "c"
    );
    assert_err!(EthernetAddr::parse("12:34:56:7g:90:ab"), MapRes, "7g:90:ab");
    assert_err!(
        EthernetAddr::parse("12:34f:56:78:90:ab"),
        OneOf,
        "f:56:78:90:ab"
    );
}

#[test]
fn test_ipv4() {
    assert_ok!("12.34.56.78;", Ipv4Addr::new(12, 34, 56, 78), ";");
    assert_err!(Ipv4Addr::parse("12.34.56.789"), MapRes, "789");
}

#[test]
fn test_string() {
    assert_ok!(r#""hello, world";"#, Cow::Borrowed("hello, world"), ";");
    assert_ok!(
        r#""esca\x0a\ped\042";"#,
        Cow::Owned(String::from("esca\nped\"")),
        ";"
    );
    assert_incomplete!(Cow::parse("\"hello"), 7);
}

#[test]
fn test_substring() {
    assert_ok!(
        "[1];",
        vec![
            Range {
                from: 1,
                to: Some(2),
            },
        ],
        ";"
    );
    assert_ok!(
        "[0:3];",
        vec![
            Range {
                from: 0,
                to: Some(3),
            },
        ],
        ";"
    );
    assert_ok!(
        "[1,:2,3-4,7:,9:10];",
        vec![
            Range {
                from: 1,
                to: Some(2),
            },
            Range {
                from: 0,
                to: Some(2),
            },
            Range {
                from: 3,
                to: Some(5),
            },
            Range { from: 7, to: None },
            Range {
                from: 9,
                to: Some(19),
            },
        ],
        ";"
    );
    assert_err!(Ranges::parse("[1-]"), Char, "-]");
    assert_err!(Ranges::parse("[-9]"), Alt, "-9]");
    assert_err!(Ranges::parse("[:]"), Alt, ":]");
    assert_err!(Ranges::parse("[-]"), Alt, "-]");
    assert_err!(Ranges::parse("[]"), Alt, "]");
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
        "\"test\"[10,12][20:];",
        Value::Substring(
            Box::new(Value::Substring(
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
            )),
            vec![Range { from: 20, to: None }]
        ),
        ";"
    );
}

#[test]
fn test_filter() {
    assert_ok!(
        "http.host contains \"t\"",
        Filter::Compare(
            Value::Field(Field("http.host")),
            ComparisonOp::Contains,
            Value::String(Cow::Borrowed("t"))
        ),
        ""
    );
    assert_ok!(
        "port in { 80 443 };",
        Filter::In(
            Value::Field(Field("port")),
            vec![Value::Unsigned(80), Value::Unsigned(443)]
        ),
        ";"
    );
    assert_ok!(
        "not +x+ and (y == 1) or z in { 10 };",
        Filter::Combine(
            Box::new(Filter::Combine(
                Box::new(Filter::Not(Box::new(Filter::Check(Field("x"))))),
                CombiningOp::And,
                Box::new(Filter::Compare(
                    Value::Field(Field("y")),
                    ComparisonOp::Equal,
                    Value::Unsigned(1)
                ))
            )),
            CombiningOp::Or,
            Box::new(Filter::In(
                Value::Field(Field("z")),
                vec![Value::Unsigned(10)]
            ))
        ),
        ";"
    );
}
