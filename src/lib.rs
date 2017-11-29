#[macro_use]
extern crate nom;

use nom::*;
use std::str::FromStr;
use std::borrow::Cow;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Operator {
    Equal,
    NotEqual,
    GreaterThan,
    LessThan,
    GreaterThanEqual,
    LessThanEqual,
    Contains,
    Matches,
    BitwiseAnd,
}

named!(pub parse_unsigned(&str) -> u64, alt!(
    preceded!(tag!("0x"), map_res!(hex_digit, |digits| u64::from_str_radix(digits, 16))) |
    preceded!(tag!("0"), map_res!(oct_digit, |digits| u64::from_str_radix(digits, 8))) |
    map_res!(digit, u64::from_str)
));

named!(pub parse_operator(&str) -> Operator, alt!(
    value!(Operator::Equal, alt!(tag!("==") | tag!("eq"))) |
    value!(Operator::NotEqual, alt!(tag!("!=") | tag!("ne"))) |
    value!(Operator::GreaterThanEqual, alt!(tag!(">=") | tag!("ge"))) |
    value!(Operator::LessThanEqual, alt!(tag!("<=") | tag!("le"))) |
    value!(Operator::GreaterThan, alt!(tag!(">") | tag!("gt"))) |
    value!(Operator::LessThan, alt!(tag!("<") | tag!("lt"))) |
    value!(Operator::Matches, alt!(tag!("~") | tag!("matches"))) |
    value!(Operator::BitwiseAnd, alt!(tag!("&") | tag!("bitwise_and"))) |
    value!(Operator::Contains, tag!("contains"))
));

named!(pub parse_path(&str) -> &str, recognize!(separated_nonempty_list!(char!('.'), alpha)));

named!(ethernet_separator(&str) -> char, one_of!(":.-"));

named!(hex_byte(&str) -> u8, map_res!(take!(2), |digits| u8::from_str_radix(digits, 16)));

named!(hex_byte_pair(&str) -> [u8; 2], do_parse!(
    b1: hex_byte >>
    opt!(ethernet_separator) >>
    b2: hex_byte >>
    ([b1, b2])
));

named!(pub parse_ethernet_addr(&str) -> [u8; 6], do_parse!(
    w1: hex_byte_pair >>
    ethernet_separator >>
    w2: hex_byte_pair >>
    ethernet_separator >>
    w3: hex_byte_pair >>
    ([w1[0], w1[1], w2[0], w2[1], w3[0], w3[1]])
));

named!(dec_byte(&str) -> u8, map_res!(digit, u8::from_str));

named!(pub parse_ipv4(&str) -> [u8; 4], do_parse!(
    b1: dec_byte >>
    char!('.') >>
    b2: dec_byte >>
    char!('.') >>
    b3: dec_byte >>
    char!('.') >>
    b4: dec_byte >>
    ([b1, b2, b3, b4])
));

named!(oct_byte(&str) -> u8, map_res!(take!(3), |digits| u8::from_str_radix(digits, 8)));

named!(pub parse_string(&str) -> Cow<str>, do_parse!(
    char!('"') >>
    unprefixed: map!(is_not!("\"\\"), Cow::Borrowed) >>
    res: fold_many0!(preceded!(char!('\\'), tuple!(
        alt!(
            preceded!(char!('x'), map!(hex_byte, |b| b as char)) |
            map!(oct_byte, |b| b as char) |
            anychar
        ),
        map!(opt!(is_not!("\"\\")), Option::unwrap_or_default)
    )), unprefixed, |acc: Cow<str>, (ch, rest)| {
        let mut acc = acc.into_owned();
        acc.push(ch);
        acc.push_str(rest);
        Cow::Owned(acc)
    }) >>
    char!('"') >>
    (res)
));
