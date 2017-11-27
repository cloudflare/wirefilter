#[macro_use]
extern crate nom;

use nom::*;
use std::str::FromStr;

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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token<'a> {
    Identifier(&'a str),
    Dot,
    Operator(Operator),
    Unsigned(u64),
    EthernetAddr([u8; 6]),
}

named!(parse_unsigned(&str) -> u64, alt!(
    preceded!(tag!("0x"), map_res!(hex_digit, |digits| u64::from_str_radix(digits, 16))) |
    preceded!(tag!("0"), map_res!(oct_digit, |digits| u64::from_str_radix(digits, 8))) |
    map_res!(digit, u64::from_str)
));

named!(parse_operator(&str) -> Operator, alt!(
    value!(Operator::Equal, tag!("==")) |
    value!(Operator::NotEqual, tag!("!=")) |
    value!(Operator::GreaterThanEqual, tag!(">=")) |
    value!(Operator::LessThanEqual, tag!("<=")) |
    value!(Operator::GreaterThan, tag!(">")) |
    value!(Operator::LessThan, tag!("<")) |
    value!(Operator::Matches, tag!("~")) |
    value!(Operator::BitwiseAnd, tag!("&"))
));

named!(parse_identifier_like(&str) -> Token, switch!(alpha,
    "eq" => value!(Token::Operator(Operator::Equal)) |
    "ne" => value!(Token::Operator(Operator::NotEqual)) |
    "gt" => value!(Token::Operator(Operator::GreaterThan)) |
    "lt" => value!(Token::Operator(Operator::LessThan)) |
    "ge" => value!(Token::Operator(Operator::GreaterThanEqual)) |
    "le" => value!(Token::Operator(Operator::LessThanEqual)) |
    "contains" => value!(Token::Operator(Operator::Contains)) |
    "matches" => value!(Token::Operator(Operator::Matches)) |
    "bitwise_and" => value!(Token::Operator(Operator::BitwiseAnd)) |
    other => value!(Token::Identifier(other))
));

named!(ethernet_separator(&str) -> char, one_of!(":.-"));

named!(byte(&str) -> u8, map_res!(take!(2), |digits| u8::from_str_radix(digits, 16)));

named!(two_bytes(&str) -> [u8; 2], do_parse!(
    b1: byte >>
    opt!(ethernet_separator) >>
    b2: byte >>
    ([b1, b2])
));

named!(parse_ethernet_addr(&str) -> [u8; 6], do_parse!(
    w1: two_bytes >>
    ethernet_separator >>
    w2: two_bytes >>
    ethernet_separator >>
    w3: two_bytes >>
    ([w1[0], w1[1], w2[0], w2[1], w3[0], w3[1]])
));

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsigned() {
        assert_eq!(parse_unsigned("0x1f5+"), IResult::Done("+", 501));
        assert_eq!(parse_unsigned("0123;"), IResult::Done(";", 83));
        assert_eq!(parse_unsigned("78!"), IResult::Done("!", 78));
        assert_eq!(parse_unsigned("0xefg"), IResult::Done("g", 239));
    }

    #[test]
    fn test_operator() {
        assert_eq!(parse_operator("~1"), IResult::Done("1", Operator::Matches));
        assert_eq!(
            parse_operator(">=2"),
            IResult::Done("2", Operator::GreaterThanEqual)
        );
        assert_eq!(parse_operator("<2"), IResult::Done("2", Operator::LessThan));
        assert_eq!(
            parse_operator("xyz"),
            IResult::Error(error_position!(ErrorKind::Alt, "xyz"))
        );
    }

    #[test]
    fn test_identifier() {
        assert_eq!(
            parse_identifier_like("xyz1"),
            IResult::Done("1", Token::Identifier("xyz"))
        );
        assert_eq!(
            parse_identifier_like("containst"),
            IResult::Done("", Token::Identifier("containst"))
        );
        assert_eq!(
            parse_identifier_like("contains t"),
            IResult::Done(" t", Token::Operator(Operator::Contains))
        );
        assert_eq!(
            parse_identifier_like("123"),
            IResult::Error(error_node_position!(
                ErrorKind::Switch,
                "123",
                error_position!(ErrorKind::Alpha, "123")
            ))
        );
    }

    #[test]
    fn test_ethernet_addr() {
        assert_eq!(
            parse_ethernet_addr("12:34:56:78:90:ab"),
            IResult::Done("", [0x12, 0x34, 0x56, 0x78, 0x90, 0xab])
        );
        assert_eq!(
            parse_ethernet_addr("12.34.56.78.90.ab"),
            IResult::Done("", [0x12, 0x34, 0x56, 0x78, 0x90, 0xab])
        );
        assert_eq!(
            parse_ethernet_addr("12.34:56.78-90ab"),
            IResult::Done("", [0x12, 0x34, 0x56, 0x78, 0x90, 0xab])
        );
        assert_eq!(
            parse_ethernet_addr("12:34:56:7g:90:ab"),
            IResult::Error(error_position!(ErrorKind::MapRes, "7g:90:ab"))
        );
        assert_eq!(
            parse_ethernet_addr("12:34f:56:78:90:ab"),
            IResult::Error(error_position!(ErrorKind::OneOf, "f:56:78:90:ab"))
        );
    }
}
