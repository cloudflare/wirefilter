#[macro_use]
extern crate nom;

use nom::*;
use std::str::FromStr;
use std::borrow::Cow;
use std::net::Ipv4Addr;

pub trait Parse<'a>: Sized {
    fn parse(input: &'a str) -> IResult<&str, Self>;
}

fn parse<'a, T: Parse<'a>>(input: &'a str) -> IResult<&str, T> {
    Parse::parse(input)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ComparisonOp {
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

impl<'a> Parse<'a> for ComparisonOp {
    named!(parse(&str) -> Self, alt!(
        value!(ComparisonOp::Equal, alt!(tag!("==") | tag!("eq"))) |
        value!(ComparisonOp::NotEqual, alt!(tag!("!=") | tag!("ne"))) |
        value!(ComparisonOp::GreaterThanEqual, alt!(tag!(">=") | tag!("ge"))) |
        value!(ComparisonOp::LessThanEqual, alt!(tag!("<=") | tag!("le"))) |
        value!(ComparisonOp::GreaterThan, alt!(tag!(">") | tag!("gt"))) |
        value!(ComparisonOp::LessThan, alt!(tag!("<") | tag!("lt"))) |
        value!(ComparisonOp::Matches, alt!(tag!("~") | tag!("matches"))) |
        value!(ComparisonOp::BitwiseAnd, alt!(tag!("&") | tag!("bitwise_and"))) |
        value!(ComparisonOp::Contains, tag!("contains"))
    ));
}

impl<'a> Parse<'a> for u64 {
    named!(parse(&str) -> Self, alt!(
        preceded!(tag!("0x"), map_res!(hex_digit, |digits| u64::from_str_radix(digits, 16))) |
        preceded!(tag!("0"), map_res!(oct_digit, |digits| u64::from_str_radix(digits, 8))) |
        map_res!(digit, u64::from_str)
    ));
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Field<'a>(pub &'a str);

impl<'a> Parse<'a> for Field<'a> {
    named!(
        parse(&'a str) -> Self,
        map!(
            recognize!(separated_nonempty_list!(char!('.'), alpha)),
            Field
        )
    );
}

named!(ethernet_separator(&str) -> char, one_of!(":.-"));

named!(hex_byte(&str) -> u8, map_res!(take!(2), |digits| u8::from_str_radix(digits, 16)));

named!(hex_byte_pair(&str) -> [u8; 2], do_parse!(
    b1: hex_byte >>
    opt!(ethernet_separator) >>
    b2: hex_byte >>
    ([b1, b2])
));

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EthernetAddr(pub [u8; 6]);

impl<'a> Parse<'a> for EthernetAddr {
    named!(parse(&str) -> Self, do_parse!(
        w1: hex_byte_pair >>
        ethernet_separator >>
        w2: hex_byte_pair >>
        ethernet_separator >>
        w3: hex_byte_pair >>
        (EthernetAddr([w1[0], w1[1], w2[0], w2[1], w3[0], w3[1]]))
    ));
}

named!(dec_byte(&str) -> u8, map_res!(digit, u8::from_str));

impl<'a> Parse<'a> for Ipv4Addr {
    named!(parse(&str) -> Self, do_parse!(
        b1: dec_byte >>
        char!('.') >>
        b2: dec_byte >>
        char!('.') >>
        b3: dec_byte >>
        char!('.') >>
        b4: dec_byte >>
        (Ipv4Addr::new(b1, b2, b3, b4))
    ));
}

named!(oct_byte(&str) -> u8, map_res!(take!(3), |digits| u8::from_str_radix(digits, 8)));

impl<'a> Parse<'a> for Cow<'a, str> {
    named!(
        parse(&'a str) -> Self,
        do_parse!(
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
        )
    );
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Range {
    pub from: isize,
    pub to: Option<isize>,
}

named!(index(&str) -> isize, map_res!(digit, isize::from_str));

impl<'a> Parse<'a> for Range {
    named!(parse(&str) -> Self, alt!(
        map!(separated_pair!(index, char!(':'), opt!(index)), |(start, len)| Range {
            from: start,
            to: len.map(|len| start + len)
        }) |
        map!(separated_pair!(index, char!('-'), index), |(start, end)| Range {
            from: start,
            to: Some(end + 1)
        }) |
        map!(preceded!(char!(':'), index), |end| Range {
            from: 0,
            to: Some(end)
        }) |
        map!(index, |index| Range {
            from: index,
            to: Some(index + 1)
        })
    ));
}

pub type Ranges = Vec<Range>;

impl<'a> Parse<'a> for Ranges {
    named!(parse(&str) -> Self, delimited!(
        char!('['),
        separated_nonempty_list!(char!(','), parse),
        char!(']')
    ));
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Value<'a> {
    Unsigned(u64),
    String(Cow<'a, str>),
    Field(Field<'a>),
    EthernetAddr(EthernetAddr),
    Ipv4Addr(Ipv4Addr),
    Substring(Box<Value<'a>>, Ranges),
}

named!(simple_value(&str) -> Value, alt!(
    map!(parse, Value::Ipv4Addr) |
    map!(parse, Value::EthernetAddr) |
    map!(parse, Value::Unsigned) |
    map!(parse, Value::String) |
    map!(parse, Value::Field)
));

impl<'a> Parse<'a> for Value<'a> {
    named!(
        parse(&'a str) -> Self,
        do_parse!(
            first: simple_value >>
            result: fold_many0!(
                parse,
                first,
                |acc, ranges| Value::Substring(Box::new(acc), ranges)
            ) >>
            (result)
        )
    );
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CombiningOp {
    And,
    Or,
    Xor,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Filter<'a> {
    Check(Field<'a>),
    Compare(Value<'a>, ComparisonOp, Value<'a>),
    Not(Box<Filter<'a>>),
    Combine(Box<Filter<'a>>, CombiningOp, Box<Filter<'a>>),
    In(Value<'a>, Vec<Value<'a>>),
}

named!(simple_filter(&str) -> Filter, ws!(alt!(
    delimited!(char!('+'), map!(parse, Filter::Check), char!('+')) |
    preceded!(
        alt!(tag!("!") | tag!("not")),
        map!(simple_filter, |inner| Filter::Not(Box::new(inner)))
    ) |
    do_parse!(
        first: parse >>
        res: alt!(
            do_parse!(
                op: parse >>
                second: parse >>
                (Filter::Compare(
                    /* https://github.com/Geal/nom/issues/626 */ Clone::clone(&first),
                    op,
                    second
                ))
            ) |
            do_parse!(
                tag!("in") >>
                char!('{') >>
                values: many1!(parse) >>
                char!('}') >>
                (Filter::In(first, values))
            )
        ) >>
        (res)
    ) |
    delimited!(char!('('), parse, char!(')'))
)));

named!(filter_and(&str) -> Filter, do_parse!(
    first: simple_filter >>
    res: fold_many0!(ws!(preceded!(
        alt!(tag!("&&") | tag!("and")),
        simple_filter
    )), first, |acc, second| Filter::Combine(Box::new(acc), CombiningOp::And, Box::new(second))) >>
    (res)
));

named!(filter_xor(&str) -> Filter, do_parse!(
    first: filter_and >>
    res: fold_many0!(ws!(preceded!(
        alt!(tag!("^^") | tag!("xor")),
        filter_and
    )), first, |acc, second| Filter::Combine(Box::new(acc), CombiningOp::Xor, Box::new(second))) >>
    (res)
));

named!(filter_or(&str) -> Filter, do_parse!(
    first: filter_xor >>
    res: fold_many0!(ws!(preceded!(
        alt!(tag!("||") | tag!("or")),
        filter_xor
    )), first, |acc, second| Filter::Combine(Box::new(acc), CombiningOp::Or, Box::new(second))) >>
    (res)
));

impl<'a> Parse<'a> for Filter<'a> {
    fn parse(input: &'a str) -> IResult<&str, Self> {
        filter_or(input)
    }
}
