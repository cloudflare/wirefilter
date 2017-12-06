#[macro_use]
extern crate quick_error;

extern crate cidr;

quick_error! {
    #[derive(Debug)]
    pub enum ErrorKind {
        Name(name: &'static str) {
            description(name)
            display("expected {}", name)
        }
        Take(count: usize) {
            description("more characters")
            display("expected {} characters", count)
        }
        Literal(s: &'static str) {
            description(s)
            display("expected literal {:?}", s)
        }
        Enum(name: &'static str, variants: &'static [&'static str]) {
            description(name)
            display("expected {} starting with one of {:?}", name, variants)
        }
        ParseInt(err: ::std::num::ParseIntError, radix: u32) {
            cause(err)
            description("integer")
            display("expected a valid integer in radix {}", radix)
        }
        ParseIp(err: ::cidr::NetworkParseError) {
            cause(err)
            description("network")
            display("expected a valid IP network")
        }
        CharacterEscape {
            description("character escape")
            display("expected \", xHH or OOO after \\")
        }
        EndingQuote {
            description("ending quote")
            display("expected to find an ending quote")
        }
        CountMismatch(name: &'static str, actual: usize, expected: usize) {
            description("different count of items")
            display("expected {} {} items, but found {}", expected, name, actual)
        }
        UnknownField {
            description("registered field")
            display("unknown field")
        }
        Incomparable(lhs: Type, op: ComparisonOp, rhs: Type) {
            description("comparable types")
            display("cannot compare {:?} and {:?} with operator {:?}", lhs, rhs, op)
        }
    }
}

pub type LexError<'a> = (ErrorKind, &'a str);

pub type LexResult<'a, T> = Result<(T, &'a str), LexError<'a>>;

pub trait Lex<'a>: Sized {
    fn lex(input: &'a str) -> LexResult<'a, Self>;
}

#[macro_use]
mod utils;

mod context;
mod bytes;
mod field;
mod ip_addr;
mod number;
mod op;
mod string;

pub use self::field::Field;
pub use self::op::{CombiningOp, ComparisonOp, UnaryOp};
pub use context::Context;
pub use context::execution::ExecutionContext;

use cidr::IpCidr;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    IpAddr,
    Bytes,
    Unsigned,
    String,
}

nested_enum!(#[derive(Debug, Clone)] RhsValue {
    IpCidr(IpCidr),
    Bytes(Vec<u8>),
    Unsigned(u64),
    String(String),
});

impl RhsValue {
    pub fn get_type(&self) -> Type {
        match *self {
            RhsValue::IpCidr(_) => Type::IpAddr,
            RhsValue::Bytes(_) => Type::Bytes,
            RhsValue::Unsigned(_) => Type::Unsigned,
            RhsValue::String(_) => Type::String,
        }
    }
}

pub fn simple_filter<'a, C: Context<'a>>(input: &'a str, context: C) -> LexResult<'a, C::Filter> {
    let (field, rest) = Field::lex(input)?;

    let rest = utils::skip_spaces(rest);

    let lhs = context
        .get_field(field.path)
        .ok_or_else(|| (ErrorKind::UnknownField, field.path))?;

    let (op, rest) = ComparisonOp::lex(rest)?;

    let rest = utils::skip_spaces(rest);

    let (rhs, rest) = RhsValue::lex(rest)?;

    let rhs_type = rhs.get_type();

    let filter = context.compare(lhs, op, rhs).map_err(|lhs_type| {
        (
            ErrorKind::Incomparable(lhs_type, op, rhs_type),
            utils::span(input, rest),
        )
    })?;

    let rest = utils::skip_spaces(rest);

    Ok((filter, rest))
}
