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
            display("expected {} {}s, but found {}", expected, name, actual)
        }
        UnknownField {
            description("registered field")
            display("unknown field")
        }
        Incomparable(lhs: Type, op: ComparisonOp, rhs: Type) {
            description("comparable types")
            display("cannot compare {:?} and {:?} with operator {:?}", lhs, rhs, op)
        }
        EOF {
            description("end of input")
            display("unrecognised input")
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
    IpAddrV4,
    IpAddrV6,
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
            RhsValue::IpCidr(IpCidr::V4(_)) => Type::IpAddrV4,
            RhsValue::IpCidr(IpCidr::V6(_)) => Type::IpAddrV6,
            RhsValue::Bytes(_) => Type::Bytes,
            RhsValue::Unsigned(_) => Type::Unsigned,
            RhsValue::String(_) => Type::String,
        }
    }
}

fn simple_filter<'a, C: Context<'a>>(input: &'a str, context: C) -> LexResult<'a, C::Filter> {
    if let Ok(input) = utils::expect(input, "(") {
        let input = input.trim_left();
        let (res, input) = combined_filter(input, context)?;
        let input = input.trim_left();
        let input = utils::expect(input, ")")?;
        return Ok((res, input.trim_left()));
    }

    let initial_input = input;

    let (field, input) = Field::lex(input)?;

    let input = input.trim_left();

    let lhs = context
        .get_field(field.path)
        .ok_or_else(|| (ErrorKind::UnknownField, field.path))?;

    let (op, input) = ComparisonOp::lex(input)?;

    let input = input.trim_left();

    let (rhs, input) = RhsValue::lex(input)?;

    let rhs_type = rhs.get_type();

    let filter = context.compare(lhs, op, rhs).map_err(|lhs_type| {
        (
            ErrorKind::Incomparable(lhs_type, op, rhs_type),
            utils::span(initial_input, input),
        )
    })?;

    Ok((filter, input.trim_left()))
}

fn combining_op(input: &str) -> (Option<CombiningOp>, &str) {
    match CombiningOp::lex(input) {
        Ok((op, input)) => (Some(op), input.trim_left()),
        Err(_) => (None, input),
    }
}

fn filter_prec<'a, C: Context<'a>>(
    context: C,
    mut lhs: C::Filter,
    min_prec: Option<CombiningOp>,
    mut lookahead: (Option<CombiningOp>, &'a str),
) -> LexResult<'a, C::Filter> {
    while let Some(op) = lookahead.0 {
        let mut rhs = simple_filter(lookahead.1, context)?;
        loop {
            lookahead = combining_op(rhs.1);
            if lookahead.0 <= Some(op) {
                break;
            }
            rhs = filter_prec(context, rhs.0, lookahead.0, lookahead)?;
        }
        lhs = context.combine(lhs, op, rhs.0);
        if lookahead.0 < min_prec {
            // pretend we haven't seen an operator if its precedence is
            // outside of our limits
            lookahead = (None, rhs.1);
        }
    }
    Ok((lhs, lookahead.1))
}

fn combined_filter<'a, C: Context<'a>>(input: &'a str, context: C) -> LexResult<'a, C::Filter> {
    let (lhs, input) = simple_filter(input, context)?;
    let lookahead = combining_op(input);
    filter_prec(context, lhs, None, lookahead)
}

pub fn filter<'a, C: Context<'a>>(input: &'a str, context: C) -> Result<C::Filter, LexError<'a>> {
    let (res, input) = combined_filter(input, context)?;
    if input.is_empty() {
        Ok(res)
    } else {
        Err((ErrorKind::EOF, input))
    }
}
