#[macro_use]
extern crate quick_error;

#[macro_use]
extern crate bitflags;

extern crate cidr;

extern crate regex;

quick_error! {
    #[derive(Debug, PartialEq)]
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
        ParseRegex(err: ::regex::Error) {
            cause(err)
            description("regex")
            display("expected a valid regular expression")
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
        UnsupportedOp(lhs: ::types::Type, op: op::ComparisonOp) {
            description("valid operation")
            display("cannot use operation {:?} on type {:?}", op, lhs)
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

mod bytes;
mod field;
mod filter;
mod ip_addr;
mod number;
pub mod op;
pub mod types;

pub use self::bytes::Bytes;
pub use self::field::Field;
pub use self::number::Range;
pub use self::filter::{Filter, Context};
