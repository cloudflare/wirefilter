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
        Incomparable(lhs: context::Type, op: op::ComparisonOp, rhs: context::Type) {
            description("comparable types")
            display("cannot compare {:?} and {:?} with operator {:?}", lhs, rhs, op)
        }
        EOF {
            description("end of input")
            display("unrecognised input")
        }
    }
}

#[cfg(test)]
macro_rules! assert_ok {
    ($s:expr, $res:expr, $rest:expr) => {
        assert_eq!($s, Ok(($res, $rest)))
    };

    ($s:expr, $res:expr) => {
        assert_ok!($s, $res, "")
    };
}

#[cfg(test)]
macro_rules! assert_err {
    ($s:expr, $kind:expr, $span:expr) => {
        assert_eq!($s, Err(($kind, $span)))
    };
}

pub type LexError<'a> = (ErrorKind, &'a str);

pub type LexResult<'a, T> = Result<(T, &'a str), LexError<'a>>;

pub trait Lex<'a>: Sized {
    fn lex(input: &'a str) -> LexResult<'a, Self>;
}

#[macro_use]
mod utils;

pub mod context;
mod bytes;
mod field;
pub mod filter;
mod ip_addr;
mod number;
pub mod op;

pub use self::bytes::Bytes;
pub use self::field::Field;
pub use self::number::Range;
pub use filter::filter;
