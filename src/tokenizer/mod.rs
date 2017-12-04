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
        ParseIpAddr(err: ::std::net::AddrParseError) {
            cause(err)
            description("address")
            display("expected a valid IP address")
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
            description("count mismatch")
            display("expected {} {} items, but found {}", expected, name, actual)
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
mod ip_addr;
mod number;
mod op;
mod spaces;
mod string;

pub use self::field::Field;
pub use self::op::ComparisonOp;
pub use self::spaces::Spaces;

nested_enum!(Value<'a> {
	IpAddr(::std::net::IpAddr),
	Bytes(Vec<u8>),
	Unsigned(u64),
	Field(Field<'a>),
	String(String),
});

nested_enum!(Token<'a> {
	Spaces(Spaces),
	ComparisonOp(ComparisonOp),
	Value(Value<'a>),
});
