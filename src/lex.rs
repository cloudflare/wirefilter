use cidr::NetworkParseError;
use op::ComparisonOp;
use regex::Error as RegexError;
use types::Type;

use std::num::ParseIntError;

#[derive(Debug, PartialEq, Fail)]
pub enum LexErrorKind {
    #[fail(display = "expected {}", _0)]
    ExpectedName(&'static str),

    #[fail(display = "expected literal {:?}", _0)]
    ExpectedLiteral(&'static str),

    #[fail(display = "{} while parsing with radix {}", err, radix)]
    ParseInt {
        #[cause]
        err: ParseIntError,
        radix: u32,
    },

    #[fail(display = "{}", _0)]
    ParseNetwork(
        #[cause]
        NetworkParseError,
    ),

    #[fail(display = "{}", _0)]
    ParseRegex(
        #[cause]
        RegexError,
    ),

    #[fail(display = "expected \", xHH or OOO after \\")]
    InvalidCharacterEscape,

    #[fail(display = "could not find an ending quote")]
    MissingEndingQuote,

    #[fail(display = "expected {} {}s, but found {}", expected, name, actual)]
    CountMismatch {
        name: &'static str,
        actual: usize,
        expected: usize,
    },

    #[fail(display = "unknown field")]
    UnknownField,

    #[fail(display = "cannot use operation {:?} on type {:?}", op, lhs)]
    UnsupportedOp { lhs: Type, op: ComparisonOp },

    #[fail(display = "unrecognised input")]
    EOF,
}

pub type LexError<'i> = (LexErrorKind, &'i str);

pub type LexResult<'i, T> = Result<(T, &'i str), LexError<'i>>;

pub trait Lex<'i>: Sized {
    fn lex(input: &'i str) -> LexResult<'i, Self>;
}

pub fn expect<'i>(input: &'i str, s: &'static str) -> Result<&'i str, LexError<'i>> {
    if input.starts_with(s) {
        Ok(&input[s.len()..])
    } else {
        Err((LexErrorKind::ExpectedLiteral(s), input))
    }
}

macro_rules! lex_enum {
    (@decl $preamble:tt $name:ident $input:ident { $($decl:tt)* } { $($expr:tt)* } {
        $ty:ty => $item:ident,
        $($rest:tt)*
    }) => {
        lex_enum!(@decl $preamble $name $input {
            $($decl)*
            $item($ty),
        } {
            $($expr)*
            if let Ok((res, $input)) = $crate::lex::Lex::lex($input) {
                return Ok(($name::$item(res), $input));
            }
        } { $($rest)* });
    };

    (@decl $preamble:tt $name:ident $input:ident { $($decl:tt)* } { $($expr:tt)* } {
        $($s:tt)|+ => $item:ident $(= $value:expr)*,
        $($rest:tt)*
    }) => {
        lex_enum!(@decl $preamble $name $input {
            $($decl)*
            $item $(= $value)*,
        } {
            $($expr)*
            $(if let Ok($input) = $crate::lex::expect($input, $s) {
                return Ok(($name::$item, $input));
            })+
        } { $($rest)* });
    };

    (@decl { $($preamble:tt)* } $name:ident $input:ident $decl:tt { $($expr:stmt)* } {}) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
        $($preamble)*
        pub enum $name $decl

        impl<'i> $crate::lex::Lex<'i> for $name {
            fn lex($input: &'i str) -> $crate::lex::LexResult<Self> {
                $($expr)*
                Err((
                    $crate::lex::LexErrorKind::ExpectedName(stringify!($name)),
                    $input
                ))
            }
        }
    };

    ($(# $attrs:tt)* $name:ident $items:tt) => {
        lex_enum!(@decl {
            $(# $attrs)*
        } $name input {} {} $items);
    };
}

pub fn span<'i>(input: &'i str, rest: &'i str) -> &'i str {
    &input[..input.len() - rest.len()]
}

pub fn take_while<'i, F: Fn(char) -> bool>(
    input: &'i str,
    name: &'static str,
    f: F,
) -> LexResult<'i, &'i str> {
    let mut iter = input.chars();
    loop {
        let rest = iter.as_str();
        match iter.next() {
            Some(c) if f(c) => {}
            _ => {
                return if rest.len() != input.len() {
                    Ok((span(input, rest), rest))
                } else {
                    Err((LexErrorKind::ExpectedName(name), input))
                };
            }
        }
    }
}

pub fn take(input: &str, expected: usize) -> LexResult<&str> {
    if input.len() >= expected {
        Ok(input.split_at(expected))
    } else {
        Err((
            LexErrorKind::CountMismatch {
                name: "character",
                actual: input.len(),
                expected,
            },
            input,
        ))
    }
}

fn fixed_byte(input: &str, digits: usize, radix: u32) -> LexResult<u8> {
    let (digits, rest) = take(input, digits)?;
    match u8::from_str_radix(digits, radix) {
        Ok(b) => Ok((b, rest)),
        Err(err) => Err((LexErrorKind::ParseInt { err, radix }, digits)),
    }
}

pub fn hex_byte(input: &str) -> LexResult<u8> {
    fixed_byte(input, 2, 16)
}

pub fn oct_byte(input: &str) -> LexResult<u8> {
    fixed_byte(input, 3, 8)
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
