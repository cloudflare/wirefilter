use cidr::NetworkParseError;
use op::ComparisonOp;
use regex::Error as RegexError;
use types::Type;

use std::num::ParseIntError;

quick_error! {
    #[derive(Debug, PartialEq)]
    pub enum LexErrorKind {
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
        ParseInt(err: ParseIntError, radix: u32) {
            cause(err)
            description("integer")
            display("expected a valid integer in radix {}", radix)
        }
        ParseIp(err: NetworkParseError) {
            cause(err)
            description("network")
            display("expected a valid IP network")
        }
        ParseRegex(err: RegexError) {
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
        UnsupportedOp(lhs: Type, op: ComparisonOp) {
            description("valid operation")
            display("cannot use operation {:?} on type {:?}", op, lhs)
        }
        EOF {
            description("end of input")
            display("unrecognised input")
        }
    }
}

pub type LexError<'a> = (LexErrorKind, &'a str);

pub type LexResult<'a, T> = Result<(T, &'a str), LexError<'a>>;

pub trait Lex<'a>: Sized {
    fn lex(input: &'a str) -> LexResult<'a, Self>;
}

pub fn expect<'a>(input: &'a str, s: &'static str) -> Result<&'a str, LexError<'a>> {
    if input.starts_with(s) {
        Ok(&input[s.len()..])
    } else {
        Err((LexErrorKind::Literal(s), input))
    }
}

macro_rules! simple_enum {
    ($(# $attrs:tt)* $name:ident { $( $($s:tt)|+ => $item:ident $(= $value:expr)*, )+ }) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
        $(# $attrs)*
        pub enum $name {
            $($item $(= $value)*,)+
        }

        impl<'a> $crate::lex::Lex<'a> for $name {
            fn lex(input: &'a str) -> $crate::lex::LexResult<'a, Self> {
                static EXPECTED_LITERALS: &'static [&'static str] = &[
                    $($($s),+),+
                ];

                $($(if let Ok(input) = $crate::lex::expect(input, $s) {
                    Ok(($name::$item, input))
                } else)+)+ {
                    Err((
                        $crate::lex::LexErrorKind::Enum(stringify!($name), EXPECTED_LITERALS),
                        input
                    ))
                }
            }
        }
    };
}

macro_rules! nested_enum {
    (!impl $input:ident, $name:ident :: $item:ident ($ty:ty)) => {
        nested_enum!(!impl $input, $name::$item ($ty) <- $crate::lex::Lex::lex)
    };

    (!impl $input:ident, $name:ident :: $item:ident <- $func:path) => {
        $func($input).map(|(_, input)| ($name::$item, input))
    };

    (!impl $input:ident, $name:ident :: $item:ident ( $ty:ty ) <- $func:path) => {
        $func($input).map(|(res, input)| ($name::$item(res), input))
    };

    ($(# $attrs:tt)* $name:ident { $($item:ident $(( $ty:ty ))* $(<- $func:path)*,)+ }) => {
        $(# $attrs)*
        pub enum $name {
            $($item $(($ty))*,)+
        }

        impl<'a> $crate::lex::Lex<'a> for $name {
            fn lex(input: &'a str) -> $crate::lex::LexResult<'a, Self> {
                $(match nested_enum!(!impl input, $name::$item $(($ty))* $(<- $func)*) {
                    Ok(res) => {
                        return Ok(res);
                    }
                    Err(_) => {}
                };)+
                Err(($crate::lex::LexErrorKind::Name(stringify!($name)), input))
            }
        }
    };
}

pub fn span<'a>(input: &'a str, rest: &'a str) -> &'a str {
    &input[..input.len() - rest.len()]
}

pub fn take_while<'a, F: Fn(char) -> bool>(
    input: &'a str,
    name: &'static str,
    f: F,
) -> LexResult<'a, &'a str> {
    let mut iter = input.chars();
    loop {
        let rest = iter.as_str();
        match iter.next() {
            Some(c) if f(c) => {}
            _ => {
                return if rest.len() != input.len() {
                    Ok((span(input, rest), rest))
                } else {
                    Err((LexErrorKind::CountMismatch(name, 0, 1), input))
                };
            }
        }
    }
}

pub fn take<'a>(input: &'a str, count: usize) -> LexResult<'a, &'a str> {
    if input.len() >= count {
        Ok(input.split_at(count))
    } else {
        Err((
            LexErrorKind::CountMismatch("character", input.len(), count),
            input,
        ))
    }
}

fn fixed_byte(input: &str, digits: usize, radix: u32) -> LexResult<u8> {
    let (digits, rest) = take(input, digits)?;
    match u8::from_str_radix(digits, radix) {
        Ok(b) => Ok((b, rest)),
        Err(e) => Err((LexErrorKind::ParseInt(e, radix), digits)),
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
