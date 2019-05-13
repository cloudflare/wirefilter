use crate::{
    rhs_types::RegexError,
    scheme::{IndexAccessError, UnknownFieldError, UnknownFunctionError},
    types::{Type, TypeMismatchError},
};
use cidr::NetworkParseError;
use failure::Fail;
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
    ParseNetwork(#[cause] NetworkParseError),

    #[fail(display = "{}", _0)]
    ParseRegex(#[cause] RegexError),

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

    #[fail(display = "{}", _0)]
    UnknownField(#[cause] UnknownFieldError),

    #[fail(display = "{}", _0)]
    UnknownFunction(#[cause] UnknownFunctionError),

    #[fail(display = "cannot use this operation type {:?}", lhs_type)]
    UnsupportedOp { lhs_type: Type },

    #[fail(display = "incompatible range bounds")]
    IncompatibleRangeBounds,

    #[fail(display = "unrecognised input")]
    EOF,

    #[fail(display = "invalid number of arguments")]
    InvalidArgumentsCount {
        expected_min: usize,
        expected_max: usize,
    },

    #[fail(display = "invalid type of argument #{}: {}", index, mismatch)]
    InvalidArgumentType {
        index: usize,
        #[cause]
        mismatch: TypeMismatchError,
    },

    #[fail(display = "{}", _0)]
    InvalidIndexAccess(#[cause] IndexAccessError),
}

pub type LexError<'i> = (LexErrorKind, &'i str);

pub type LexResult<'i, T> = Result<(T, &'i str), LexError<'i>>;

pub trait Lex<'i>: Sized {
    fn lex(input: &'i str) -> LexResult<'i, Self>;
}

pub trait LexWith<'i, E>: Sized {
    fn lex_with(input: &'i str, extra: E) -> LexResult<'i, Self>;
}

impl<'i, T: Lex<'i>, E> LexWith<'i, E> for T {
    fn lex_with(input: &'i str, _extra: E) -> LexResult<'i, Self> {
        Self::lex(input)
    }
}

pub fn expect<'i>(input: &'i str, s: &'static str) -> Result<&'i str, LexError<'i>> {
    if input.starts_with(s) {
        Ok(&input[s.len()..])
    } else {
        Err((LexErrorKind::ExpectedLiteral(s), input))
    }
}

// Tabs are harder to format as part of the error message because they have
// a different printable width than other characters, and so become a common
// source of issues in different compilers.
//
// It's not impossible to work around that limitation, but let's not bother
// for now until someone really needs them (tabs vs spaces all the way down...).
const SPACE_CHARS: &[char] = &[' ', '\r', '\n'];

pub fn skip_space(input: &str) -> &str {
    input.trim_start_matches(SPACE_CHARS)
}

/// This macro generates enum declaration + lexer implementation.
///
/// It works by recursively processing variants one by one, while passing
/// around intermediate state (partial declaration and lexer bodies).
macro_rules! lex_enum {
    // Branch for handling `SomeType => VariantName`.
    //
    // Creates a newtype variant `VariantName(SomeType)`.
    //
    // On the parser side, tries to parse `SomeType` and wraps into the variant
    // on success.
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

    // Branch for handling `"some_string" | "other_string" => VariantName`.
    // (also supports optional constant value via `... => VariantName = 42`)
    //
    // Creates a unit variant `VariantName`.
    //
    // On the parser side, tries to parse either of the given string values,
    // and returns the variant if any of them succeeded.
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

    // Internal finish point for declaration + lexer generation.
    //
    // This is invoked when no more variants are left to process.
    // At this point declaration and lexer body are considered complete.
    (@decl { $($preamble:tt)* } $name:ident $input:ident $decl:tt { $($expr:stmt)* } {}) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize)]
        $($preamble)*
        pub enum $name $decl

        impl<'i> $crate::lex::Lex<'i> for $name {
            fn lex($input: &'i str) -> $crate::lex::LexResult<'_, Self> {
                $($expr)*
                Err((
                    $crate::lex::LexErrorKind::ExpectedName(stringify!($name)),
                    $input
                ))
            }
        }
    };

    // The public entry point to the macro.
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

pub fn take(input: &str, expected: usize) -> LexResult<'_, &str> {
    let mut chars = input.chars();
    for i in 0..expected {
        chars.next().ok_or_else(|| {
            (
                LexErrorKind::CountMismatch {
                    name: "character",
                    actual: i,
                    expected,
                },
                input,
            )
        })?;
    }
    let rest = chars.as_str();
    Ok((span(input, rest), rest))
}

pub fn complete<T>(res: LexResult<'_, T>) -> Result<T, LexError<'_>> {
    let (res, input) = res?;
    if input.is_empty() {
        Ok(res)
    } else {
        Err((LexErrorKind::EOF, input))
    }
}

#[cfg(test)]
macro_rules! assert_ok {
    ($s:expr, $res:expr, $rest:expr) => {{
        let expr = $s.unwrap();
        assert_eq!(expr, ($res, $rest));
        expr.0
    }};

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

#[cfg(test)]
macro_rules! assert_json {
    ($expr:expr, $json:tt) => {
        assert_eq!(
            ::serde_json::to_value(&$expr).unwrap(),
            ::serde_json::json!($json)
        );
    };
}
