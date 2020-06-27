use crate::{
    functions::{FunctionArgInvalidConstantError, FunctionArgKindMismatchError},
    rhs_types::{RegexError, WildcardError},
    scheme::{IndexAccessError, UnknownFieldError, UnknownFunctionError},
    types::{Type, TypeMismatchError},
};
use cidr::errors::NetworkParseError;
use std::num::ParseIntError;
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
/// LexErrorKind occurs when there is an invalid or unexpected token.
pub enum LexErrorKind {
    /// Expected the next token to be a Field
    #[error("expected {0}")]
    ExpectedName(&'static str),

    /// Expected the next token to be a Literal
    #[error("expected literal {0:?}")]
    ExpectedLiteral(&'static str),

    /// Expected the next token to be an int
    #[error("{err} while parsing with radix {radix}")]
    ParseInt {
        /// The error that occurred parsing the token as an int
        #[source]
        err: ParseIntError,
        /// The base of the number
        radix: u32,
    },

    /// Expected the next token to be a network address such a CIDR, IPv4 or
    /// IPv6 address
    #[error("{0}")]
    ParseNetwork(#[source] NetworkParseError),

    /// Expected the next token to be a regular expression
    #[error("{0}")]
    ParseRegex(#[source] RegexError),

    /// Expected the next token to be a wildcard expression
    #[error("{0}")]
    ParseWildcard(#[source] WildcardError),

    /// Expected the next token to be an escape character
    #[error("expected \", xHH or OOO after \\")]
    InvalidCharacterEscape,

    /// Invalid raw string hash count
    #[error("invalid raw string hash count, there can't be more than 255 #s")]
    InvalidRawStringHashCount,

    /// Expected the next token to be an ending quote
    #[error("could not find an ending quote")]
    MissingEndingQuote,

    /// Expected to take some number of characters from the input but the
    /// input was too short
    #[error("expected {expected} {name}s, but found {actual}")]
    CountMismatch {
        /// This is set to "character" for all occurences of this error
        name: &'static str,
        /// The actual number of characters
        actual: usize,
        /// The expected number of characters
        expected: usize,
    },

    /// The next token refers to a Field that is not present in the Scheme
    #[error("{0}")]
    UnknownField(#[source] UnknownFieldError),

    /// The next token refers to a Function that is not present in the Scheme
    #[error("{0}")]
    UnknownFunction(#[source] UnknownFunctionError),

    /// The next token refers to an Identifier that is not present in the Scheme
    /// ie: neither as a Field or as a Function
    #[error("unknown identifier")]
    UnknownIdentifier,

    /// The operation cannot be performed on this Field
    #[error("cannot perform this operation on type {lhs_type:?}")]
    UnsupportedOp {
        /// The type of the Field
        lhs_type: Type,
    },

    /// This variant is not in use
    #[error("incompatible range bounds")]
    IncompatibleRangeBounds,

    /// End Of File
    #[error("unrecognised input")]
    EOF,

    /// Invalid number of arguments for the function
    #[error("invalid number of arguments")]
    InvalidArgumentsCount {
        /// The minimum number of arguments for the function
        expected_min: usize,
        /// The maximum number of arguments for the function or None if the
        /// function takes an unlimited number of arguments
        expected_max: Option<usize>,
    },

    /// Invalid argument kind for the function
    #[error("invalid kind of argument #{index}: {mismatch}")]
    InvalidArgumentKind {
        /// The position of the argument in the function call
        index: usize,
        /// The expected and the actual kind for the argument
        #[source]
        mismatch: FunctionArgKindMismatchError,
    },

    /// Invalid argument type for the function
    #[error("invalid type of argument #{index}: {mismatch}")]
    InvalidArgumentType {
        /// The position of the argument in the function call
        index: usize,
        /// The expected and actual type for the argument
        #[source]
        mismatch: TypeMismatchError,
    },

    /// Invalid argument value for the function
    #[error("invalid value of argument #{index}: {invalid}")]
    InvalidArgumentValue {
        /// The position of the argument in the function call
        index: usize,
        /// The error message that explains why the value is invalid
        #[source]
        invalid: FunctionArgInvalidConstantError,
    },

    /// The index is invalid
    #[error("{0}")]
    InvalidIndexAccess(#[source] IndexAccessError),

    /// Invalid type
    #[error("{0}")]
    TypeMismatch(#[source] TypeMismatchError),

    /// Invalid usage of map each access operator
    #[error("invalid use of map each access operator")]
    InvalidMapEachAccess,

    /// Invalid list name
    #[error("invalid list name {name:?}")]
    InvalidListName {
        /// Name of the list
        name: String,
    },
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
    if let Some(index) = input.strip_prefix(s) {
        Ok(index)
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
        $(#[$meta:meta])* $ty:ty => $item:ident,
        $($rest:tt)*
    }) => {
        lex_enum!(@decl $preamble $name $input {
            $($decl)*
            $(#[$meta])*
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
        $(#[$meta:meta])* $($s:literal)|+ => $item:ident $(= $value:expr)*,
        $($rest:tt)*
    }) => {
        lex_enum!(@decl $preamble $name $input {
            $($decl)*
            $(#[$meta])*
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
        #[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Serialize)]
        $($preamble)*
        pub enum $name $decl

        impl<'i> $crate::lex::Lex<'i> for $name {
            fn lex($input: &'i str) -> $crate::lex::LexResult<'i, Self> {
                $($expr)*
                Err((
                    $crate::lex::LexErrorKind::ExpectedName(stringify!($name)),
                    $input
                ))
            }
        }
    };

    // The public entry point to the macro.
    ($(#[$meta:meta])* $name:ident $items:tt) => {
        lex_enum!(@decl {
            $(#[$meta])*
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
        chars.next().ok_or({
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
    ($expr:expr, $json:tt) => {{
        let json = ::serde_json::to_value(&$expr).unwrap();
        assert_eq!(json, ::serde_json::json!($json));
        json
    }};
}
