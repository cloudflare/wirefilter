#![feature(prelude_import)]
#![no_std]
#![feature(log_syntax)]
#[prelude_import]
use std::prelude::v1::*;
#[macro_use]
extern crate std as std;

#[macro_use]
extern crate quick_error;

pub mod tokenizer {
    use std::char;
    #[allow(unknown_lints)]
    #[allow(unused_doc_comment)]
    pub enum ErrorKind {
        Take(usize),
        Literal(&'static str),
        Enum(&'static str, &'static [&'static str]),
        ParseInt(::std::num::ParseIntError, u32),
        TakeWhile(&'static str),
        CharacterEscape,
        EndingQuote,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    #[allow(unknown_lints)]
    #[allow(unused_doc_comment)]
    impl ::std::fmt::Debug for ErrorKind {
        fn fmt(&self, __arg_0: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            match (&*self,) {
                (&ErrorKind::Take(ref __self_0),) => {
                    let mut builder = __arg_0.debug_tuple("Take");
                    let _ = builder.field(&&(*__self_0));
                    builder.finish()
                }
                (&ErrorKind::Literal(ref __self_0),) => {
                    let mut builder = __arg_0.debug_tuple("Literal");
                    let _ = builder.field(&&(*__self_0));
                    builder.finish()
                }
                (&ErrorKind::Enum(ref __self_0, ref __self_1),) => {
                    let mut builder = __arg_0.debug_tuple("Enum");
                    let _ = builder.field(&&(*__self_0));
                    let _ = builder.field(&&(*__self_1));
                    builder.finish()
                }
                (&ErrorKind::ParseInt(ref __self_0, ref __self_1),) => {
                    let mut builder = __arg_0.debug_tuple("ParseInt");
                    let _ = builder.field(&&(*__self_0));
                    let _ = builder.field(&&(*__self_1));
                    builder.finish()
                }
                (&ErrorKind::TakeWhile(ref __self_0),) => {
                    let mut builder = __arg_0.debug_tuple("TakeWhile");
                    let _ = builder.field(&&(*__self_0));
                    builder.finish()
                }
                (&ErrorKind::CharacterEscape,) => {
                    let mut builder = __arg_0.debug_tuple("CharacterEscape");
                    builder.finish()
                }
                (&ErrorKind::EndingQuote,) => {
                    let mut builder = __arg_0.debug_tuple("EndingQuote");
                    builder.finish()
                }
            }
        }
    }
    #[allow(unused)]
    #[allow(unknown_lints)]
    #[allow(unused_doc_comment)]
    impl ::std::fmt::Display for ErrorKind {
        fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            match *self {
                ErrorKind::Take(ref count) => {
                    let display_fn = |_, f: &mut ::std::fmt::Formatter| {
                        f.write_fmt(::std::fmt::Arguments::new_v1_formatted(
                            &["expected ", " characters"],
                            &match (&count,) {
                                (__arg0,) => [
                                    ::std::fmt::ArgumentV1::new(__arg0, ::std::fmt::Display::fmt),
                                ],
                            },
                            &[
                                ::std::fmt::rt::v1::Argument {
                                    position: ::std::fmt::rt::v1::Position::At(0usize),
                                    format: ::std::fmt::rt::v1::FormatSpec {
                                        fill: ' ',
                                        align: ::std::fmt::rt::v1::Alignment::Unknown,
                                        flags: 0u32,
                                        precision: ::std::fmt::rt::v1::Count::Implied,
                                        width: ::std::fmt::rt::v1::Count::Implied,
                                    },
                                },
                            ],
                        ))
                    };
                    display_fn(self, fmt)
                }
                ErrorKind::Literal(ref s) => {
                    let display_fn = |_, f: &mut ::std::fmt::Formatter| {
                        f.write_fmt(::std::fmt::Arguments::new_v1_formatted(
                            &["expected literal "],
                            &match (&s,) {
                                (__arg0,) => {
                                    [::std::fmt::ArgumentV1::new(__arg0, ::std::fmt::Debug::fmt)]
                                }
                            },
                            &[
                                ::std::fmt::rt::v1::Argument {
                                    position: ::std::fmt::rt::v1::Position::At(0usize),
                                    format: ::std::fmt::rt::v1::FormatSpec {
                                        fill: ' ',
                                        align: ::std::fmt::rt::v1::Alignment::Unknown,
                                        flags: 0u32,
                                        precision: ::std::fmt::rt::v1::Count::Implied,
                                        width: ::std::fmt::rt::v1::Count::Implied,
                                    },
                                },
                            ],
                        ))
                    };
                    display_fn(self, fmt)
                }
                ErrorKind::Enum(ref name, ref variants) => {
                    let display_fn = |_, f: &mut ::std::fmt::Formatter| {
                        f.write_fmt(::std::fmt::Arguments::new_v1_formatted(
                            &["expected ", " starting with one of "],
                            &match (&name, &variants) {
                                (__arg0, __arg1) => [
                                    ::std::fmt::ArgumentV1::new(__arg0, ::std::fmt::Display::fmt),
                                    ::std::fmt::ArgumentV1::new(__arg1, ::std::fmt::Debug::fmt),
                                ],
                            },
                            &[
                                ::std::fmt::rt::v1::Argument {
                                    position: ::std::fmt::rt::v1::Position::At(0usize),
                                    format: ::std::fmt::rt::v1::FormatSpec {
                                        fill: ' ',
                                        align: ::std::fmt::rt::v1::Alignment::Unknown,
                                        flags: 0u32,
                                        precision: ::std::fmt::rt::v1::Count::Implied,
                                        width: ::std::fmt::rt::v1::Count::Implied,
                                    },
                                },
                                ::std::fmt::rt::v1::Argument {
                                    position: ::std::fmt::rt::v1::Position::At(1usize),
                                    format: ::std::fmt::rt::v1::FormatSpec {
                                        fill: ' ',
                                        align: ::std::fmt::rt::v1::Alignment::Unknown,
                                        flags: 0u32,
                                        precision: ::std::fmt::rt::v1::Count::Implied,
                                        width: ::std::fmt::rt::v1::Count::Implied,
                                    },
                                },
                            ],
                        ))
                    };
                    display_fn(self, fmt)
                }
                ErrorKind::ParseInt(ref err, ref radix) => {
                    let display_fn = |_, f: &mut ::std::fmt::Formatter| {
                        f.write_fmt(::std::fmt::Arguments::new_v1_formatted(
                            &["expected a valid integer in radix "],
                            &match (&radix,) {
                                (__arg0,) => [
                                    ::std::fmt::ArgumentV1::new(__arg0, ::std::fmt::Display::fmt),
                                ],
                            },
                            &[
                                ::std::fmt::rt::v1::Argument {
                                    position: ::std::fmt::rt::v1::Position::At(0usize),
                                    format: ::std::fmt::rt::v1::FormatSpec {
                                        fill: ' ',
                                        align: ::std::fmt::rt::v1::Alignment::Unknown,
                                        flags: 0u32,
                                        precision: ::std::fmt::rt::v1::Count::Implied,
                                        width: ::std::fmt::rt::v1::Count::Implied,
                                    },
                                },
                            ],
                        ))
                    };
                    display_fn(self, fmt)
                }
                ErrorKind::TakeWhile(ref name) => {
                    let display_fn = |_, f: &mut ::std::fmt::Formatter| {
                        f.write_fmt(::std::fmt::Arguments::new_v1_formatted(
                            &["expected at least one ", " character"],
                            &match (&name,) {
                                (__arg0,) => [
                                    ::std::fmt::ArgumentV1::new(__arg0, ::std::fmt::Display::fmt),
                                ],
                            },
                            &[
                                ::std::fmt::rt::v1::Argument {
                                    position: ::std::fmt::rt::v1::Position::At(0usize),
                                    format: ::std::fmt::rt::v1::FormatSpec {
                                        fill: ' ',
                                        align: ::std::fmt::rt::v1::Alignment::Unknown,
                                        flags: 0u32,
                                        precision: ::std::fmt::rt::v1::Count::Implied,
                                        width: ::std::fmt::rt::v1::Count::Implied,
                                    },
                                },
                            ],
                        ))
                    };
                    display_fn(self, fmt)
                }
                ErrorKind::CharacterEscape => {
                    let display_fn = |_, f: &mut ::std::fmt::Formatter| {
                        f.write_fmt(::std::fmt::Arguments::new_v1(
                            &["expected \", xHH or OOO after \\"],
                            &match () {
                                () => [],
                            },
                        ))
                    };
                    display_fn(self, fmt)
                }
                ErrorKind::EndingQuote => {
                    let display_fn = |_, f: &mut ::std::fmt::Formatter| {
                        f.write_fmt(::std::fmt::Arguments::new_v1(
                            &["expected to find an ending quote"],
                            &match () {
                                () => [],
                            },
                        ))
                    };
                    display_fn(self, fmt)
                }
            }
        }
    }
    #[allow(unused)]
    #[allow(unknown_lints)]
    #[allow(unused_doc_comment)]
    impl ::std::error::Error for ErrorKind {
        fn description(&self) -> &str {
            match *self {
                ErrorKind::Take(ref count) => "more characters",
                ErrorKind::Literal(ref s) => s,
                ErrorKind::Enum(ref name, ref variants) => name,
                ErrorKind::ParseInt(ref err, ref radix) => "integer",
                ErrorKind::TakeWhile(ref name) => name,
                ErrorKind::CharacterEscape => "character escape",
                ErrorKind::EndingQuote => "finished string",
            }
        }
        fn cause(&self) -> Option<&::std::error::Error> {
            match *self {
                ErrorKind::Take(ref count) => None,
                ErrorKind::Literal(ref s) => None,
                ErrorKind::Enum(ref name, ref variants) => None,
                ErrorKind::ParseInt(ref err, ref radix) => Some(err),
                ErrorKind::TakeWhile(ref name) => None,
                ErrorKind::CharacterEscape => None,
                ErrorKind::EndingQuote => None,
            }
        }
    }
    pub type LexError<'a> = (ErrorKind, &'a str);
    pub type LexResult<'a, T> = Result<(T, &'a str), LexError<'a>>;
    fn expect<'a>(input: &'a str, s: &'static str) -> LexResult<'a, &'static str> {
        if input.starts_with(s) {
            Ok((s, &input[s.len()..]))
        } else {
            Err((ErrorKind::Literal(s), input))
        }
    }
    pub trait Lex<'a>: Sized {
        fn lex(input: &'a str) -> LexResult<'a, Self>;
    }
    macro_rules! simple_enum((
                             $ name : ident {
                             $ ( $ ( $ s : tt ) | + => $ item : ident , ) + }
                             ) => {
                             # [
                             derive ( Debug , PartialEq , Eq , Clone , Copy )
                             ] pub enum $ name { $ ( $ item , ) + } impl < 'a
                             > Lex < 'a > for $ name {
                             fn lex ( input : & 'a str ) -> LexResult < 'a ,
                             Self > {
                             static EXPECTED_LITERALS : & 'static [
                             & 'static str ] = & [ $ ( $ ( $ s ) , + ) , + ] ;
                             $ (
                             $ (
                             if let Ok ( ( _ , input ) ) = expect (
                             input , $ s ) {
                             Ok ( ( $ name :: $ item , input ) ) } else ) + )
                             + {
                             Err (
                             (
                             ErrorKind :: Enum (
                             stringify ! ( $ name ) , EXPECTED_LITERALS ) ,
                             input ) ) } } } } ;);
    #[structural_match]
    #[rustc_copy_clone_marker]
    pub enum ComparisonOp {
        Equal,
        NotEqual,
        GreaterThanEqual,
        LessThanEqual,
        GreaterThan,
        LessThan,
        Contains,
        Matches,
        BitwiseAnd,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::fmt::Debug for ComparisonOp {
        fn fmt(&self, __arg_0: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            match (&*self,) {
                (&ComparisonOp::Equal,) => {
                    let mut builder = __arg_0.debug_tuple("Equal");
                    builder.finish()
                }
                (&ComparisonOp::NotEqual,) => {
                    let mut builder = __arg_0.debug_tuple("NotEqual");
                    builder.finish()
                }
                (&ComparisonOp::GreaterThanEqual,) => {
                    let mut builder = __arg_0.debug_tuple("GreaterThanEqual");
                    builder.finish()
                }
                (&ComparisonOp::LessThanEqual,) => {
                    let mut builder = __arg_0.debug_tuple("LessThanEqual");
                    builder.finish()
                }
                (&ComparisonOp::GreaterThan,) => {
                    let mut builder = __arg_0.debug_tuple("GreaterThan");
                    builder.finish()
                }
                (&ComparisonOp::LessThan,) => {
                    let mut builder = __arg_0.debug_tuple("LessThan");
                    builder.finish()
                }
                (&ComparisonOp::Contains,) => {
                    let mut builder = __arg_0.debug_tuple("Contains");
                    builder.finish()
                }
                (&ComparisonOp::Matches,) => {
                    let mut builder = __arg_0.debug_tuple("Matches");
                    builder.finish()
                }
                (&ComparisonOp::BitwiseAnd,) => {
                    let mut builder = __arg_0.debug_tuple("BitwiseAnd");
                    builder.finish()
                }
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::cmp::PartialEq for ComparisonOp {
        #[inline]
        fn eq(&self, __arg_0: &ComparisonOp) -> bool {
            {
                let __self_vi = unsafe { ::std::intrinsics::discriminant_value(&*self) } as isize;
                let __arg_1_vi =
                    unsafe { ::std::intrinsics::discriminant_value(&*__arg_0) } as isize;
                if true && __self_vi == __arg_1_vi {
                    match (&*self, &*__arg_0) {
                        _ => true,
                    }
                } else {
                    false
                }
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::cmp::Eq for ComparisonOp {
        #[inline]
        #[doc(hidden)]
        fn assert_receiver_is_total_eq(&self) -> () {
            {}
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::clone::Clone for ComparisonOp {
        #[inline]
        fn clone(&self) -> ComparisonOp {
            {
                *self
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::marker::Copy for ComparisonOp {}
    impl<'a> Lex<'a> for ComparisonOp {
        fn lex(input: &'a str) -> LexResult<'a, Self> {
            static EXPECTED_LITERALS: &'static [&'static str] = &[
                "eq",
                "=",
                "ne",
                "!=",
                "ge",
                ">=",
                "le",
                "<=",
                "gt",
                ">",
                "lt",
                "<",
                "contains",
                "~",
                "matches",
                "&",
                "bitwise_and",
            ];
            if let Ok((_, input)) = expect(input, "eq") {
                Ok((ComparisonOp::Equal, input))
            } else if let Ok((_, input)) = expect(input, "=") {
                Ok((ComparisonOp::Equal, input))
            } else if let Ok((_, input)) = expect(input, "ne") {
                Ok((ComparisonOp::NotEqual, input))
            } else if let Ok((_, input)) = expect(input, "!=") {
                Ok((ComparisonOp::NotEqual, input))
            } else if let Ok((_, input)) = expect(input, "ge") {
                Ok((ComparisonOp::GreaterThanEqual, input))
            } else if let Ok((_, input)) = expect(input, ">=") {
                Ok((ComparisonOp::GreaterThanEqual, input))
            } else if let Ok((_, input)) = expect(input, "le") {
                Ok((ComparisonOp::LessThanEqual, input))
            } else if let Ok((_, input)) = expect(input, "<=") {
                Ok((ComparisonOp::LessThanEqual, input))
            } else if let Ok((_, input)) = expect(input, "gt") {
                Ok((ComparisonOp::GreaterThan, input))
            } else if let Ok((_, input)) = expect(input, ">") {
                Ok((ComparisonOp::GreaterThan, input))
            } else if let Ok((_, input)) = expect(input, "lt") {
                Ok((ComparisonOp::LessThan, input))
            } else if let Ok((_, input)) = expect(input, "<") {
                Ok((ComparisonOp::LessThan, input))
            } else if let Ok((_, input)) = expect(input, "contains") {
                Ok((ComparisonOp::Contains, input))
            } else if let Ok((_, input)) = expect(input, "~") {
                Ok((ComparisonOp::Matches, input))
            } else if let Ok((_, input)) = expect(input, "matches") {
                Ok((ComparisonOp::Matches, input))
            } else if let Ok((_, input)) = expect(input, "&") {
                Ok((ComparisonOp::BitwiseAnd, input))
            } else if let Ok((_, input)) = expect(input, "bitwise_and") {
                Ok((ComparisonOp::BitwiseAnd, input))
            } else {
                Err((ErrorKind::Enum("ComparisonOp", EXPECTED_LITERALS), input))
            }
        }
    }
    macro_rules! nested_enum((
                             ! impl $ input : ident , $ name : ident :: $ item
                             : ident ( $ ty : ty ) ) => {
                             nested_enum ! (
                             ! impl $ input , $ name :: $ item ( $ ty ) <- $
                             crate :: tokenizer :: Lex :: lex ) } ; (
                             ! impl $ input : ident , $ name : ident :: $ item
                             : ident <- $ func : path ) => {
                             $ func ( $ input ) . map (
                             | ( _ , input ) | ( $ name :: $ item , input ) )
                             } ; (
                             ! impl $ input : ident , $ name : ident :: $ item
                             : ident ( $ ty : ty ) <- $ func : path ) => {
                             $ func ( $ input ) . map (
                             | ( res , input ) | (
                             $ name :: $ item ( res ) , input ) ) } ; (
                             $ name : ident < 'a > {
                             $ (
                             $ item : ident $ ( ( $ ty : ty ) ) * $ (
                             <- $ func : path ) * , ) + } ) => {
                             # [ derive ( Debug , PartialEq , Eq , Clone ) ]
                             pub enum $ name < 'a > {
                             $ ( $ item $ ( ( $ ty ) ) * , ) + } impl < 'a >
                             Lex < 'a > for $ name < 'a > {
                             fn lex ( input : & 'a str ) -> LexResult < 'a ,
                             Self > {
                             let mut shortest_err = (
                             ErrorKind :: Enum (
                             stringify ! ( $ name ) , & [  ] ) , input ) ; $ (
                             match nested_enum ! (
                             ! impl input , $ name :: $ item $ ( ( $ ty ) ) *
                             $ ( <- $ func ) * ) {
                             Ok ( res ) => { return Ok ( res ) ; } Err ( err )
                             => {
                             if err . 1 . len (  ) <= shortest_err . 1 . len (
                              ) { shortest_err = err ; } } } ; ) + Err (
                             shortest_err ) } } } ;);
    fn span<'a>(input: &'a str, rest: &'a str) -> &'a str {
        &input[..input.len() - rest.len()]
    }
    fn take_while<'a, F: Fn(char) -> bool>(
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
                        Err((ErrorKind::TakeWhile(name), input))
                    };
                }
            }
        }
    }
    fn ident(input: &str) -> LexResult<&str> {
        take_while(input, "identifier", char::is_alphabetic)
    }
    fn list<
        'a,
        S,
        T,
        A,
        SP: Fn(&'a str) -> LexResult<'a, S>,
        TP: Fn(&'a str) -> LexResult<'a, T>,
        I: Fn(T) -> A,
        F: Fn(A, T) -> A,
    >(
        input: &'a str,
        sep: SP,
        item: TP,
        initial_transform: I,
        fold: F,
    ) -> LexResult<'a, A> {
        let (first, mut input) = item(input)?;
        let mut acc = initial_transform(first);
        loop {
            match sep(input) {
                Ok((_, after_sep)) => {
                    input = after_sep;
                }
                Err(_) => {
                    return Ok((acc, input));
                }
            };
            let (item, after_item) = item(input)?;
            acc = fold(acc, item);
            input = after_item;
        }
    }
    fn field<'a>(input: &'a str) -> LexResult<'a, &'a str> {
        list(input, |input| expect(input, "."), ident)
    }
    fn number(input: &str, radix: u32) -> LexResult<u64> {
        let (digits, input) = take_while(input, "digit", |c| c.is_digit(radix))?;
        let res = u64::from_str_radix(digits, radix)
            .map_err(|e| (ErrorKind::ParseInt(e, radix), digits))?;
        Ok((res, input))
    }
    fn unsigned<'a>(input: &'a str) -> LexResult<'a, u64> {
        if let Ok((_, input)) = expect(input, "0x") {
            number(input, 16)
        } else if let Ok((_, input)) = expect(input, "0") {
            number(input, 8)
        } else {
            number(input, 10)
        }
    }
    fn take<'a>(input: &'a str, count: usize) -> LexResult<'a, &'a str> {
        if input.len() >= count {
            Ok(input.split_at(count))
        } else {
            Err((ErrorKind::Take(count), input))
        }
    }
    fn fixed_byte(input: &str, digits: usize, radix: u32) -> LexResult<u8> {
        let (digits, rest) = take(input, digits)?;
        match u8::from_str_radix(digits, radix) {
            Ok(b) => Ok((b, rest)),
            Err(e) => Err((ErrorKind::ParseInt(e, radix), digits)),
        }
    }
    fn hex_byte(input: &str) -> LexResult<u8> {
        fixed_byte(input, 2, 16)
    }
    fn oct_byte(input: &str) -> LexResult<u8> {
        fixed_byte(input, 3, 8)
    }
    fn string(input: &str) -> LexResult<String> {
        let (_, input) = expect(input, "\"")?;
        let mut res = String::new();
        let mut iter = input.chars();
        loop {
            match iter.next().ok_or_else(|| (ErrorKind::EndingQuote, input))? {
                '\\' => {
                    let input = iter.as_str();
                    let (b, input) = (if let Ok((_, input)) = expect(input, "\"") {
                        Ok((b'\"', input))
                    } else if let Ok((_, input)) = expect(input, "x") {
                        hex_byte(input)
                    } else {
                        oct_byte(input).map_err(|_| (ErrorKind::CharacterEscape, input))
                    })?;
                    res.push(b as char);
                    iter = input.chars();
                }
                '\"' => return Ok((res, iter.as_str())),
                c => res.push(c),
            };
        }
    }
    fn spaces(input: &str) -> LexResult<&str> {
        take_while(input, "whitespace", char::is_whitespace)
    }
    #[structural_match]
    pub enum Value<'a> {
        Field(&'a str),
        Unsigned(u64),
        String(String),
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::std::fmt::Debug for Value<'a> {
        fn fmt(&self, __arg_0: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            match (&*self,) {
                (&Value::Field(ref __self_0),) => {
                    let mut builder = __arg_0.debug_tuple("Field");
                    let _ = builder.field(&&(*__self_0));
                    builder.finish()
                }
                (&Value::Unsigned(ref __self_0),) => {
                    let mut builder = __arg_0.debug_tuple("Unsigned");
                    let _ = builder.field(&&(*__self_0));
                    builder.finish()
                }
                (&Value::String(ref __self_0),) => {
                    let mut builder = __arg_0.debug_tuple("String");
                    let _ = builder.field(&&(*__self_0));
                    builder.finish()
                }
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::std::cmp::PartialEq for Value<'a> {
        #[inline]
        fn eq(&self, __arg_0: &Value<'a>) -> bool {
            {
                let __self_vi = unsafe { ::std::intrinsics::discriminant_value(&*self) } as isize;
                let __arg_1_vi =
                    unsafe { ::std::intrinsics::discriminant_value(&*__arg_0) } as isize;
                if true && __self_vi == __arg_1_vi {
                    match (&*self, &*__arg_0) {
                        (&Value::Field(ref __self_0), &Value::Field(ref __arg_1_0)) => {
                            true && (*__self_0) == (*__arg_1_0)
                        }
                        (&Value::Unsigned(ref __self_0), &Value::Unsigned(ref __arg_1_0)) => {
                            true && (*__self_0) == (*__arg_1_0)
                        }
                        (&Value::String(ref __self_0), &Value::String(ref __arg_1_0)) => {
                            true && (*__self_0) == (*__arg_1_0)
                        }
                        _ => unsafe { ::std::intrinsics::unreachable() },
                    }
                } else {
                    false
                }
            }
        }
        #[inline]
        fn ne(&self, __arg_0: &Value<'a>) -> bool {
            {
                let __self_vi = unsafe { ::std::intrinsics::discriminant_value(&*self) } as isize;
                let __arg_1_vi =
                    unsafe { ::std::intrinsics::discriminant_value(&*__arg_0) } as isize;
                if true && __self_vi == __arg_1_vi {
                    match (&*self, &*__arg_0) {
                        (&Value::Field(ref __self_0), &Value::Field(ref __arg_1_0)) => {
                            false || (*__self_0) != (*__arg_1_0)
                        }
                        (&Value::Unsigned(ref __self_0), &Value::Unsigned(ref __arg_1_0)) => {
                            false || (*__self_0) != (*__arg_1_0)
                        }
                        (&Value::String(ref __self_0), &Value::String(ref __arg_1_0)) => {
                            false || (*__self_0) != (*__arg_1_0)
                        }
                        _ => unsafe { ::std::intrinsics::unreachable() },
                    }
                } else {
                    true
                }
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::std::cmp::Eq for Value<'a> {
        #[inline]
        #[doc(hidden)]
        fn assert_receiver_is_total_eq(&self) -> () {
            {
                let _: ::std::cmp::AssertParamIsEq<&'a str>;
                let _: ::std::cmp::AssertParamIsEq<u64>;
                let _: ::std::cmp::AssertParamIsEq<String>;
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::std::clone::Clone for Value<'a> {
        #[inline]
        fn clone(&self) -> Value<'a> {
            match (&*self,) {
                (&Value::Field(ref __self_0),) => {
                    Value::Field(::std::clone::Clone::clone(&(*__self_0)))
                }
                (&Value::Unsigned(ref __self_0),) => {
                    Value::Unsigned(::std::clone::Clone::clone(&(*__self_0)))
                }
                (&Value::String(ref __self_0),) => {
                    Value::String(::std::clone::Clone::clone(&(*__self_0)))
                }
            }
        }
    }
    impl<'a> Lex<'a> for Value<'a> {
        fn lex(input: &'a str) -> LexResult<'a, Self> {
            let mut shortest_err = (ErrorKind::Enum("Value", &[]), input);
            match field(input).map(|(res, input)| (Value::Field(res), input)) {
                Ok(res) => {
                    return Ok(res);
                }
                Err(err) => if err.1.len() <= shortest_err.1.len() {
                    shortest_err = err;
                },
            };
            match unsigned(input).map(|(res, input)| (Value::Unsigned(res), input)) {
                Ok(res) => {
                    return Ok(res);
                }
                Err(err) => if err.1.len() <= shortest_err.1.len() {
                    shortest_err = err;
                },
            };
            match string(input).map(|(res, input)| (Value::String(res), input)) {
                Ok(res) => {
                    return Ok(res);
                }
                Err(err) => if err.1.len() <= shortest_err.1.len() {
                    shortest_err = err;
                },
            };
            Err(shortest_err)
        }
    }
    #[structural_match]
    pub enum Token<'a> {
        Value(Value<'a>),
        ComparisonOp(ComparisonOp),
        Spaces,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::std::fmt::Debug for Token<'a> {
        fn fmt(&self, __arg_0: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            match (&*self,) {
                (&Token::Value(ref __self_0),) => {
                    let mut builder = __arg_0.debug_tuple("Value");
                    let _ = builder.field(&&(*__self_0));
                    builder.finish()
                }
                (&Token::ComparisonOp(ref __self_0),) => {
                    let mut builder = __arg_0.debug_tuple("ComparisonOp");
                    let _ = builder.field(&&(*__self_0));
                    builder.finish()
                }
                (&Token::Spaces,) => {
                    let mut builder = __arg_0.debug_tuple("Spaces");
                    builder.finish()
                }
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::std::cmp::PartialEq for Token<'a> {
        #[inline]
        fn eq(&self, __arg_0: &Token<'a>) -> bool {
            {
                let __self_vi = unsafe { ::std::intrinsics::discriminant_value(&*self) } as isize;
                let __arg_1_vi =
                    unsafe { ::std::intrinsics::discriminant_value(&*__arg_0) } as isize;
                if true && __self_vi == __arg_1_vi {
                    match (&*self, &*__arg_0) {
                        (&Token::Value(ref __self_0), &Token::Value(ref __arg_1_0)) => {
                            true && (*__self_0) == (*__arg_1_0)
                        }
                        (
                            &Token::ComparisonOp(ref __self_0),
                            &Token::ComparisonOp(ref __arg_1_0),
                        ) => true && (*__self_0) == (*__arg_1_0),
                        _ => true,
                    }
                } else {
                    false
                }
            }
        }
        #[inline]
        fn ne(&self, __arg_0: &Token<'a>) -> bool {
            {
                let __self_vi = unsafe { ::std::intrinsics::discriminant_value(&*self) } as isize;
                let __arg_1_vi =
                    unsafe { ::std::intrinsics::discriminant_value(&*__arg_0) } as isize;
                if true && __self_vi == __arg_1_vi {
                    match (&*self, &*__arg_0) {
                        (&Token::Value(ref __self_0), &Token::Value(ref __arg_1_0)) => {
                            false || (*__self_0) != (*__arg_1_0)
                        }
                        (
                            &Token::ComparisonOp(ref __self_0),
                            &Token::ComparisonOp(ref __arg_1_0),
                        ) => false || (*__self_0) != (*__arg_1_0),
                        _ => false,
                    }
                } else {
                    true
                }
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::std::cmp::Eq for Token<'a> {
        #[inline]
        #[doc(hidden)]
        fn assert_receiver_is_total_eq(&self) -> () {
            {
                let _: ::std::cmp::AssertParamIsEq<Value<'a>>;
                let _: ::std::cmp::AssertParamIsEq<ComparisonOp>;
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::std::clone::Clone for Token<'a> {
        #[inline]
        fn clone(&self) -> Token<'a> {
            match (&*self,) {
                (&Token::Value(ref __self_0),) => {
                    Token::Value(::std::clone::Clone::clone(&(*__self_0)))
                }
                (&Token::ComparisonOp(ref __self_0),) => {
                    Token::ComparisonOp(::std::clone::Clone::clone(&(*__self_0)))
                }
                (&Token::Spaces,) => Token::Spaces,
            }
        }
    }
    impl<'a> Lex<'a> for Token<'a> {
        fn lex(input: &'a str) -> LexResult<'a, Self> {
            let mut shortest_err = (ErrorKind::Enum("Token", &[]), input);
            match ::tokenizer::Lex::lex(input).map(|(res, input)| (Token::Value(res), input)) {
                Ok(res) => {
                    return Ok(res);
                }
                Err(err) => if err.1.len() <= shortest_err.1.len() {
                    shortest_err = err;
                },
            };
            match ::tokenizer::Lex::lex(input).map(|(res, input)| (Token::ComparisonOp(res), input))
            {
                Ok(res) => {
                    return Ok(res);
                }
                Err(err) => if err.1.len() <= shortest_err.1.len() {
                    shortest_err = err;
                },
            };
            match spaces(input).map(|(_, input)| (Token::Spaces, input)) {
                Ok(res) => {
                    return Ok(res);
                }
                Err(err) => if err.1.len() <= shortest_err.1.len() {
                    shortest_err = err;
                },
            };
            Err(shortest_err)
        }
    }
}
