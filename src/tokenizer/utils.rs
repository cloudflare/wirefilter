use tokenizer::{ErrorKind, LexError, LexResult};

pub fn expect<'a>(input: &'a str, s: &'static str) -> Result<&'a str, LexError<'a>> {
    if input.starts_with(s) {
        Ok(&input[s.len()..])
    } else {
        Err((ErrorKind::Literal(s), input))
    }
}

#[macro_export]
macro_rules! simple_enum {
    ($name:ident { $( $($s:tt)|+ => $item:ident, )+ }) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        pub enum $name {
            $($item,)+
        }

        impl<'a> $crate::tokenizer::Lex<'a> for $name {
            fn lex(input: &'a str) -> $crate::tokenizer::LexResult<'a, Self> {
                static EXPECTED_LITERALS: &'static [&'static str] = &[
                    $($($s),+),+
                ];

                $($(if let Ok(input) = $crate::tokenizer::utils::expect(input, $s) {
                    Ok(($name::$item, input))
                } else)+)+ {
                    Err((
                        $crate::tokenizer::ErrorKind::Enum(stringify!($name), EXPECTED_LITERALS),
                        input
                    ))
                }
            }
        }
    };
}

#[macro_export]
macro_rules! nested_enum {
    (!impl $input:ident, $name:ident :: $item:ident ($ty:ty)) => {
        nested_enum!(!impl $input, $name::$item ($ty) <- $crate::tokenizer::Lex::lex)
    };

    (!impl $input:ident, $name:ident :: $item:ident <- $func:path) => {
        $func($input).map(|(_, input)| ($name::$item, input))
    };

    (!impl $input:ident, $name:ident :: $item:ident ( $ty:ty ) <- $func:path) => {
        $func($input).map(|(res, input)| ($name::$item(res), input))
    };

    ($name:ident <'a> { $($item:ident $(( $ty:ty ))* $(<- $func:path)*,)+ }) => {
        #[derive(Debug, PartialEq, Eq, Clone)]
        pub enum $name<'a> {
            $($item $(($ty))*,)+
        }

        impl<'a> Lex<'a> for $name<'a> {
            fn lex(input: &'a str) -> LexResult<'a, Self> {
                $(match nested_enum!(!impl input, $name::$item $(($ty))* $(<- $func)*) {
                    Ok(res) => {
                        return Ok(res);
                    }
                    Err(_) => {}
                };)+
                Err((ErrorKind::Name(stringify!($name)), input))
            }
        }
    };
}

pub fn span<'a>(input: &'a str, rest: &'a str) -> (&'a str, &'a str) {
    (&input[..input.len() - rest.len()], rest)
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
                    Ok(span(input, rest))
                } else {
                    Err((ErrorKind::CountMismatch(name, 0, 1), input))
                };
            }
        }
    }
}

pub fn list<
    'a,
    T,
    SP: Fn(&'a str) -> Result<&'a str, LexError<'a>>,
    TP: Fn(&'a str) -> LexResult<'a, T>,
>(
    input: &'a str,
    sep: SP,
    item: TP,
) -> LexResult<'a, &'a str> {
    let mut rest = item(input)?.1;
    loop {
        match sep(rest) {
            Ok(after_sep) => {
                rest = after_sep;
            }
            Err(_) => {
                break;
            }
        };
        rest = item(rest)?.1;
    }
    Ok(span(input, rest))
}

pub fn take<'a>(input: &'a str, count: usize) -> LexResult<'a, &'a str> {
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

pub fn hex_byte(input: &str) -> LexResult<u8> {
    fixed_byte(input, 2, 16)
}

pub fn oct_byte(input: &str) -> LexResult<u8> {
    fixed_byte(input, 3, 8)
}
