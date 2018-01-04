use {ErrorKind, LexError, LexResult, Lex};

pub fn expect<'a>(input: &'a str, s: &'static str) -> Result<&'a str, LexError<'a>> {
    if input.starts_with(s) {
        Ok(&input[s.len()..])
    } else {
        Err((ErrorKind::Literal(s), input))
    }
}

macro_rules! simple_enum {
    ($name:ident { $( $($s:tt)|+ => $item:ident, )+ }) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
        pub enum $name {
            $($item,)+
        }

        impl<'a> $crate::Lex<'a> for $name {
            fn lex(input: &'a str) -> $crate::LexResult<'a, Self> {
                static EXPECTED_LITERALS: &'static [&'static str] = &[
                    $($($s),+),+
                ];

                $($(if let Ok(input) = $crate::utils::expect(input, $s) {
                    Ok(($name::$item, input))
                } else)+)+ {
                    Err((
                        $crate::ErrorKind::Enum(stringify!($name), EXPECTED_LITERALS),
                        input
                    ))
                }
            }
        }
    };
}

macro_rules! nested_enum {
    (!impl $input:ident, $name:ident :: $item:ident ($ty:ty)) => {
        nested_enum!(!impl $input, $name::$item ($ty) <- $crate::Lex::lex)
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

        impl<'a> $crate::Lex<'a> for $name {
            fn lex(input: &'a str) -> $crate::LexResult<'a, Self> {
                $(match nested_enum!(!impl input, $name::$item $(($ty))* $(<- $func)*) {
                    Ok(res) => {
                        return Ok(res);
                    }
                    Err(_) => {}
                };)+
                Err(($crate::ErrorKind::Name(stringify!($name)), input))
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
                    Err((ErrorKind::CountMismatch(name, 0, 1), input))
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
            ErrorKind::CountMismatch("character", input.len(), count),
            input,
        ))
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

impl<'a, T: Lex<'a>> Lex<'a> for Vec<T> {
    fn lex(mut input: &'a str) -> LexResult<Self> {
        let mut res = Vec::new();
        loop {
            let (item, rest) = T::lex(input.trim_left())?;
            res.push(item);
            input = rest.trim_left();
            if let Ok(rest) = expect(input, ",") {
                input = rest.trim_left();
            } else {
                return Ok((res, input));
            }
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
