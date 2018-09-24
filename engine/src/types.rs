use lex::{expect, skip_space, Lex, LexError, LexResult, LexWith};
use range_set::RangeSet;
use rhs_types::Bytes;
use std::{
    cmp::Ordering,
    fmt::{self, Debug, Formatter},
    iter::FromIterator,
    marker::PhantomData,
    net::IpAddr,
    ops::Deref,
};
use strict_partial_ord::StrictPartialOrd;
use vec_set::VecSet;

struct RhsValuesLexer<'i, T: Lex<'i>> {
    input: &'i str,
    phantom: PhantomData<T>,
}

impl<'i, T: Lex<'i>> RhsValuesLexer<'i, T> {
    fn new(input: &'i str) -> Result<Self, LexError> {
        Ok(RhsValuesLexer {
            input: expect(input, "{")?,
            phantom: PhantomData,
        })
    }

    fn lex<R: FromIterator<T>>(input: &'i str) -> LexResult<'i, R> {
        let mut iter = Self::new(input)?;
        let res = iter.collect::<Result<_, _>>()?;
        Ok((res, iter.input))
    }
}

impl<'a, 'i, T: Lex<'i>> Iterator for &'a mut RhsValuesLexer<'i, T> {
    type Item = Result<T, LexError<'i>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.input = skip_space(self.input);
        if let Ok(input) = expect(self.input, "}") {
            self.input = input;
            None
        } else {
            Some(T::lex(self.input).map(|(res, input)| {
                self.input = input;
                res
            }))
        }
    }
}

macro_rules! declare_types {
    (@enum $(# $attrs:tt)* $name:ident $(<$lt:tt>)* { $($variant:ident ( $ty:ty ) , )* }) => {
        $(# $attrs)*
        pub enum $name $(<$lt>)* {
            $($variant($ty),)*
        }

        impl $(<$lt>)* GetType for $name $(<$lt>)* {
            fn get_type(&self) -> Type {
                match self {
                    $($name::$variant(_) => Type::$variant,)*
                }
            }
        }

        impl $(<$lt>)* Debug for $name $(<$lt>)* {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match self {
                    $($name::$variant(inner) => Debug::fmt(inner, f),)*
                }
            }
        }
    };

    ($($name:ident ( $lhs_ty:ty | $rhs_ty:ty | $multi_rhs_ty:ident ) , )*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
        #[repr(u8)]
        pub enum Type {
            $($name,)*
        }

        pub trait GetType {
            fn get_type(&self) -> Type;
        }

        impl GetType for Type {
            fn get_type(&self) -> Type {
                *self
            }
        }

        declare_types!(@enum #[repr(u8)] #[derive(Clone)] LhsValue<'a> {
            $($name($lhs_ty),)*
        });

        $(impl<'a> From<$lhs_ty> for LhsValue<'a> {
            fn from(value: $lhs_ty) -> Self {
                LhsValue::$name(value)
            }
        })*

        declare_types!(
            @enum
            #[derive(PartialEq, Eq, Clone, Serialize)]
            #[serde(untagged)]
            RhsValue {
                $($name($rhs_ty),)*
            }
        );

        declare_types!(
            @enum
            #[derive(PartialEq, Eq, Clone, Serialize)]
            #[serde(untagged)]
            RhsValues {
                $($name($multi_rhs_ty<$rhs_ty>),)*
            }
        );

        impl<'a> PartialOrd<RhsValue> for LhsValue<'a> {
            fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
                match (self, other) {
                    $((LhsValue::$name(lhs), RhsValue::$name(rhs)) => {
                        lhs.strict_partial_cmp(rhs)
                    },)*
                    _ => None,
                }
            }
        }

        impl<'a> StrictPartialOrd<RhsValue> for LhsValue<'a> {}

        impl<'a> PartialEq<RhsValue> for LhsValue<'a> {
            fn eq(&self, other: &RhsValue) -> bool {
                self.strict_partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl<'i> LexWith<'i, Type> for RhsValue {
            fn lex_with(input: &str, ty: Type) -> LexResult<Self> {
                Ok(match ty {
                    $(Type::$name => {
                        let (value, input) = <$rhs_ty>::lex(input)?;
                        (RhsValue::$name(value), input)
                    })*
                })
            }
        }

        impl<'i> LexWith<'i, Type> for RhsValues {
            fn lex_with(input: &str, ty: Type) -> LexResult<Self> {
                Ok(match ty {
                    $(Type::$name => {
                        let (value, input) = RhsValuesLexer::lex(input)?;
                        (RhsValues::$name(value), input)
                    })*
                })
            }
        }

        impl RhsValues {
            pub fn contains(&self, lhs: &LhsValue) -> bool {
                match (self, lhs) {
                    $((RhsValues::$name(values), LhsValue::$name(lhs)) => {
                        values.contains(lhs.deref())
                    })*
                    _ => false,
                }
            }
        }
    };
}

// special case for simply passing strings
impl<'a> From<&'a str> for LhsValue<'a> {
    fn from(s: &'a str) -> Self {
        s.as_bytes().into()
    }
}

impl<'i> Lex<'i> for bool {
    fn lex(_input: &str) -> LexResult<Self> {
        // Boolean fields should be checked without parsing RHS value
        unreachable!()
    }
}

impl StrictPartialOrd for bool {}

declare_types!(
    Ip(IpAddr | IpAddr | RangeSet),
    Bytes(&'a [u8] | Bytes | VecSet),
    Unsigned(u64 | u64 | RangeSet),
    Bool(bool | bool | VecSet),
);
