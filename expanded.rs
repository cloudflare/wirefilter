#![feature(prelude_import)]
#![no_std]
#[prelude_import]
use std::prelude::v1::*;
#[macro_use]
extern crate nom;
#[macro_use]
extern crate std as std;

use nom::*;
use std::str::FromStr;

#[structural_match]
#[rustc_copy_clone_marker]
pub enum Operator {
    Equal,
    NotEqual,
    GreaterThan,
    LessThan,
    GreaterThanEqual,
    LessThanEqual,
    Contains,
    Matches,
    BitwiseAnd,
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::fmt::Debug for Operator {
    fn fmt(&self, __arg_0: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match (&*self,) {
            (&Operator::Equal,) => {
                let mut builder = __arg_0.debug_tuple("Equal");
                builder.finish()
            }
            (&Operator::NotEqual,) => {
                let mut builder = __arg_0.debug_tuple("NotEqual");
                builder.finish()
            }
            (&Operator::GreaterThan,) => {
                let mut builder = __arg_0.debug_tuple("GreaterThan");
                builder.finish()
            }
            (&Operator::LessThan,) => {
                let mut builder = __arg_0.debug_tuple("LessThan");
                builder.finish()
            }
            (&Operator::GreaterThanEqual,) => {
                let mut builder = __arg_0.debug_tuple("GreaterThanEqual");
                builder.finish()
            }
            (&Operator::LessThanEqual,) => {
                let mut builder = __arg_0.debug_tuple("LessThanEqual");
                builder.finish()
            }
            (&Operator::Contains,) => {
                let mut builder = __arg_0.debug_tuple("Contains");
                builder.finish()
            }
            (&Operator::Matches,) => {
                let mut builder = __arg_0.debug_tuple("Matches");
                builder.finish()
            }
            (&Operator::BitwiseAnd,) => {
                let mut builder = __arg_0.debug_tuple("BitwiseAnd");
                builder.finish()
            }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::cmp::PartialEq for Operator {
    #[inline]
    fn eq(&self, __arg_0: &Operator) -> bool {
        {
            let __self_vi = unsafe { ::std::intrinsics::discriminant_value(&*self) } as isize;
            let __arg_1_vi = unsafe { ::std::intrinsics::discriminant_value(&*__arg_0) } as isize;
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
impl ::std::cmp::Eq for Operator {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {}
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::clone::Clone for Operator {
    #[inline]
    fn clone(&self) -> Operator {
        {
            *self
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::marker::Copy for Operator {}

#[structural_match]
pub enum Token<'a> {
    Identifier(&'a str),
    Dot,
    Operator(Operator),
    Unsigned(u64),
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl<'a> ::std::fmt::Debug for Token<'a> {
    fn fmt(&self, __arg_0: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match (&*self,) {
            (&Token::Identifier(ref __self_0),) => {
                let mut builder = __arg_0.debug_tuple("Identifier");
                let _ = builder.field(&&(*__self_0));
                builder.finish()
            }
            (&Token::Dot,) => {
                let mut builder = __arg_0.debug_tuple("Dot");
                builder.finish()
            }
            (&Token::Operator(ref __self_0),) => {
                let mut builder = __arg_0.debug_tuple("Operator");
                let _ = builder.field(&&(*__self_0));
                builder.finish()
            }
            (&Token::Unsigned(ref __self_0),) => {
                let mut builder = __arg_0.debug_tuple("Unsigned");
                let _ = builder.field(&&(*__self_0));
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
            let __arg_1_vi = unsafe { ::std::intrinsics::discriminant_value(&*__arg_0) } as isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*__arg_0) {
                    (&Token::Identifier(ref __self_0), &Token::Identifier(ref __arg_1_0)) => {
                        true && (*__self_0) == (*__arg_1_0)
                    }
                    (&Token::Operator(ref __self_0), &Token::Operator(ref __arg_1_0)) => {
                        true && (*__self_0) == (*__arg_1_0)
                    }
                    (&Token::Unsigned(ref __self_0), &Token::Unsigned(ref __arg_1_0)) => {
                        true && (*__self_0) == (*__arg_1_0)
                    }
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
            let __arg_1_vi = unsafe { ::std::intrinsics::discriminant_value(&*__arg_0) } as isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*__arg_0) {
                    (&Token::Identifier(ref __self_0), &Token::Identifier(ref __arg_1_0)) => {
                        false || (*__self_0) != (*__arg_1_0)
                    }
                    (&Token::Operator(ref __self_0), &Token::Operator(ref __arg_1_0)) => {
                        false || (*__self_0) != (*__arg_1_0)
                    }
                    (&Token::Unsigned(ref __self_0), &Token::Unsigned(ref __arg_1_0)) => {
                        false || (*__self_0) != (*__arg_1_0)
                    }
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
            let _: ::std::cmp::AssertParamIsEq<&'a str>;
            let _: ::std::cmp::AssertParamIsEq<Operator>;
            let _: ::std::cmp::AssertParamIsEq<u64>;
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl<'a> ::std::clone::Clone for Token<'a> {
    #[inline]
    fn clone(&self) -> Token<'a> {
        match (&*self,) {
            (&Token::Identifier(ref __self_0),) => {
                Token::Identifier(::std::clone::Clone::clone(&(*__self_0)))
            }
            (&Token::Dot,) => Token::Dot,
            (&Token::Operator(ref __self_0),) => {
                Token::Operator(::std::clone::Clone::clone(&(*__self_0)))
            }
            (&Token::Unsigned(ref __self_0),) => {
                Token::Unsigned(::std::clone::Clone::clone(&(*__self_0)))
            }
        }
    }
}







#[allow(unused_variables)]
fn parse_unsigned(i: &str) -> ::IResult<&str, u64, u32> {
    {
        {
            let i_ = i.clone();
            let res = {
                match {
                    {
                        let i_ = i_.clone();
                        match {
                            use {Compare, CompareResult, InputLength, Slice};
                            let res: ::IResult<_, _> = match (i_).compare("0x") {
                                CompareResult::Ok => {
                                    let blen = "0x".input_len();
                                    ::IResult::Done(i_.slice(blen..), i_.slice(..blen))
                                }
                                CompareResult::Incomplete => {
                                    ::IResult::Incomplete(::Needed::Size("0x".input_len()))
                                }
                                CompareResult::Error => {
                                    ::IResult::Error(::Err::Position(::ErrorKind::Tag, i_))
                                }
                            };
                            res
                        } {
                            ::IResult::Error(e) => ::IResult::Error(e),
                            ::IResult::Incomplete(::Needed::Unknown) => {
                                ::IResult::Incomplete(::Needed::Unknown)
                            }
                            ::IResult::Incomplete(::Needed::Size(i)) => {
                                let (needed, overflowed) = 0usize.overflowing_add(i);
                                match overflowed {
                                    true => ::IResult::Incomplete(::Needed::Unknown),
                                    false => ::IResult::Incomplete(::Needed::Size(needed)),
                                }
                            }
                            ::IResult::Done(i, o) => {
                                let i_ = i.clone();
                                {
                                    match {
                                        pub fn _unify<T, R, F: FnOnce(T) -> R>(f: F, t: T) -> R {
                                            f(t)
                                        }
                                        match hex_digit(i_) {
                                            ::IResult::Error(e) => ::IResult::Error(e),
                                            ::IResult::Incomplete(::Needed::Unknown) => {
                                                ::IResult::Incomplete(::Needed::Unknown)
                                            }
                                            ::IResult::Incomplete(::Needed::Size(i)) => {
                                                ::IResult::Incomplete(::Needed::Size(i))
                                            }
                                            ::IResult::Done(i, o) => ::IResult::Done(
                                                i,
                                                _unify(|digits| u64::from_str_radix(digits, 16), o),
                                            ),
                                        }
                                    } {
                                        ::IResult::Error(e) => ::IResult::Error(e),
                                        ::IResult::Incomplete(::Needed::Unknown) => {
                                            ::IResult::Incomplete(::Needed::Unknown)
                                        }
                                        ::IResult::Incomplete(::Needed::Size(i)) => {
                                            let (needed, overflowed) =
                                                (0usize
                                                    + (::InputLength::input_len(&(i_))
                                                        - ::InputLength::input_len(&i)))
                                                    .overflowing_add(i);
                                            match overflowed {
                                                true => ::IResult::Incomplete(::Needed::Unknown),
                                                false => {
                                                    ::IResult::Incomplete(::Needed::Size(needed))
                                                }
                                            }
                                        }
                                        ::IResult::Done(i, o) => ::IResult::Done(i, (o, o)),
                                    }
                                }
                            }
                        }
                    }
                } {
                    ::IResult::Error(a) => ::IResult::Error(a),
                    ::IResult::Incomplete(i) => ::IResult::Incomplete(i),
                    ::IResult::Done(remaining, (_, o)) => ::IResult::Done(remaining, o),
                }
            };
            match res {
                ::IResult::Done(_, _) => res,
                ::IResult::Incomplete(_) => res,
                ::IResult::Error(e) => {
                    let out = {
                        let i_ = i.clone();
                        let res = {
                            match {
                                {
                                    let i_ = i_.clone();
                                    match {
                                        use {Compare, CompareResult, InputLength, Slice};
                                        let res:
                                                                    ::IResult<_,
                                                                              _> =
                                                                match (i_).compare("0")
                                                                    {
                                                                    CompareResult::Ok
                                                                    => {
                                                                        let blen =
                                                                            "0".input_len();
                                                                        ::IResult::Done(i_.slice(blen..),
                                                                                        i_.slice(..blen))
                                                                    }
                                                                    CompareResult::Incomplete
                                                                    => {
                                                                        ::IResult::Incomplete(::Needed::Size("0".input_len()))
                                                                    }
                                                                    CompareResult::Error
                                                                    => {
                                                                        ::IResult::Error(::Err::Position(::ErrorKind::Tag,
                                                                                                         i_))
                                                                    }
                                                                };
                                        res
                                    } {
                                        ::IResult::Error(e) => ::IResult::Error(e),
                                        ::IResult::Incomplete(::Needed::Unknown) => {
                                            ::IResult::Incomplete(::Needed::Unknown)
                                        }
                                        ::IResult::Incomplete(::Needed::Size(i)) => {
                                            let (needed, overflowed) = 0usize.overflowing_add(i);
                                            match overflowed {
                                                true => ::IResult::Incomplete(::Needed::Unknown),
                                                false => {
                                                    ::IResult::Incomplete(::Needed::Size(needed))
                                                }
                                            }
                                        }
                                        ::IResult::Done(i, o) => {
                                            let i_ = i.clone();
                                            {
                                                match {
                                                    pub fn _unify<T, R, F: FnOnce(T) -> R>(
                                                        f: F,
                                                        t: T,
                                                    ) -> R
                                                    {
                                                        f(t)
                                                    }
                                                    match oct_digit(i_) {
                                                        ::IResult::Error(e) => ::IResult::Error(e),
                                                        ::IResult::Incomplete(
                                                            ::Needed::Unknown,
                                                        ) => {
                                                            ::IResult::Incomplete(::Needed::Unknown)
                                                        }
                                                        ::IResult::Incomplete(
                                                            ::Needed::Size(i),
                                                        ) => {
                                                            ::IResult::Incomplete(::Needed::Size(i))
                                                        }
                                                        ::IResult::Done(i, o) => ::IResult::Done(
                                                            i,
                                                            _unify(
                                                                |digits| {
                                                                    u64::from_str_radix(digits, 8)
                                                                },
                                                                o,
                                                            ),
                                                        ),
                                                    }
                                                } {
                                                    ::IResult::Error(e) => ::IResult::Error(e),
                                                    ::IResult::Incomplete(::Needed::Unknown) => {
                                                        ::IResult::Incomplete(::Needed::Unknown)
                                                    }
                                                    ::IResult::Incomplete(::Needed::Size(i)) => {
                                                        let (needed,
                                                                           overflowed) =
                                                                          (0usize
                                                                               +
                                                                               (::InputLength::input_len(&(i_))
                                                                                    -
                                                                                    ::InputLength::input_len(&i))).overflowing_add(i);
                                                        match overflowed {
                                                            true => ::IResult::Incomplete(
                                                                ::Needed::Unknown,
                                                            ),
                                                            false => ::IResult::Incomplete(
                                                                ::Needed::Size(needed),
                                                            ),
                                                        }
                                                    }
                                                    ::IResult::Done(i, o) => {
                                                        ::IResult::Done(i, (o, o))
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } {
                                ::IResult::Error(a) => ::IResult::Error(a),
                                ::IResult::Incomplete(i) => ::IResult::Incomplete(i),
                                ::IResult::Done(remaining, (_, o)) => ::IResult::Done(remaining, o),
                            }
                        };
                        match res {
                            ::IResult::Done(_, _) => res,
                            ::IResult::Incomplete(_) => res,
                            ::IResult::Error(e) => {
                                let out = {
                                    let i_ = i.clone();
                                    let res = {
                                        pub fn _unify<T, R, F: FnOnce(T) -> R>(f: F, t: T) -> R {
                                            f(t)
                                        }
                                        match digit(i_) {
                                            ::IResult::Error(e) => ::IResult::Error(e),
                                            ::IResult::Incomplete(::Needed::Unknown) => {
                                                ::IResult::Incomplete(::Needed::Unknown)
                                            }
                                            ::IResult::Incomplete(::Needed::Size(i)) => {
                                                ::IResult::Incomplete(::Needed::Size(i))
                                            }
                                            ::IResult::Done(i, o) => {
                                                ::IResult::Done(i, _unify(u64::from_str, o))
                                            }
                                        }
                                    };
                                    match res {
                                        ::IResult::Done(_, _) => res,
                                        ::IResult::Incomplete(_) => res,
                                        ::IResult::Error(e) => {
                                            let out = ::IResult::Error(
                                                ::Err::Position(::ErrorKind::Alt, i),
                                            );
                                            fn unify_types<T>(_: &T, _: &T) {}
                                            if let ::IResult::Error(ref e2) = out {
                                                unify_types(&e, e2);
                                            }
                                            out
                                        }
                                    }
                                };
                                fn unify_types<T>(_: &T, _: &T) {}
                                if let ::IResult::Error(ref e2) = out {
                                    unify_types(&e, e2);
                                }
                                out
                            }
                        }
                    };
                    fn unify_types<T>(_: &T, _: &T) {}
                    if let ::IResult::Error(ref e2) = out {
                        unify_types(&e, e2);
                    }
                    out
                }
            }
        }
    }
}
#[allow(unused_variables)]
fn parse_operator(i: &str) -> ::IResult<&str, Operator, u32> {
    {
        {
            let i_ = i.clone();
            let res = {
                match {
                    use {Compare, CompareResult, InputLength, Slice};
                    let res: ::IResult<_, _> = match (i_).compare("==") {
                        CompareResult::Ok => {
                            let blen = "==".input_len();
                            ::IResult::Done(i_.slice(blen..), i_.slice(..blen))
                        }
                        CompareResult::Incomplete => {
                            ::IResult::Incomplete(::Needed::Size("==".input_len()))
                        }
                        CompareResult::Error => {
                            ::IResult::Error(::Err::Position(::ErrorKind::Tag, i_))
                        }
                    };
                    res
                } {
                    ::IResult::Done(i, _) => {
                        let res: ::IResult<_, _> = ::IResult::Done(i, Operator::Equal);
                        res
                    }
                    ::IResult::Error(e) => ::IResult::Error(e),
                    ::IResult::Incomplete(i) => ::IResult::Incomplete(i),
                }
            };
            match res {
                ::IResult::Done(_, _) => res,
                ::IResult::Incomplete(_) => res,
                ::IResult::Error(e) => {
                    let out = {
                        let i_ = i.clone();
                        let res = {
                            match {
                                use {Compare, CompareResult, InputLength, Slice};
                                let res: ::IResult<_, _> = match (i_).compare("!=") {
                                    CompareResult::Ok => {
                                        let blen = "!=".input_len();
                                        ::IResult::Done(i_.slice(blen..), i_.slice(..blen))
                                    }
                                    CompareResult::Incomplete => {
                                        ::IResult::Incomplete(::Needed::Size("!=".input_len()))
                                    }
                                    CompareResult::Error => {
                                        ::IResult::Error(::Err::Position(::ErrorKind::Tag, i_))
                                    }
                                };
                                res
                            } {
                                ::IResult::Done(i, _) => {
                                    let res: ::IResult<_, _> =
                                        ::IResult::Done(i, Operator::NotEqual);
                                    res
                                }
                                ::IResult::Error(e) => ::IResult::Error(e),
                                ::IResult::Incomplete(i) => ::IResult::Incomplete(i),
                            }
                        };
                        match res {
                            ::IResult::Done(_, _) => res,
                            ::IResult::Incomplete(_) => res,
                            ::IResult::Error(e) => {
                                let out = {
                                    let i_ = i.clone();
                                    let res = {
                                        match {
                                            use {Compare, CompareResult, InputLength, Slice};
                                            let res:
                                                                      ::IResult<_,
                                                                                _> =
                                                                  match (i_).compare(">=")
                                                                      {
                                                                      CompareResult::Ok
                                                                      => {
                                                                          let blen =
                                                                              ">=".input_len();
                                                                          ::IResult::Done(i_.slice(blen..),
                                                                                          i_.slice(..blen))
                                                                      }
                                                                      CompareResult::Incomplete
                                                                      => {
                                                                          ::IResult::Incomplete(::Needed::Size(">=".input_len()))
                                                                      }
                                                                      CompareResult::Error
                                                                      => {
                                                                          ::IResult::Error(::Err::Position(::ErrorKind::Tag,
                                                                                                           i_))
                                                                      }
                                                                  };
                                            res
                                        } {
                                            ::IResult::Done(i, _) => {
                                                let res:
                                                                    ::IResult<_,
                                                                              _> =
                                                                ::IResult::Done(i,
                                                                                Operator::GreaterThanEqual);
                                                res
                                            }
                                            ::IResult::Error(e) => ::IResult::Error(e),
                                            ::IResult::Incomplete(i) => ::IResult::Incomplete(i),
                                        }
                                    };
                                    match res {
                                        ::IResult::Done(_, _) => res,
                                        ::IResult::Incomplete(_) => res,
                                        ::IResult::Error(e) => {
                                            let out = {
                                                let i_ = i.clone();
                                                let res = {
                                                    match {
                                                        use {Compare, CompareResult, InputLength,
                                                             Slice};
                                                        let res:
                                                                                      ::IResult<_,
                                                                                                _> =
                                                                                  match (i_).compare("<=")
                                                                                      {
                                                                                      CompareResult::Ok
                                                                                      =>
                                                                                      {
                                                                                          let blen =
                                                                                              "<=".input_len();
                                                                                          ::IResult::Done(i_.slice(blen..),
                                                                                                          i_.slice(..blen))
                                                                                      }
                                                                                      CompareResult::Incomplete
                                                                                      =>
                                                                                      {
                                                                                          ::IResult::Incomplete(::Needed::Size("<=".input_len()))
                                                                                      }
                                                                                      CompareResult::Error
                                                                                      =>
                                                                                      {
                                                                                          ::IResult::Error(::Err::Position(::ErrorKind::Tag,
                                                                                                                           i_))
                                                                                      }
                                                                                  };
                                                        res
                                                    } {
                                                        ::IResult::Done(i, _) => {
                                                            let res:
                                                                                    ::IResult<_,
                                                                                              _> =
                                                                                ::IResult::Done(i,
                                                                                                Operator::LessThanEqual);
                                                            res
                                                        }
                                                        ::IResult::Error(e) => ::IResult::Error(e),
                                                        ::IResult::Incomplete(i) => {
                                                            ::IResult::Incomplete(i)
                                                        }
                                                    }
                                                };
                                                match res {
                                                    ::IResult::Done(_, _) => res,
                                                    ::IResult::Incomplete(_) => res,
                                                    ::IResult::Error(e) => {
                                                        let out = {
                                                            let i_ = i.clone();
                                                            let res = {
                                                                match {
                                                                    use {Compare, CompareResult,
                                                                         InputLength, Slice};
                                                                    let res:
                                                                                                      ::IResult<_,
                                                                                                                _> =
                                                                                                  match (i_).compare(">")
                                                                                                      {
                                                                                                      CompareResult::Ok
                                                                                                      =>
                                                                                                      {
                                                                                                          let blen =
                                                                                                              ">".input_len();
                                                                                                          ::IResult::Done(i_.slice(blen..),
                                                                                                                          i_.slice(..blen))
                                                                                                      }
                                                                                                      CompareResult::Incomplete
                                                                                                      =>
                                                                                                      {
                                                                                                          ::IResult::Incomplete(::Needed::Size(">".input_len()))
                                                                                                      }
                                                                                                      CompareResult::Error
                                                                                                      =>
                                                                                                      {
                                                                                                          ::IResult::Error(::Err::Position(::ErrorKind::Tag,
                                                                                                                                           i_))
                                                                                                      }
                                                                                                  };
                                                                    res
                                                                } {
                                                                    ::IResult::Done(i, _) => {
                                                                        let res:
                                                                                                    ::IResult<_,
                                                                                                              _> =
                                                                                                ::IResult::Done(i,
                                                                                                                Operator::GreaterThan);
                                                                        res
                                                                    }
                                                                    ::IResult::Error(e) => {
                                                                        ::IResult::Error(e)
                                                                    }
                                                                    ::IResult::Incomplete(i) => {
                                                                        ::IResult::Incomplete(i)
                                                                    }
                                                                }
                                                            };
                                                            match res {
                                                                ::IResult::Done(_, _) => res,
                                                                ::IResult::Incomplete(_) => res,
                                                                ::IResult::Error(e) => {
                                                                    let out = {
                                                                        let i_ = i.clone();
                                                                        let res = {
                                                                            match {
                                                                                                              use ::{Compare,
                                                                                                                     CompareResult,
                                                                                                                     InputLength,
                                                                                                                     Slice};
                                                                                                              let res:
                                                                                                                      ::IResult<_,
                                                                                                                                _> =
                                                                                                                  match (i_).compare("<")
                                                                                                                      {
                                                                                                                      CompareResult::Ok
                                                                                                                      =>
                                                                                                                      {
                                                                                                                          let blen =
                                                                                                                              "<".input_len();
                                                                                                                          ::IResult::Done(i_.slice(blen..),
                                                                                                                                          i_.slice(..blen))
                                                                                                                      }
                                                                                                                      CompareResult::Incomplete
                                                                                                                      =>
                                                                                                                      {
                                                                                                                          ::IResult::Incomplete(::Needed::Size("<".input_len()))
                                                                                                                      }
                                                                                                                      CompareResult::Error
                                                                                                                      =>
                                                                                                                      {
                                                                                                                          ::IResult::Error(::Err::Position(::ErrorKind::Tag,
                                                                                                                                                           i_))
                                                                                                                      }
                                                                                                                  };
                                                                                                              res
                                                                                                          }
                                                                                                        {
                                                                                                        ::IResult::Done(i,
                                                                                                                        _)
                                                                                                        =>
                                                                                                        {
                                                                                                            let res:
                                                                                                                    ::IResult<_,
                                                                                                                              _> =
                                                                                                                ::IResult::Done(i,
                                                                                                                                Operator::LessThan);
                                                                                                            res
                                                                                                        }
                                                                                                        ::IResult::Error(e)
                                                                                                        =>
                                                                                                        ::IResult::Error(e),
                                                                                                        ::IResult::Incomplete(i)
                                                                                                        =>
                                                                                                        ::IResult::Incomplete(i),
                                                                                                    }
                                                                        };
                                                                        match res
                                                                                                {
                                                                                                ::IResult::Done(_,
                                                                                                                _)
                                                                                                =>
                                                                                                res,
                                                                                                ::IResult::Incomplete(_)
                                                                                                =>
                                                                                                res,
                                                                                                ::IResult::Error(e)
                                                                                                =>
                                                                                                {
                                                                                                    let out =
                                                                                                        {
                                                                                                            let i_ =
                                                                                                                i.clone();
                                                                                                            let res =
                                                                                                                {
                                                                                                                    match {
                                                                                                                              use ::{Compare,
                                                                                                                                     CompareResult,
                                                                                                                                     InputLength,
                                                                                                                                     Slice};
                                                                                                                              let res:
                                                                                                                                      ::IResult<_,
                                                                                                                                                _> =
                                                                                                                                  match (i_).compare("~")
                                                                                                                                      {
                                                                                                                                      CompareResult::Ok
                                                                                                                                      =>
                                                                                                                                      {
                                                                                                                                          let blen =
                                                                                                                                              "~".input_len();
                                                                                                                                          ::IResult::Done(i_.slice(blen..),
                                                                                                                                                          i_.slice(..blen))
                                                                                                                                      }
                                                                                                                                      CompareResult::Incomplete
                                                                                                                                      =>
                                                                                                                                      {
                                                                                                                                          ::IResult::Incomplete(::Needed::Size("~".input_len()))
                                                                                                                                      }
                                                                                                                                      CompareResult::Error
                                                                                                                                      =>
                                                                                                                                      {
                                                                                                                                          ::IResult::Error(::Err::Position(::ErrorKind::Tag,
                                                                                                                                                                           i_))
                                                                                                                                      }
                                                                                                                                  };
                                                                                                                              res
                                                                                                                          }
                                                                                                                        {
                                                                                                                        ::IResult::Done(i,
                                                                                                                                        _)
                                                                                                                        =>
                                                                                                                        {
                                                                                                                            let res:
                                                                                                                                    ::IResult<_,
                                                                                                                                              _> =
                                                                                                                                ::IResult::Done(i,
                                                                                                                                                Operator::Matches);
                                                                                                                            res
                                                                                                                        }
                                                                                                                        ::IResult::Error(e)
                                                                                                                        =>
                                                                                                                        ::IResult::Error(e),
                                                                                                                        ::IResult::Incomplete(i)
                                                                                                                        =>
                                                                                                                        ::IResult::Incomplete(i),
                                                                                                                    }
                                                                                                                };
                                                                                                            match res
                                                                                                                {
                                                                                                                ::IResult::Done(_,
                                                                                                                                _)
                                                                                                                =>
                                                                                                                res,
                                                                                                                ::IResult::Incomplete(_)
                                                                                                                =>
                                                                                                                res,
                                                                                                                ::IResult::Error(e)
                                                                                                                =>
                                                                                                                {
                                                                                                                    let out =
                                                                                                                        {
                                                                                                                            let i_ =
                                                                                                                                i.clone();
                                                                                                                            let res =
                                                                                                                                {
                                                                                                                                    match {
                                                                                                                                              use ::{Compare,
                                                                                                                                                     CompareResult,
                                                                                                                                                     InputLength,
                                                                                                                                                     Slice};
                                                                                                                                              let res:
                                                                                                                                                      ::IResult<_,
                                                                                                                                                                _> =
                                                                                                                                                  match (i_).compare("&")
                                                                                                                                                      {
                                                                                                                                                      CompareResult::Ok
                                                                                                                                                      =>
                                                                                                                                                      {
                                                                                                                                                          let blen =
                                                                                                                                                              "&".input_len();
                                                                                                                                                          ::IResult::Done(i_.slice(blen..),
                                                                                                                                                                          i_.slice(..blen))
                                                                                                                                                      }
                                                                                                                                                      CompareResult::Incomplete
                                                                                                                                                      =>
                                                                                                                                                      {
                                                                                                                                                          ::IResult::Incomplete(::Needed::Size("&".input_len()))
                                                                                                                                                      }
                                                                                                                                                      CompareResult::Error
                                                                                                                                                      =>
                                                                                                                                                      {
                                                                                                                                                          ::IResult::Error(::Err::Position(::ErrorKind::Tag,
                                                                                                                                                                                           i_))
                                                                                                                                                      }
                                                                                                                                                  };
                                                                                                                                              res
                                                                                                                                          }
                                                                                                                                        {
                                                                                                                                        ::IResult::Done(i,
                                                                                                                                                        _)
                                                                                                                                        =>
                                                                                                                                        {
                                                                                                                                            let res:
                                                                                                                                                    ::IResult<_,
                                                                                                                                                              _> =
                                                                                                                                                ::IResult::Done(i,
                                                                                                                                                                Operator::BitwiseAnd);
                                                                                                                                            res
                                                                                                                                        }
                                                                                                                                        ::IResult::Error(e)
                                                                                                                                        =>
                                                                                                                                        ::IResult::Error(e),
                                                                                                                                        ::IResult::Incomplete(i)
                                                                                                                                        =>
                                                                                                                                        ::IResult::Incomplete(i),
                                                                                                                                    }
                                                                                                                                };
                                                                                                                            match res
                                                                                                                                {
                                                                                                                                ::IResult::Done(_,
                                                                                                                                                _)
                                                                                                                                =>
                                                                                                                                res,
                                                                                                                                ::IResult::Incomplete(_)
                                                                                                                                =>
                                                                                                                                res,
                                                                                                                                ::IResult::Error(e)
                                                                                                                                =>
                                                                                                                                {
                                                                                                                                    let out =
                                                                                                                                        ::IResult::Error(::Err::Position(::ErrorKind::Alt,
                                                                                                                                                                         i));
                                                                                                                                    fn unify_types<T>(_:
                                                                                                                                                          &T,
                                                                                                                                                      _:
                                                                                                                                                          &T) {
                                                                                                                                    }
                                                                                                                                    if let ::IResult::Error(ref e2)
                                                                                                                                           =
                                                                                                                                           out
                                                                                                                                           {
                                                                                                                                        unify_types(&e,
                                                                                                                                                    e2);
                                                                                                                                    }
                                                                                                                                    out
                                                                                                                                }
                                                                                                                            }
                                                                                                                        };
                                                                                                                    fn unify_types<T>(_:
                                                                                                                                          &T,
                                                                                                                                      _:
                                                                                                                                          &T) {
                                                                                                                    }
                                                                                                                    if let ::IResult::Error(ref e2)
                                                                                                                           =
                                                                                                                           out
                                                                                                                           {
                                                                                                                        unify_types(&e,
                                                                                                                                    e2);
                                                                                                                    }
                                                                                                                    out
                                                                                                                }
                                                                                                            }
                                                                                                        };
                                                                                                    fn unify_types<T>(_:
                                                                                                                          &T,
                                                                                                                      _:
                                                                                                                          &T) {
                                                                                                    }
                                                                                                    if let ::IResult::Error(ref e2)
                                                                                                           =
                                                                                                           out
                                                                                                           {
                                                                                                        unify_types(&e,
                                                                                                                    e2);
                                                                                                    }
                                                                                                    out
                                                                                                }
                                                                                            }
                                                                    };
                                                                    fn unify_types<T>(
                                                                        _: &T,
                                                                        _: &T,
                                                                    )
                                                                    {
                                                                    }
                                                                    if let ::IResult::Error(
                                                                        ref e2,
                                                                    ) = out
                                                                    {
                                                                        unify_types(&e, e2);
                                                                    }
                                                                    out
                                                                }
                                                            }
                                                        };
                                                        fn unify_types<T>(_: &T, _: &T) {}
                                                        if let ::IResult::Error(ref e2) = out {
                                                            unify_types(&e, e2);
                                                        }
                                                        out
                                                    }
                                                }
                                            };
                                            fn unify_types<T>(_: &T, _: &T) {}
                                            if let ::IResult::Error(ref e2) = out {
                                                unify_types(&e, e2);
                                            }
                                            out
                                        }
                                    }
                                };
                                fn unify_types<T>(_: &T, _: &T) {}
                                if let ::IResult::Error(ref e2) = out {
                                    unify_types(&e, e2);
                                }
                                out
                            }
                        }
                    };
                    fn unify_types<T>(_: &T, _: &T) {}
                    if let ::IResult::Error(ref e2) = out {
                        unify_types(&e, e2);
                    }
                    out
                }
            }
        }
    }
}
#[allow(unused_variables)]
fn parse_identifier(i: &str) -> ::IResult<&str, Token, u32> {
    {
        {
            let i_ = i.clone();
            match {
                pub fn _unify<T, R, F: FnOnce(T) -> R>(f: F, t: T) -> R {
                    f(t)
                }
                match alpha(i_) {
                    ::IResult::Error(e) => ::IResult::Error(e),
                    ::IResult::Incomplete(::Needed::Unknown) => {
                        ::IResult::Incomplete(::Needed::Unknown)
                    }
                    ::IResult::Incomplete(::Needed::Size(i)) => {
                        ::IResult::Incomplete(::Needed::Size(i))
                    }
                    ::IResult::Done(i, o) => ::IResult::Done(i, _unify(|o| Some(o), o)),
                }
            } {
                ::IResult::Error(e) => ::IResult::Error({
                    let next_errors = match e {
                        ::Err::Code(e) => {
                            let mut v = ::std::vec::Vec::new();
                            v.push(::Err::Code(e));
                            v
                        }
                        ::Err::Position(e, p) => {
                            let mut v = ::std::vec::Vec::new();
                            v.push(::Err::Position(e, p));
                            v
                        }
                        ::Err::Node(e, mut next) => {
                            next.push(::Err::Code(e));
                            next
                        }
                        ::Err::NodePosition(e, p, mut next) => {
                            next.push(::Err::Position(e, p));
                            next
                        }
                    };
                    ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                }),
                ::IResult::Incomplete(i) => ::IResult::Incomplete(i),
                ::IResult::Done(i, o) => match o {
                    Some("eq") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::Equal));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some("ne") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::NotEqual));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some("gt") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::GreaterThan));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some("lt") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::LessThan));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some("ge") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::GreaterThanEqual));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some("le") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::LessThanEqual));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some("contains") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::Contains));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some("matches") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::Matches));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some("bitwise_and") => match {
                        let res: ::IResult<_, _> =
                            ::IResult::Done(i, Token::Operator(Operator::BitwiseAnd));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    Some(other) => match {
                        let res: ::IResult<_, _> = ::IResult::Done(i, Token::Identifier(other));
                        res
                    } {
                        ::IResult::Error(e) => ::IResult::Error({
                            let next_errors = match e {
                                ::Err::Code(e) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Code(e));
                                    v
                                }
                                ::Err::Position(e, p) => {
                                    let mut v = ::std::vec::Vec::new();
                                    v.push(::Err::Position(e, p));
                                    v
                                }
                                ::Err::Node(e, mut next) => {
                                    next.push(::Err::Code(e));
                                    next
                                }
                                ::Err::NodePosition(e, p, mut next) => {
                                    next.push(::Err::Position(e, p));
                                    next
                                }
                            };
                            ::Err::NodePosition(::ErrorKind::Switch, i, next_errors)
                        }),
                        a => a,
                    },
                    _ => ::IResult::Error(::Err::Position(::ErrorKind::Switch, i)),
                },
            }
        }
    }
}
