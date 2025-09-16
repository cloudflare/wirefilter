use std::{borrow::Cow, iter};

use crate::{FunctionArgs, FunctionDefinition, LhsValue, Type};

#[derive(Debug, Default)]
pub struct UrlDecodeFunction {}

fn decode_once(input: &[u8], unicode_u: bool) -> Vec<u8> {
    let mut out = Vec::with_capacity(input.len());
    let mut i = 0;
    while i < input.len() {
        match input[i] {
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b'%' => {
                if unicode_u
                    && i + 5 < input.len()
                    && (input[i + 1] == b'u' || input[i + 1] == b'U')
                {
                    let hex = &input[i + 2..i + 6];
                    if let Ok(s) = std::str::from_utf8(hex) {
                        if let Ok(code_point) = u32::from_str_radix(s, 16) {
                            if let Some(ch) = std::char::from_u32(code_point) {
                                let mut buf = [0u8; 4];
                                let encoded = ch.encode_utf8(&mut buf).as_bytes();
                                out.extend_from_slice(encoded);
                                i += 6;
                                continue;
                            }
                        }
                    }
                    out.push(b'%');
                    i += 1;
                } else if i + 2 < input.len() {
                    // parse %HH
                    let hex = &input[i + 1..i + 3];
                    if let Ok(s) = std::str::from_utf8(hex) {
                        if let Ok(byte) = u8::from_str_radix(s, 16) {
                            out.push(byte);
                            i += 3;
                            continue;
                        }
                    }
                    out.push(b'%');
                    i += 1;
                } else {
                    out.push(b'%');
                    i += 1;
                }
            }
            b => {
                out.push(b);
                i += 1;
            }
        }
    }
    out
}

#[inline]
fn url_decode<'a>(source: Cow<'_, [u8]>, options: Option<Cow<'_, [u8]>>) -> Cow<'a, [u8]> {
    // parse options: look for 'r' and 'u' characters
    let mut recursive = false;
    let mut unicode_u = false;
    if let Some(opts) = options {
        for &b in opts.as_ref() {
            match b {
                b'r' => recursive = true,
                b'u' => unicode_u = true,
                _ => {}
            }
        }
    }

    let mut current = source.into_owned();

    // At least one pass
    let mut next = decode_once(&current, unicode_u);

    if recursive {
        // Limit iterations to avoid pathological loops
        for _ in 0..10 {
            if next == current {
                break;
            }
            current = next;
            next = decode_once(&current, unicode_u);
        }
        Cow::Owned(current)
    } else {
        Cow::Owned(next)
    }
}

#[inline]
fn url_decode_impl<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let source_arg = args.next().expect("expected 1 argument, got 0");
    let options_arg = args.next();

    if args.next().is_some() {
        panic!("expected maximum 2 args, got {}", 3 + args.count());
    }

    match (source_arg, options_arg) {
        (_, Some(Err(Type::Bytes))) => None,
        (Ok(LhsValue::Bytes(source)), opt) => {
            let options_extracted = match opt {
                Some(Ok(LhsValue::Bytes(o))) => Some(o),
                None => None,
                _ => unreachable!(),
            };
            Some(LhsValue::Bytes(url_decode(source, options_extracted)))
        }
        (Err(Type::Bytes), _) => None,
        _ => unreachable!(),
    }
}

impl FunctionDefinition for UrlDecodeFunction {
    fn check_param(
        &self,
        _: &crate::ParserSettings,
        params: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        next_param: &super::FunctionParam<'_>,
        _: Option<&mut super::FunctionDefinitionContext>,
    ) -> Result<(), super::FunctionParamError> {
        match params.len() {
            0 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Field)?;
                next_param.expect_val_type(iter::once(Type::Bytes.into()))?;
            }
            1 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Literal)?;
                next_param.expect_val_type(iter::once(Type::Bytes.into()))?;
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    fn return_type(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<&super::FunctionDefinitionContext>,
    ) -> Type {
        Type::Bytes
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (1, Some(1))
    }

    fn compile(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<super::FunctionDefinitionContext>,
    ) -> Box<dyn for<'i, 'a> Fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 'static>
    {
        Box::new(url_decode_impl)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Type;

    fn owned_bytes(s: &str) -> LhsValue<'_> {
        LhsValue::Bytes(Cow::Owned(s.as_bytes().to_vec()))
    }

    #[test]
    fn test_url_decode_basic() {
        let mut args = vec![Ok(LhsValue::Bytes(Cow::Borrowed(b"John%20Doe")))].into_iter();
        assert_eq!(url_decode_impl(&mut args), Some(owned_bytes("John Doe")));

        let mut args = vec![Ok(LhsValue::Bytes(Cow::Borrowed(b"John+Doe")))].into_iter();
        assert_eq!(url_decode_impl(&mut args), Some(owned_bytes("John Doe")));

        let mut args = vec![Ok(LhsValue::Bytes(Cow::Borrowed(b"%2520")))].into_iter();
        // without recursive flag -> "%20"
        assert_eq!(url_decode_impl(&mut args), Some(owned_bytes("%20")));

        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"%2520"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"r"))),
        ]
        .into_iter();
        assert_eq!(url_decode_impl(&mut args), Some(owned_bytes(" ")));
    }

    #[test]
    fn test_url_decode_unicode_u() {
        // %u2601 -> U+2601 (cloud)
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"%u2601"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"u"))),
        ]
        .into_iter();
        let res = url_decode_impl(&mut args).unwrap();
        if let LhsValue::Bytes(b) = res {
            assert_eq!(b.into_owned(), "☁".as_bytes());
        } else {
            panic!("expected bytes")
        }
    }

    #[test]
    #[should_panic(expected = "expected 1 argument, got 0")]
    fn test_panic_no_args() {
        let mut args = vec![].into_iter();
        url_decode_impl(&mut args);
    }
}
