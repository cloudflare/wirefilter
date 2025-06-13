use std::{borrow::Cow, iter};

use crate::{FunctionArgs, FunctionDefinition, LhsValue, Type};
use outer_regex::bytes::Regex;

#[derive(Debug, Default)]
pub struct WildcardReplaceFunction {}

#[inline]
fn wildcard_replace<'a>(
    source: Cow<'_, [u8]>,
    wildcard_pattern: Cow<'_, [u8]>,
    replacement: Cow<'_, [u8]>,
    flags: Option<Cow<'_, [u8]>>,
) -> Cow<'a, [u8]> {
    let widlcard_pattern_str = std::str::from_utf8(wildcard_pattern.as_ref())
        .expect("Pattern argument must be valid UTF-8 for wildcard replacement.");

    let replacement_str = std::str::from_utf8(replacement.as_ref())
        .expect("Replacement argument must be valid UTF-8 for wildcard replacement.");

    let mut regex_pattern_str = String::from('^');
    for c in widlcard_pattern_str.chars() {
        match c {
            '*' => regex_pattern_str.push_str("(.*?)"),
            '?' => regex_pattern_str.push('.'),
            '.' | '+' | '[' | ']' | '{' | '}' | '(' | ')' | '\\' | '^' | '$' | '|' => {
                regex_pattern_str.push('\\');
                regex_pattern_str.push(c);
            }
            _ => {
                regex_pattern_str.push(c);
            }
        }
    }

    let final_regex_pattern = match flags {
        Some(flag_bytes) => {
            if flag_bytes.as_ref() == [b's'] {
                regex_pattern_str
            } else {
                format!("(?i){}", regex_pattern_str)
            }
        }
        _ => regex_pattern_str,
    };

    let re = Regex::new(&final_regex_pattern).expect("Invalid regex pattern generated.");
    let replaced_bytes: Cow<'_, [u8]> = re.replace_all(source.as_ref(), replacement_str.as_bytes());

    Cow::Owned(replaced_bytes.into_owned())
}

#[inline]
fn wildcard_replace_impl<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let source_arg = args.next().expect("expected at least 3 args, got 0");
    let wildcard_pattern_arg = args.next().expect("expected at least 3 args, got 1");
    let replacement_arg = args.next().expect("expected at least 3 args, got 2");
    let flags_arg = args.next();

    if args.next().is_some() {
        panic!("expected maximum 4 args, got {}", 5 + args.count());
    }

    match (source_arg, wildcard_pattern_arg, replacement_arg, flags_arg) {
        (_, _, _, Some(Err(Type::Bytes))) => None, // needs to be tested here so it does not go into unreachable
        (
            Ok(LhsValue::Bytes(source)),
            Ok(LhsValue::Bytes(wildcard_pattern)),
            Ok(LhsValue::Bytes(replacement)),
            flags,
        ) => {
            let flags_extracted = match flags {
                Some(Ok(LhsValue::Bytes(flags_raw))) => Some(flags_raw),
                None => None,
                _ => unreachable!(),
            };
            Some(LhsValue::Bytes(wildcard_replace(
                source,
                wildcard_pattern,
                replacement,
                flags_extracted,
            )))
        }
        (Err(Type::Bytes), _, _, _) => None,
        (_, Err(Type::Bytes), _, _) => None,
        (_, _, Err(Type::Bytes), _) => None,
        _ => unreachable!(),
    }
}

impl FunctionDefinition for WildcardReplaceFunction {
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
            2 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Literal)?;
                next_param.expect_val_type(iter::once(Type::Bytes.into()))?;
            }
            3 => {
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
        (3, Some(1))
    }

    fn compile(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<super::FunctionDefinitionContext>,
    ) -> Box<dyn for<'i, 'a> Fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 'static>
    {
        Box::new(wildcard_replace_impl)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Type;
    use std::borrow::Cow;

    fn owned_bytes(s: &str) -> LhsValue<'_> {
        LhsValue::Bytes(Cow::Owned(s.as_bytes().to_vec()))
    }

    #[test]
    fn test_wildcard_replace_for_uri() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(
                b"https://apps.example.com/calendar/admin?expand=true",
            ))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"https://*.example.com/*/*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(
                b"https://example.com/${1}/${2}/${3}",
            ))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes(
                "https://example.com/apps/calendar/admin?expand=true"
            ))
        );

        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(
                b"https://example.com/applications/app1",
            ))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/applications/*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/apps/${1}"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("https://example.com/applications/app1"))
        );

        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/calendar"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/apps/${1}"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("/apps/calendar"))
        );

        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/Apps/calendar"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/apps/*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/${1}"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"s"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("/Apps/calendar"))
        );

        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/apps/calendar/login"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/apps/*/login"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/${1}/login"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("/calendar/login"))
        );
    }

    #[test]
    fn test_wildcard_replace_basic() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"hello world"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"w*d"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"universe"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("hello world"))
        );
    }

    #[test]
    fn test_wildcard_replace_special_chars_in_pattern() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"file.txt"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"*.txt"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"document.md"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("document.md"))
        );
    }

    #[test]
    fn test_wildcard_replace_no_match() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"hello world"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"xyz*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"test"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("hello world")) // Should return original if no match
        );
    }

    #[test]
    fn test_wildcard_replace_empty_source() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b""))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"replaced"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("replaced"))
        );
    }

    #[test]
    fn test_wildcard_replace_empty_pattern() {
        // Empty pattern should match nothing, effectively replacing nothing or behaving as per regex crate.
        // Regex with empty pattern usually matches at every position.
        // Current logic converts "" to "", which matches at every position.
        // replace_all with "" and "X" on "abc" -> "XabcX" (if regex matches start/end of string)
        // or "XaXbXcX" (if regex matches between chars).
        // The current code's `re.replace_all` with an empty pattern and "X" on "abc" results in "Xabc".
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"abc"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b""))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"X"))),
        ]
        .into_iter();
        assert_eq!(wildcard_replace_impl(&mut args), Some(owned_bytes("Xabc")));
    }

    #[test]
    fn test_wildcard_replace_empty_replacement() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"remove this part"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b" this *"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b""))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("remove this part"))
        );
    }

    #[test]
    fn test_wildcard_replace_with_s_flag() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"HELLO world"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"h*o"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"X"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"s"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("HELLO world"))
        );
    }

    #[test]
    fn test_wildcard_replace_no_flag() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"HELLO world"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"h*o"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"X"))),
        ]
        .into_iter();
        assert_eq!(
            wildcard_replace_impl(&mut args),
            Some(owned_bytes("HELLO world"))
        );
    }

    #[test]
    #[should_panic(expected = "expected at least 3 args, got 0")]
    fn test_panic_no_args() {
        let mut args = vec![].into_iter();
        wildcard_replace_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected at least 3 args, got 2")]
    fn test_panic_two_args() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"a"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"b"))),
        ]
        .into_iter();
        wildcard_replace_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected maximum 4 args, got 5")]
    fn test_panic_five_args() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"a"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"b"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"c"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"d"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"e"))),
        ]
        .into_iter();
        wildcard_replace_impl(&mut args);
    }

    #[test]
    fn test_err_propagation() {
        // Source is Err
        let mut args_err_source = vec![
            Err(Type::Bytes),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"rep"))),
        ]
        .into_iter();
        assert_eq!(wildcard_replace_impl(&mut args_err_source), None);

        // Pattern is Err
        let mut args_err_pattern = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"abc"))),
            Err(Type::Bytes),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"rep"))),
        ]
        .into_iter();
        assert_eq!(wildcard_replace_impl(&mut args_err_pattern), None);

        // Replacement is Err
        let mut args_err_replacement = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"abc"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"*"))),
            Err(Type::Bytes),
        ]
        .into_iter();
        assert_eq!(wildcard_replace_impl(&mut args_err_replacement), None);

        // Flags is Err
        let mut args_err_flags = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"abc"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"rep"))),
            Err(Type::Bytes),
        ]
        .into_iter();
        assert_eq!(wildcard_replace_impl(&mut args_err_flags), None);
    }

    #[test]
    #[should_panic(expected = "Pattern argument must be valid UTF-8 for wildcard replacement.")]
    fn test_panic_invalid_utf8_pattern() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"source"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"\xFF\xFE"))), // Invalid UTF-8
            Ok(LhsValue::Bytes(Cow::Borrowed(b"replacement"))),
        ]
        .into_iter();
        wildcard_replace_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "Replacement argument must be valid UTF-8 for wildcard replacement.")]
    fn test_panic_invalid_utf8_replacement() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"source"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"\xFF\xFE"))), // Invalid UTF-8
        ]
        .into_iter();
        wildcard_replace_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "internal error: entered unreachable code")]
    fn test_panic_incorrect_arg_type() {
        let mut args = vec![
            Ok(LhsValue::Int(123)), // Not Bytes
            Ok(LhsValue::Bytes(Cow::Borrowed(b"*"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"replacement"))),
        ]
        .into_iter();
        wildcard_replace_impl(&mut args);
    }
}
