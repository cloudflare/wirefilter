use std::iter;

use crate::{LhsValue, Type};

use super::{FunctionArgKind, FunctionArgs, FunctionDefinition};

/// Returns `true` when the source starts with a given substring. Returns `false` otherwise. The source cannot be a literal value (like `"foo"`).
/// For example, if `http.request.uri.path` is `"/blog/first-post"`, then `starts_with(http.request.uri.path, "/blog")` will return `true`.
#[derive(Default, Debug)]
pub struct StartsWithFunction {}

#[inline]
fn starts_with_impl<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let source_arg = args.next().expect("expected 2 argument, got 0");
    let substring_arg = args.next().expect("expected 2 arguments, got 1");

    if args.next().is_some() {
        panic!("expected 2 arguments, got {}", 3 + args.count());
    }

    match (source_arg, substring_arg) {
        (Ok(LhsValue::Bytes(source_bytes)), Ok(LhsValue::Bytes(substring_bytes))) => {
            let res = source_bytes.as_ref().starts_with(substring_bytes.as_ref());
            Some(LhsValue::Bool(res))
        }
        (Err(Type::Bytes), _) => None,
        (_, Err(Type::Bytes)) => None,
        _ => unreachable!(),
    }
}

impl FunctionDefinition for StartsWithFunction {
    fn check_param(
        &self,
        _: &crate::ParserSettings,
        params: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        next_param: &super::FunctionParam<'_>,
        _: Option<&mut super::FunctionDefinitionContext>,
    ) -> Result<(), super::FunctionParamError> {
        match params.len() {
            1 => {
                // first arg
                next_param.expect_arg_kind(FunctionArgKind::Field)?;
                next_param.expect_val_type(iter::once(Type::Bytes.into()))?;
            }
            0 => {
                // second arg
                next_param.expect_arg_kind(FunctionArgKind::Literal)?;
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
    ) -> crate::Type {
        Type::Bool
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (2, Some(0))
    }

    fn compile(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<super::FunctionDefinitionContext>,
    ) -> Box<dyn for<'i, 'a> Fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 'static>
    {
        Box::new(starts_with_impl)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Cow;

    // fn create_bytes_lhs_val(s: &str) -> LhsValue<'_> {
    //     LhsValue::Bytes(Cow::Owned(s.as_bytes().to_vec()))
    // }

    #[test]
    fn test_starts_with_fn() {
        let mut true_args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"example_value"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"exampl"))),
        ]
        .into_iter();
        assert_eq!(starts_with_impl(&mut true_args), Some(LhsValue::Bool(true)));

        let mut false_args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"example_value"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"empl"))),
        ]
        .into_iter();
        assert_eq!(
            starts_with_impl(&mut false_args),
            Some(LhsValue::Bool(false))
        );

        let mut empty_source_args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b""))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"exampl"))),
        ]
        .into_iter();
        assert_eq!(
            starts_with_impl(&mut empty_source_args),
            Some(LhsValue::Bool(false))
        );

        let mut empty_substring_args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"example_value"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b""))),
        ]
        .into_iter();
        assert_eq!(
            starts_with_impl(&mut empty_substring_args),
            Some(LhsValue::Bool(true))
        );
    }

    #[test]
    #[should_panic(expected = "expected 2 arguments, got 1")]
    fn test_too_few_args() {
        let mut args = vec![Err(Type::Bytes)].into_iter();
        starts_with_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected 2 arguments, got 3")]
    fn test_too_many_args() {
        let mut args = vec![Err(Type::Bytes), Err(Type::Bytes), Err(Type::Bytes)].into_iter();
        starts_with_impl(&mut args);
    }

    #[test]
    fn test_bad_args() {
        let mut first_arg_error =
            vec![Err(Type::Bytes), Ok(LhsValue::Bytes(Cow::Borrowed(b"")))].into_iter();
        assert_eq!(starts_with_impl(&mut first_arg_error), None);

        let mut second_arg_error =
            vec![Ok(LhsValue::Bytes(Cow::Borrowed(b""))), Err(Type::Bytes)].into_iter();
        assert_eq!(starts_with_impl(&mut second_arg_error), None);

        let mut both_arg_error = vec![Err(Type::Bytes), Err(Type::Bytes)].into_iter();
        assert_eq!(starts_with_impl(&mut both_arg_error), None);
    }
}
