use std::iter;

use crate::{ExpectedType, FunctionArgs, FunctionDefinition, LhsValue, Type};

/// Returns the byte length of a String or Bytes value, or the number of elements in an array.
///
/// This function is part of the Cloudflare Ruleset Engine.
///
/// # Arguments
///
/// * `value` - A `String`, `Bytes`, or `Array` type.
///
/// # Return Value
///
/// An `Integer` representing the length.
///
///
/// # Panics
///
/// This function will panic if:
/// - No arguments are provided.
/// - More than one argument is provided.
/// - The provided argument is not of type `String`, `Bytes`, or `Array`.
///
/// # Internal Implementation Details
///
/// The `LenFunction` struct implements the `FunctionDefinition` trait,
/// providing the necessary checks for parameters, return type, and
/// compilation to the underlying `len_impl` function.
///
/// The `len_impl` function handles the core logic of calculating the length
/// based on the `LhsValue` type:
/// - For `LhsValue::Array`, it returns the number of elements.
/// - For `LhsValue::Bytes` (which includes String values), it returns the byte length.
/// - It returns `None` if the expected types (`Array` or `Bytes`) are not found,
///   simulating a missing field.
#[derive(Debug, Default)]
pub struct LenFunction {}

#[inline]
fn len_impl<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let arg = args.next().expect("expected 1 argument, got 0");

    if args.next().is_some() {
        panic!("expected 1 argument, got {}", 2 + args.count());
    }

    match arg {
        Ok(LhsValue::Array(arr)) => {
            return Some(LhsValue::Int(arr.len() as i64));
        }
        Ok(LhsValue::Bytes(bytes)) => return Some(LhsValue::Int(bytes.as_ref().len() as i64)),
        Err(Type::Array(_)) | Err(Type::Bytes) => None,
        _ => unreachable!(),
    }
}

impl FunctionDefinition for LenFunction {
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
                next_param.expect_val_type(
                    [ExpectedType::Type(Type::Bytes), ExpectedType::Array]
                        .iter()
                        .cloned(),
                )?;
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
        Type::Int
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (1, Some(0))
    }

    fn compile(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<super::FunctionDefinitionContext>,
    ) -> Box<dyn for<'i, 'a> Fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 'static>
    {
        Box::new(len_impl)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{Array, Type};
    use std::borrow::Cow;

    #[test]
    fn test_ln_fn() {
        // Test with LhsValue::Bytes
        let bytes_val = LhsValue::Bytes(Cow::Borrowed(b"hello"));
        let mut args_bytes = vec![Ok(bytes_val)].into_iter();
        assert_eq!(len_impl(&mut args_bytes), Some(LhsValue::Int(5)));

        let arr_val = LhsValue::Array(Array::from_iter([1, 2, 3].into_iter()));
        let mut args_array = vec![Ok(arr_val)].into_iter();
        assert_eq!(len_impl(&mut args_array), Some(LhsValue::Int(3)));

        // Test with empty LhsValue::Bytes
        let empty_bytes_val = LhsValue::Bytes(Cow::Borrowed(b""));
        let mut args_empty_bytes = vec![Ok(empty_bytes_val)].into_iter();
        assert_eq!(len_impl(&mut args_empty_bytes), Some(LhsValue::Int(0)));

        // Test with empty LhsValue::Array
        let empty_arr_val = LhsValue::Array(Array::new(Type::Int));
        let mut args_empty_array = vec![Ok(empty_arr_val)].into_iter();
        assert_eq!(len_impl(&mut args_empty_array), Some(LhsValue::Int(0)));

        // Test with Err(Type::Bytes) - simulating missing field
        let mut args_err_bytes = vec![Err(Type::Bytes)].into_iter();
        assert_eq!(len_impl(&mut args_err_bytes), None);

        // Test with Err(Type::Array(_)) - simulating missing field
        let mut args_err_array = vec![Err(Type::Array(Type::Int.into()))].into_iter();
        assert_eq!(len_impl(&mut args_err_array), None);
    }

    #[test]
    #[should_panic(expected = "expected 1 argument, got 0")]
    fn test_len_fn_no_args() {
        let mut args = vec![].into_iter();
        len_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected 1 argument, got 2")]
    fn test_len_fn_too_many_args() {
        let val1 = LhsValue::Bytes(Cow::Borrowed(b"a"));
        let val2 = LhsValue::Bytes(Cow::Borrowed(b"b"));
        let mut args = vec![Ok(val1), Ok(val2)].into_iter();
        len_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected 1 argument, got 3")]
    fn test_len_fn_three_args() {
        let val1 = LhsValue::Bytes(Cow::Borrowed(b"a"));
        let val2 = LhsValue::Bytes(Cow::Borrowed(b"b"));
        let val3 = LhsValue::Bytes(Cow::Borrowed(b"c"));
        let mut args = vec![Ok(val1), Ok(val2), Ok(val3)].into_iter();
        len_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "internal error: entered unreachable code")]
    fn test_len_fn_incorrect_type_int() {
        let val = LhsValue::Int(123);
        let mut args = vec![Ok(val)].into_iter();
        len_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "internal error: entered unreachable code")]
    fn test_len_fn_incorrect_type_bool() {
        let val = LhsValue::Bool(true);
        let mut args = vec![Ok(val)].into_iter();
        len_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "internal error: entered unreachable code")]
    fn test_len_fn_incorrect_type_ip() {
        let val = LhsValue::Ip("1.1.1.1".parse().unwrap());
        let mut args = vec![Ok(val)].into_iter();
        len_impl(&mut args);
    }
}
