use crate::{
    FunctionArgKind, FunctionArgs, FunctionDefinition, FunctionDefinitionContext, FunctionParam,
    FunctionParamError, GetType, LhsValue, ParserSettings, Type,
};
use std::iter::once;

#[inline]
fn any_impl<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let arg = args.next().expect("expected 1 argument, got 0");
    if args.next().is_some() {
        panic!("expected 1 argument, got {}", 2 + args.count());
    }
    match arg {
        Ok(LhsValue::Array(arr)) => Some(LhsValue::Bool(
            arr.into_iter().any(|lhs| bool::try_from(lhs).unwrap()),
        )),
        Err(Type::Array(ref arr)) if arr.get_type() == Type::Bool => None,
        _ => unreachable!(),
    }
}

/// A function which, given an array of bool, returns true if any one of the
/// arguments is true, otherwise false.
///
/// It expects one argument and will error if given an incorrect number of
/// arguments or an argument of invalid type.
#[derive(Debug, Default)]
pub struct AnyFunction {}

impl FunctionDefinition for AnyFunction {
    fn check_param(
        &self,
        _: &ParserSettings,
        params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        next_param: &FunctionParam<'_>,
        _: Option<&mut FunctionDefinitionContext>,
    ) -> Result<(), FunctionParamError> {
        match params.len() {
            0 => {
                next_param.expect_arg_kind(FunctionArgKind::Field)?;
                next_param.expect_val_type(once(Type::Array(Type::Bool.into()).into()))?;
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    fn return_type(
        &self,
        _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        _: Option<&FunctionDefinitionContext>,
    ) -> Type {
        Type::Bool
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (1, Some(0))
    }

    fn compile<'s>(
        &'s self,
        _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        _: Option<FunctionDefinitionContext>,
    ) -> Box<dyn for<'a> Fn(FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 's> {
        Box::new(any_impl)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Array;

    #[test]
    fn test_any_fn() {
        // assert that any([]) is false
        let arr = LhsValue::Array(Array::new(Type::Bool));
        let mut args = vec![Ok(arr)].into_iter();
        assert_eq!(Some(LhsValue::from(false)), any_impl(&mut args));

        // assert that any([true]) is true
        let arr = LhsValue::Array(Array::from_iter([true]));
        let mut args = vec![Ok(arr)].into_iter();
        assert_eq!(Some(LhsValue::from(true)), any_impl(&mut args));

        // assert that any([false]) is false
        let arr = LhsValue::Array(Array::from_iter([false]));
        let mut args = vec![Ok(arr)].into_iter();
        assert_eq!(Some(LhsValue::from(false)), any_impl(&mut args));

        // assert that any([false, true]) is true
        let arr = LhsValue::Array(Array::from_iter([false, true]));
        let mut args = vec![Ok(arr)].into_iter();
        assert_eq!(Some(LhsValue::from(true)), any_impl(&mut args));

        // assert that any([true, true]) is true
        let arr = LhsValue::Array(Array::from_iter([true, true]));
        let mut args = vec![Ok(arr)].into_iter();
        assert_eq!(Some(LhsValue::from(true)), any_impl(&mut args));
    }

    #[test]
    #[should_panic(expected = "expected 1 argument, got 0")]
    fn test_any_fn_no_args() {
        let mut args = vec![].into_iter();
        any_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected 1 argument, got 2")]
    fn test_any_fn_too_many_args() {
        let arr = LhsValue::Array(Array::new(Type::Bool));
        let mut args = vec![Ok(arr.clone()), Ok(arr.clone())].into_iter();
        any_impl(&mut args);
    }

    #[test]
    #[should_panic]
    fn test_any_fn_bad_lhs_value() {
        let mut args = vec![Ok(LhsValue::from(false))].into_iter();
        any_impl(&mut args);
    }

    #[test]
    #[should_panic]
    fn test_any_fn_bad_lhs_arr_value() {
        let arr = LhsValue::Array(Array::from_iter(["hello"]));
        let mut args = vec![Ok(arr)].into_iter();
        any_impl(&mut args);
    }
}
