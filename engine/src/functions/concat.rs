use crate::{
    Array, ExpectedType, FunctionArgs, FunctionDefinition, FunctionDefinitionContext,
    FunctionParam, FunctionParamError, GetType, LhsValue, ParserSettings, Type,
};
use std::{borrow::Cow, iter::once};

/// A function which, given one or more arrays or byte-strings, returns the
/// concatenation of each of them.
///
/// It expects at least two arguments and will error if given no arguments
/// or the arguments are of different types.
#[derive(Debug, Default)]
pub struct ConcatFunction {}

impl ConcatFunction {
    /// Creates a new definition for the `concat` function.
    pub const fn new() -> Self {
        Self {}
    }
}

fn concat_array<'a>(mut accumulator: Array<'a>, args: FunctionArgs<'_, 'a>) -> Array<'a> {
    for arg in args {
        match arg {
            Ok(LhsValue::Array(value)) => accumulator.try_extend(value).unwrap(),
            Err(Type::Array(_)) => (),
            _ => (),
        };
    }
    accumulator
}

fn concat_bytes<'a>(mut accumulator: Cow<'a, [u8]>, args: FunctionArgs<'_, 'a>) -> Cow<'a, [u8]> {
    for arg in args {
        match arg {
            Ok(LhsValue::Bytes(value)) => accumulator.to_mut().extend(value.iter()),
            Err(Type::Bytes) => (),
            _ => (),
        }
    }
    accumulator
}

pub(crate) const EXPECTED_TYPES: [ExpectedType; 2] =
    [ExpectedType::Array, ExpectedType::Type(Type::Bytes)];

impl FunctionDefinition for ConcatFunction {
    fn check_param(
        &self,
        _: &ParserSettings,
        params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        next_param: &FunctionParam<'_>,
        _: Option<&mut FunctionDefinitionContext>,
    ) -> Result<(), FunctionParamError> {
        match params.next() {
            // the next argument must have the same type
            Some(param) => {
                next_param.expect_val_type(once(param.get_type().into()))?;
            }
            None => {
                next_param.expect_val_type(EXPECTED_TYPES.iter().cloned())?;
            }
        }

        Ok(())
    }

    fn return_type(
        &self,
        params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        _: Option<&FunctionDefinitionContext>,
    ) -> Type {
        params.next().unwrap().get_type()
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (2, None)
    }

    fn compile<'s>(
        &'s self,
        _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        _: Option<FunctionDefinitionContext>,
    ) -> Box<dyn for<'a> Fn(FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 's> {
        Box::new(|args| {
            while let Some(arg) = args.next() {
                match arg {
                    Ok(LhsValue::Array(array)) => {
                        return Some(LhsValue::Array(concat_array(array, args)))
                    }
                    Ok(LhsValue::Bytes(bytes)) => {
                        return Some(LhsValue::Bytes(concat_bytes(bytes, args)))
                    }
                    Err(_) => (),
                    _ => unreachable!(),
                }
            }
            None
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeMismatchError;

    pub static CONCAT_FN: ConcatFunction = ConcatFunction::new();

    #[test]
    fn test_concat_bytes() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"hello"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"world"))),
        ]
        .into_iter();
        assert_eq!(
            Some(LhsValue::Bytes(Cow::Borrowed(b"helloworld"))),
            CONCAT_FN.compile(&mut std::iter::empty(), None)(&mut args)
        );
    }

    #[test]
    fn test_concat_many_bytes() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"hello"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"world"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"hello2"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"world2"))),
        ]
        .into_iter();
        assert_eq!(
            Some(LhsValue::Bytes(Cow::Borrowed(b"helloworldhello2world2"))),
            CONCAT_FN.compile(&mut std::iter::empty(), None)(&mut args)
        );
    }

    #[test]
    fn test_concat_function() {
        let arg1 = LhsValue::Array(Array::from_iter([1, 2, 3]));
        let arg2 = LhsValue::Array(Array::from_iter([4, 5, 6]));
        let mut args = vec![Ok(arg1), Ok(arg2)].into_iter();
        assert_eq!(
            Some(LhsValue::Array(Array::from_iter([1, 2, 3, 4, 5, 6]))),
            CONCAT_FN.compile(&mut std::iter::empty(), None)(&mut args)
        );
    }

    #[test]
    #[should_panic]
    fn test_concat_function_bad_arg_type() {
        let mut args = vec![Ok(LhsValue::from(2))].into_iter();
        CONCAT_FN.compile(&mut std::iter::empty(), None)(&mut args);
    }

    #[test]
    fn test_concat_function_check_param() {
        let settings = ParserSettings::default();

        let arg1 = FunctionParam::Variable(Type::Array(Type::Bytes.into()));
        assert_eq!(
            Ok(()),
            CONCAT_FN.check_param(&settings, &mut vec![].into_iter(), &arg1, None)
        );

        let arg2 = FunctionParam::Variable(Type::Array(Type::Bytes.into()));
        assert_eq!(
            Ok(()),
            CONCAT_FN.check_param(&settings, &mut vec![arg1.clone()].into_iter(), &arg2, None)
        );

        let arg3 = FunctionParam::Variable(Type::Int);

        assert_eq!(
            Err(FunctionParamError::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Type::Bytes.into()).into(),
                actual: Type::Int,
            })),
            CONCAT_FN.check_param(
                &settings,
                &mut vec![arg1.clone(), arg2.clone()].into_iter(),
                &arg3,
                None
            )
        );

        assert_eq!(
            Err(FunctionParamError::TypeMismatch(TypeMismatchError {
                expected: [ExpectedType::Array, ExpectedType::Type(Type::Bytes)]
                    .into_iter()
                    .into(),
                actual: Type::Int,
            })),
            CONCAT_FN.check_param(&settings, &mut vec![].into_iter(), &arg3, None)
        );

        let arg_literal = FunctionParam::Variable(Type::Bytes);

        assert_eq!(
            Ok(()),
            CONCAT_FN.check_param(
                &settings,
                &mut vec![arg_literal.clone()].into_iter(),
                &arg_literal,
                None
            )
        );
    }
}
