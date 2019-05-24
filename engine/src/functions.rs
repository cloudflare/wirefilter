use crate::{
    filter::CompiledValueResult,
    types::{ExpectedType, GetType, LhsValue, Type, TypeMismatchError},
};
use failure::Fail;
use std::fmt::{self, Debug};

/// An iterator over function arguments as [`LhsValue`]s.
pub type FunctionArgs<'i, 'a> = &'i mut dyn Iterator<Item = CompiledValueResult<'a>>;

type FunctionPtr = for<'a> fn(FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>>;

/// Wrapper around a function pointer providing the runtime implementation.
#[derive(Clone)]
pub struct FunctionImpl(FunctionPtr);

impl FunctionImpl {
    /// Creates a new wrapper around a function pointer.
    pub fn new(func: FunctionPtr) -> Self {
        Self(func)
    }

    /// Calls the wrapped function pointer.
    pub fn execute<'a>(&self, args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        (self.0)(args)
    }
}

impl fmt::Debug for FunctionImpl {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_tuple("FunctionImpl")
            .field(&(self.0 as *const ()))
            .finish()
    }
}

impl PartialEq for FunctionImpl {
    fn eq(&self, other: &FunctionImpl) -> bool {
        self.0 as *const () == other.0 as *const ()
    }
}

impl Eq for FunctionImpl {}

/// Defines what kind of argument a function expects.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum FunctionArgKind {
    /// Allow only literal as argument.
    Literal,
    /// Allow only field as argument.
    Field,
}

/// An error that occurs on a kind mismatch.
#[derive(Debug, PartialEq, Fail)]
#[fail(
    display = "expected argument of kind {:?}, but got {:?}",
    expected, actual
)]
pub struct FunctionArgKindMismatchError {
    /// Expected value type.
    pub expected: FunctionArgKind,
    /// Provided value type.
    pub actual: FunctionArgKind,
}

/// An error that occurs for a bad function parameter
#[derive(Debug, PartialEq, Fail)]
pub enum FunctionParamError {
    /// Function paramater value type has a different type than expected
    #[fail(display = "expected {}", _0)]
    TypeMismatch(#[cause] TypeMismatchError),
    /// Function parameter argument kind has a different kind than expected
    #[fail(display = "expected {}", _0)]
    FunctionArgKindMismatch(#[cause] FunctionArgKindMismatchError),
}

/// Defines a mandatory function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The type of its associated value.
    pub val_type: Type,
}

impl FunctionParam {
    /// Check if the arg_kind of current paramater matches the expected_arg_kind
    pub fn expect_arg_kind(
        &self,
        expected_arg_kind: FunctionArgKind,
    ) -> Result<(), FunctionParamError> {
        if self.arg_kind == expected_arg_kind {
            Ok(())
        } else {
            Err(FunctionParamError::FunctionArgKindMismatch(
                FunctionArgKindMismatchError {
                    expected: expected_arg_kind,
                    actual: self.arg_kind,
                },
            ))
        }
    }

    /// Checks if the val_type of current parameter matches the expected_type
    pub fn expect_val_type(&self, expected_type: ExpectedType) -> Result<(), FunctionParamError> {
        match (&expected_type, &self.val_type) {
            (ExpectedType::Array, Type::Array(_)) => return Ok(()),
            (ExpectedType::Array, _) => {}
            (ExpectedType::Map, Type::Map(_)) => return Ok(()),
            (ExpectedType::Map, _) => {}
            (ExpectedType::Type(val_type), _) => {
                if self.val_type == *val_type {
                    return Ok(());
                }
            }
        }
        Err(FunctionParamError::TypeMismatch(TypeMismatchError {
            expected: expected_type.clone(),
            actual: self.val_type.clone(),
        }))
    }
}

/// Defines an optional function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionOptParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The default value if the argument is missing.
    pub default_value: LhsValue<'static>,
}

/// Trait to implement function
pub trait FunctionDefinition: Debug + Sync + Send {
    /// Given a slice of already checked parameters, checks that next_param is
    /// correct. Return the expected the parameter definition.
    fn check_param(
        &self,
        params: &mut ExactSizeIterator<Item = FunctionParam>,
        next_param: &FunctionParam,
    ) -> Result<(), FunctionParamError>;
    /// Function return type.
    fn return_type(&self, params: &mut ExactSizeIterator<Item = FunctionParam>) -> Type;
    /// Number of mandatory arguments and number of optional arguments
    /// (N, Some(0)) means N mandatory arguments and no optional arguments
    /// (N, None) means N mandatory arguments and unlimited optional arguments
    fn arg_count(&self) -> (usize, Option<usize>);
    /// Get default value for optional arguments.
    fn default_value<'e>(&self, index: usize) -> Option<LhsValue<'e>>;
    /// Execute the real implementation.
    fn execute<'a>(&self, args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>>;
}

/// Defines a function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Function {
    /// List of mandatory arguments.
    pub params: Vec<FunctionParam>,
    /// List of optional arguments that can be specified after manatory ones.
    pub opt_params: Vec<FunctionOptParam>,
    /// Function return type.
    pub return_type: Type,
    /// Actual implementation that will be called at runtime.
    pub implementation: FunctionImpl,
}

impl FunctionDefinition for Function {
    fn check_param(
        &self,
        params: &mut ExactSizeIterator<Item = FunctionParam>,
        next_param: &FunctionParam,
    ) -> Result<(), FunctionParamError> {
        let index = params.len();
        if index < self.params.len() {
            let param = &self.params[index];
            next_param.expect_arg_kind(param.arg_kind)?;
            next_param.expect_val_type(ExpectedType::Type(param.val_type.clone()))?;
        } else if index < self.params.len() + self.opt_params.len() {
            let opt_param = &self.opt_params[index - self.params.len()];
            next_param.expect_arg_kind(opt_param.arg_kind)?;
            next_param.expect_val_type(ExpectedType::Type(opt_param.default_value.get_type()))?;
        } else {
            unreachable!();
        }
        Ok(())
    }

    fn return_type(&self, _: &mut ExactSizeIterator<Item = FunctionParam>) -> Type {
        self.return_type.clone()
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (self.params.len(), Some(self.opt_params.len()))
    }

    fn default_value<'e>(&self, index: usize) -> Option<LhsValue<'e>> {
        self.opt_params
            .get(index - self.params.len())
            .map(|opt_param| opt_param.default_value.to_owned())
    }

    fn execute<'a>(&self, args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        self.implementation.execute(args)
    }
}
