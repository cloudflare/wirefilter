use crate::{
    filter::CompiledValueResult,
    types::{ExpectedType, GetType, LhsValue, Type, TypeMismatchError},
};
use failure::Fail;
use std::{
    collections::HashSet,
    fmt::{self, Debug},
    iter::once,
};

pub(crate) struct ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = <A as Iterator>::Item>,
{
    chain: std::iter::Chain<A, B>,
    len_a: usize,
    len_b: usize,
}

impl<A, B> ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = <A as Iterator>::Item>,
{
    #[inline]
    pub(crate) fn new(a: A, b: B) -> ExactSizeChain<A, B> {
        let len_a = a.len();
        let len_b = b.len();
        ExactSizeChain {
            chain: a.chain(b),
            len_a,
            len_b,
        }
    }
}

impl<A, B> Iterator for ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = <A as Iterator>::Item>,
{
    type Item = A::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.chain.next() {
            None => None,
            Some(elem) => {
                if self.len_a > 0 {
                    self.len_a -= 1;
                } else if self.len_b > 0 {
                    self.len_b -= 1;
                }
                Some(elem)
            }
        }
    }
}

impl<A, B> ExactSizeIterator for ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = <A as Iterator>::Item>,
{
    #[inline]
    fn len(&self) -> usize {
        self.len_a + self.len_b
    }
}

/// An iterator over function arguments as [`LhsValue`]s.
pub type FunctionArgs<'i, 'a> = &'i mut dyn ExactSizeIterator<Item = CompiledValueResult<'a>>;

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

/// An error that occurs on a kind mismatch.
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "invalid argument: {:?}", msg)]
pub struct FunctionArgInvalidConstant {
    msg: String,
}

/// An error that occurs for a bad function parameter
#[derive(Debug, PartialEq, Fail)]
pub enum FunctionParamError {
    /// Function paramater value type has a different type than expected
    #[fail(display = "expected {}", _0)]
    TypeMismatch(#[cause] TypeMismatchError),
    /// Function parameter argument kind has a different kind than expected
    #[fail(display = "expected {}", _0)]
    KindMismatch(#[cause] FunctionArgKindMismatchError),
    /// Function parameter constant value is invalid
    #[fail(display = "{}", _0)]
    InvalidConstant(#[cause] FunctionArgInvalidConstant),
}

#[derive(Clone, Debug)]
pub enum FunctionDefinitionArg<'a> {
    Constant(LhsValue<'a>),
    Variable(Type),
}

impl From<&FunctionDefinitionArg<'_>> for FunctionArgKind {
    fn from(arg: &FunctionDefinitionArg<'_>) -> Self {
        match arg {
            FunctionDefinitionArg::Constant(_) => FunctionArgKind::Literal,
            FunctionDefinitionArg::Variable(_) => FunctionArgKind::Field,
        }
    }
}

impl<'a> GetType for FunctionDefinitionArg<'a> {
    fn get_type(&self) -> Type {
        match self {
            FunctionDefinitionArg::Constant(value) => value.get_type(),
            FunctionDefinitionArg::Variable(ty) => ty.clone(),
        }
    }
}

impl<'a> FunctionDefinitionArg<'a> {
    /// Check if the arg_kind of current paramater matches the expected_arg_kind
    pub fn expect_arg_kind(
        &self,
        expected_arg_kind: FunctionArgKind,
    ) -> Result<(), FunctionParamError> {
        let kind = self.into();
        if kind == expected_arg_kind {
            Ok(())
        } else {
            Err(FunctionParamError::KindMismatch(
                FunctionArgKindMismatchError {
                    expected: expected_arg_kind,
                    actual: kind,
                },
            ))
        }
    }

    /// Checks if the val_type of current parameter matches the expected_type
    pub fn expect_val_type(
        &self,
        expected_types: impl Iterator<Item = ExpectedType>,
    ) -> Result<(), FunctionParamError> {
        let ty = self.get_type();
        let mut types = HashSet::new();
        for expected_type in expected_types {
            match (&expected_type, &ty) {
                (ExpectedType::Array, Type::Array(_)) => return Ok(()),
                (ExpectedType::Array, _) => {}
                (ExpectedType::Map, Type::Map(_)) => return Ok(()),
                (ExpectedType::Map, _) => {}
                (ExpectedType::Type(val_type), _) => {
                    if ty == *val_type {
                        return Ok(());
                    }
                }
            }
            types.insert(expected_type);
        }
        Err(FunctionParamError::TypeMismatch(TypeMismatchError {
            expected: types,
            actual: ty,
        }))
    }
}

/// Trait to implement function
pub trait FunctionDefinition: Debug + Sync + Send {
    /// Given a slice of already checked parameters, checks that next_param is
    /// correct. Return the expected the parameter definition.
    fn check_arg(
        &self,
        params: &mut dyn ExactSizeIterator<Item = FunctionDefinitionArg<'_>>,
        next_param: &FunctionDefinitionArg<'_>,
    ) -> Result<(), FunctionParamError>;
    /// Function return type.
    fn return_type(
        &self,
        params: &mut dyn ExactSizeIterator<Item = FunctionDefinitionArg<'_>>,
    ) -> Type;
    /// Number of mandatory arguments and number of optional arguments
    /// (N, Some(0)) means N mandatory arguments and no optional arguments
    /// (N, None) means N mandatory arguments and unlimited optional arguments
    fn arg_count(&self) -> (usize, Option<usize>);
    /// Compile the function definition down to a closure that is going to be called
    /// during filter execution.
    fn compile<'s>(
        &'s self,
        params: &mut dyn ExactSizeIterator<Item = FunctionDefinitionArg<'_>>,
    ) -> Box<dyn for<'a> Fn(FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 's>;
}

/// Defines a mandatory function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleFunctionParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The type of its associated value.
    pub val_type: Type,
}

/// Defines an optional function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleFunctionOptParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The default value if the argument is missing.
    pub default_value: LhsValue<'static>,
}

/// Simple interface to define a function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleFunctionDefinition {
    /// List of mandatory arguments.
    pub params: Vec<SimpleFunctionParam>,
    /// List of optional arguments that can be specified after manatory ones.
    pub opt_params: Vec<SimpleFunctionOptParam>,
    /// Function return type.
    pub return_type: Type,
    /// Actual implementation that will be called at runtime.
    pub implementation: FunctionImpl,
}

impl FunctionDefinition for SimpleFunctionDefinition {
    fn check_arg(
        &self,
        params: &mut dyn ExactSizeIterator<Item = FunctionDefinitionArg<'_>>,
        next_param: &FunctionDefinitionArg<'_>,
    ) -> Result<(), FunctionParamError> {
        let index = params.len();
        if index < self.params.len() {
            let param = &self.params[index];
            next_param.expect_arg_kind(param.arg_kind)?;
            next_param.expect_val_type(once(ExpectedType::Type(param.val_type.clone())))?;
        } else if index < self.params.len() + self.opt_params.len() {
            let opt_param = &self.opt_params[index - self.params.len()];
            next_param.expect_arg_kind(opt_param.arg_kind)?;
            next_param
                .expect_val_type(once(ExpectedType::Type(opt_param.default_value.get_type())))?;
        } else {
            unreachable!();
        }
        Ok(())
    }

    fn return_type(&self, _: &mut dyn ExactSizeIterator<Item = FunctionDefinitionArg<'_>>) -> Type {
        self.return_type.clone()
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (self.params.len(), Some(self.opt_params.len()))
    }

    fn compile<'s>(
        &'s self,
        _: &mut dyn ExactSizeIterator<Item = FunctionDefinitionArg<'_>>,
    ) -> Box<dyn for<'a> Fn(FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 's> {
        Box::new(move |args| {
            let opts_args = &self.opt_params[(args.len() - self.params.len())..];
            self.implementation.execute(&mut ExactSizeChain::new(
                args,
                opts_args
                    .iter()
                    .map(|opt_arg| Ok(opt_arg.default_value.to_owned())),
            ))
        })
    }
}
