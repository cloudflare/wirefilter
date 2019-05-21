use crate::{
    filter::CompiledValueResult,
    types::{GetType, LhsValue, Type},
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

/// Defines a mandatory function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The type of its associated value.
    pub val_type: Type,
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
    ) -> Option<FunctionParam>;
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
        _: &FunctionParam,
    ) -> Option<FunctionParam> {
        let index = params.len();
        if index < self.params.len() {
            return self.params.get(index).cloned();
        } else if index < self.params.len() + self.opt_params.len() {
            return self
                .opt_params
                .get(index - self.params.len())
                .map(|opt_param| FunctionParam {
                    arg_kind: opt_param.arg_kind,
                    val_type: opt_param.default_value.get_type(),
                });
        }
        None
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
