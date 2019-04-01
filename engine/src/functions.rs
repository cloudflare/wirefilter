use crate::types::{LhsValue, Type};
use std::fmt;

type FunctionPtr = for<'a> fn(&mut dyn Iterator<Item = LhsValue<'a>>) -> LhsValue<'a>;

/// Wrapper around a function pointer providing the runtime implemetation.
#[derive(Clone)]
pub struct FunctionImpl(FunctionPtr);

impl FunctionImpl {
    /// Creates a new wrapper around a function pointer.
    pub fn new(func: FunctionPtr) -> Self {
        Self(func)
    }

    /// Calls the wrapped function pointer.
    pub fn execute<'a>(&self, args: impl IntoIterator<Item = LhsValue<'a>>) -> LhsValue<'a> {
        (self.0)(&mut args.into_iter())
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FunctionArgKind {
    /// Allow only literal as argument.
    Literal,
    /// Allow only field as argument.
    Field,
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
