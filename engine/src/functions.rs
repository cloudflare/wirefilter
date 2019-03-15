use std::fmt;
use types::{LhsValue, RhsValue, Type};

type FunctionPtr = for<'a> fn(&[LhsValue<'a>]) -> LhsValue<'a>;

/// Wrapper around a function pointer providing the runtime implemetation.
pub struct FunctionImpl(FunctionPtr);

impl FunctionImpl {
    /// Creates a new wrapper around a function pointer.
    pub fn new(func: FunctionPtr) -> Self {
        Self(func)
    }

    /// Calls the wrapped function pointer.
    pub fn execute<'a>(&self, args: &[LhsValue<'a>]) -> LhsValue<'a> {
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FunctionArgKind {
    /// Allow only literal as argument.
    Literal,
    /// Allow only field as argument.
    Field,
}

/// Defines a mandatory function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionArg {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The type of its associated value.
    pub val_type: Type,
}

/// Defines an optional function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionOptArg {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The default value if the argument is missing.
    pub value: RhsValue,
}

/// Defines a function.
#[derive(Debug, PartialEq, Eq)]
pub struct Function {
    /// List of mandatory arguments.
    pub args: Vec<FunctionArg>,
    /// List of optional arguments that can be specified after manatory ones.
    pub opt_args: Vec<FunctionOptArg>,
    /// Function return type.
    pub return_type: Type,
    /// Actual implementation that will be called at runtime.
    pub implementation: FunctionImpl,
}
