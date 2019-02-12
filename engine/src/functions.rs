use std::fmt;
use types::{LhsValue, Type};

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

/// Defines a function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FunctionArg {
    /// Allow only literal as argument.
    Literal(Type),
    /// Allow only field as argument.
    Field(Type),
}

/// Defines a function.
#[derive(Debug, PartialEq, Eq)]
pub struct Function {
    /// List of function arguments.
    pub args: Vec<FunctionArg>,
    /// Function return type.
    pub return_type: Type,
    /// Actual implementation that will be called at runtime.
    pub implementation: FunctionImpl,
}
