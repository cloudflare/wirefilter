use std::fmt;
use types::{LhsValue, Type};

type FunctionPtr = for<'a> fn(&[LhsValue<'a>]) -> LhsValue<'a>;

/// Wrapper around a function pointer providing the runtime implemetation.
#[derive(Clone)]
pub(crate) struct FunctionImpl(FunctionPtr);

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
pub(crate) struct FunctionParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The type of its associated value.
    pub val_type: Type,
}

/// Defines an optional function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct FunctionOptParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The default value if the argument is missing.
    pub default_value: LhsValue<'static>,
}

/// Defines a function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Function {
    /// List of mandatory arguments.
    pub(crate) params: Vec<FunctionParam>,
    /// List of optional arguments that can be specified after manatory ones.
    pub(crate) opt_params: Vec<FunctionOptParam>,
    /// Function return type.
    pub(crate) return_type: Type,
    /// Actual implementation that will be called at runtime.
    pub(crate) implementation: FunctionImpl,
}

impl Function {
    /// Instanciate a new Function definition
    pub fn new(return_type: Type, function_ptr: FunctionPtr) -> Self {
        Self {
            params: Default::default(),
            opt_params: Default::default(),
            return_type,
            implementation: FunctionImpl::new(function_ptr),
        }
    }

    /// Add a mandatory parameter to a Function definition
    pub fn param(mut self, arg_kind: FunctionArgKind, val_type: Type) -> Self {
        self.params.push(FunctionParam { arg_kind, val_type });
        self
    }

    /// Add an optional parameter to a Function definition
    pub fn opt_param(
        mut self,
        arg_kind: FunctionArgKind,
        default_value: LhsValue<'static>,
    ) -> Self {
        self.opt_params.push(FunctionOptParam {
            arg_kind,
            default_value,
        });
        self
    }
}
