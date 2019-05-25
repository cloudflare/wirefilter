use crate::{
    filter::CompiledValueResult,
    types::{GetType, LhsValue, Type, TypeMismatchError},
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

/// FunctionArgKind is the kind of argument that can be passed to a function.
/// A function argument can be either a Literal or a Field.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum FunctionArgKind {
    /// The function argument is a Field
    Field,
    /// The function argument is a Literal
    Literal,
}

/// FunctionArgCount is the number of required and optional arguments
/// for a function.
pub struct FunctionArgCount {
    /// The number of required arguments
    pub required: usize,
    /// The number if optional arguments
    pub optional: FunctionOptArgCount,
}

impl FunctionArgCount {
    /// The total number of arguments that can be passed to the function,
    /// including optional arguments.
    pub fn count(&self) -> usize {
        self.required
            + match self.optional {
                FunctionOptArgCount::Fixed(n) => n,
                FunctionOptArgCount::Unlimited => 0,
            }
    }
}

/// FunctionOptArgCount is the number of optional arguments for a function.
/// A function can have a fixed number or unlimited optional arguments.
pub enum FunctionOptArgCount {
    Fixed(usize),
    Unlimited,
}

impl FunctionOptArgCount {
    pub fn is_fixed(&self) -> bool {
        match self {
            FunctionOptArgCount::Fixed(_) => true,
            _ => false,
        }
    }

    pub fn is_unlimited(&self) -> bool {
        match self {
            FunctionOptArgCount::Unlimited => true,
            _ => false,
        }
    }
}

/// FunctionArgCountMismatchError occurs when a function expects N arguments
/// but receives a number of arguments other than N.
///
/// For example, a len function might return a FunctionArgCountMismatchError
/// when it expects a single argument but instead received no or more than
/// one argument.
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "expected {:?} arguments, but got {:?}", expected, actual)]
pub struct FunctionArgCountMismatchError {
    /// The expected number of arguments
    pub expected: usize,
    /// The provided number of arguments
    pub actual: usize,
}

/// FunctionArgKindMismatchError occurs when a function expects one variant
/// of FunctionArgKind but the argument is of another.
///
/// For example, a function would return a FunctionArgKindMismatchError when
/// a parameter expects a Field as its argument but instead received an argument
/// that is a Literal.
#[derive(Debug, PartialEq, Fail)]
#[fail(
    display = "expected argument of kind {:?}, but got {:?}",
    expected, actual
)]
pub struct FunctionArgKindMismatchError {
    /// The expected FunctionArgKind
    pub expected: FunctionArgKind,
    /// The provided FunctionArgKind
    pub actual: FunctionArgKind,
}

/// InvalidFunctionArgsError occurs when one or more arguments for a function's
/// parameters do not match the function's signature.
pub enum InvalidFunctionArgError {
    /// An incorrect number of arguments have been passed to the function
    CountMismatch(FunctionArgCountMismatchError),
    /// The argument does not match the FunctionArgKind of the parameter
    KindMismatch(FunctionArgKindMismatchError),
    /// The argument does not match the type of the parameter
    TypeMismatch(TypeMismatchError),
}

/// FunctionParam represents a required function argument.
///
/// It annotates the kind of argument (i.e. whether the argument is a Field
/// or a Literal) and one or more types that may be passed as arguments for
/// this parameter.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionParam {
    /// the kind of argument
    pub arg_kind: FunctionArgKind,
    /// one or more types that may be passed as arguments for this parameter
    pub arg_type: Type,
}

/// FunctionOptParam is an optional function argument. An optional argument
/// can be either a Field or a Literal and has a default value if no
/// argument is specified.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionOptParam {
    /// The FunctionArgKind
    pub arg_kind: FunctionArgKind,
    /// The default value if no argument is specified
    pub default_value: LhsValue<'static>,
}

/// FunctionDefinition is the interface for a function.
pub trait FunctionDefinition: Debug + Sync + Send {
    /// Returns the number of required and optional arguments for the function.
    fn arg_count(&self) -> FunctionArgCount;

    /// Gets the default value for the optional argument.
    fn default_value<'e>(&self, index: usize) -> Option<LhsValue<'e>>;

    /// Execute the function.
    fn execute<'a>(&self, args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>>;

    /// Gets the return type of the function.
    fn return_type(&self, params: &mut ExactSizeIterator<Item = FunctionParam>) -> Type;

    /// Given an iterator of checked parameters, checks that the next parameter
    /// is correct or returns an error.
    ///
    /// The iterator is empty when the parameter being checked is the first
    /// parameter in the function definition, or equally when a function only
    /// accepts a single argument.
    fn validate(
        &self,
        checked_params: &mut ExactSizeIterator<Item = FunctionParam>,
        next: &FunctionParam,
    ) -> Result<FunctionParam, InvalidFunctionArgError>;
}

/// Defines a function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Function {
    /// List of mandatory arguments.
    pub params: Vec<FunctionParam>,
    /// List of optional arguments.
    pub opt_params: Vec<FunctionOptParam>,
    /// The return type of the function.
    pub return_type: Type,
    /// The function implementation called at runtime.
    pub implementation: FunctionImpl,
}

impl FunctionDefinition for Function {
    fn arg_count(&self) -> FunctionArgCount {
        FunctionArgCount {
            required: self.params.len(),
            optional: FunctionOptArgCount::Fixed(self.opt_params.len()),
        }
    }

    fn default_value<'e>(&self, index: usize) -> Option<LhsValue<'e>> {
        self.opt_params
            .get(index - self.params.len())
            .map(|opt_param| opt_param.default_value.to_owned())
    }

    fn validate(
        &self,
        checked_params: &mut ExactSizeIterator<Item = FunctionParam>,
        _: &FunctionParam,
    ) -> Result<FunctionParam, InvalidFunctionArgError> {
        let index = checked_params.len();
        if index < self.params.len() {
            // TODO: change unwrap to err
            return Ok(self.params.get(index).cloned().unwrap());
        } else if index < self.params.len() + self.opt_params.len() {
            // TODO: change unwrap to err
            return Ok(self
                .opt_params
                .get(index - self.params.len())
                .map(|opt_param| FunctionParam {
                    arg_kind: opt_param.arg_kind,
                    arg_type: opt_param.default_value.get_type(),
                })
                .unwrap());
        }
        Err(InvalidFunctionArgError::CountMismatch(
            FunctionArgCountMismatchError {
                expected: index + 1,
                actual: checked_params.len(),
            },
        ))
    }

    fn execute<'a>(&self, args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        self.implementation.execute(args)
    }

    fn return_type(&self, _: &mut ExactSizeIterator<Item = FunctionParam>) -> Type {
        self.return_type.clone()
    }
}
