use super::FunctionDefinition;
use dyn_clone::DynClone;
use dyn_eq::DynEq;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt::Debug;

/// A value that can be stored as settings for a function definition.
pub trait FunctionSettingsValue: Any + Debug + DynClone + DynEq + Send + Sync {}

impl<T> FunctionSettingsValue for T where T: Any + Clone + Debug + Eq + Send + Sync {}

dyn_clone::clone_trait_object!(FunctionSettingsValue);
dyn_eq::eq_trait_object!(FunctionSettingsValue);

/// Function-specific settings used while parsing expressions.
///
/// Settings are associated with the concrete function-definition type. If the same definition
/// type is registered in a scheme under multiple names, every registration uses the same settings.
/// Setting another value for the same definition type replaces the previous value.
///
/// # Example
///
/// ```
/// # use wirefilter::{CompiledFunction, FunctionDefinition, FunctionDefinitionContext};
/// # use wirefilter::{FunctionParam, FunctionParamError, FunctionSettings, ParserSettings, Type};
///
/// #[derive(Clone, Debug, Eq, PartialEq)]
/// struct ConcatSettings {
///     max_len: usize,
/// }
///
/// #[derive(Debug)]
/// struct ConcatFunction;
///
/// impl FunctionDefinition for ConcatFunction {
///     type Settings = ConcatSettings;
///
/// #   fn check_param(
/// #       &self,
/// #       _: &ParserSettings,
/// #       _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
/// #       _: &FunctionParam<'_>,
/// #       _: Option<&mut FunctionDefinitionContext>,
/// #   ) -> Result<(), FunctionParamError> { unreachable!() }
/// #   fn return_type(
/// #       &self,
/// #       _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
/// #       _: Option<&FunctionDefinitionContext>,
/// #   ) -> Type { Type::Bytes }
/// #   fn arg_count(&self) -> (usize, Option<usize>) { (0, Some(0)) }
/// #   fn compile(
/// #       &self,
/// #       _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
/// #       _: Option<FunctionDefinitionContext>,
/// #   ) -> CompiledFunction { Box::new(|_| None) }
/// }
///
/// let mut function_settings = FunctionSettings::default();
/// function_settings.set::<ConcatFunction>(ConcatSettings { max_len: 4096 });
///
/// assert_eq!(
///     function_settings.get::<ConcatFunction>(),
///     Some(&ConcatSettings { max_len: 4096 }),
/// );
///
/// let parser_settings = ParserSettings {
///     function_settings,
///     ..ParserSettings::default()
/// };
/// ```
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FunctionSettings {
    values: HashMap<TypeId, Box<dyn FunctionSettingsValue>>,
}

impl FunctionSettings {
    /// Sets the settings associated with every registration of function definition type `F`.
    ///
    /// This replaces any previously configured value for `F`.
    pub fn set<F: FunctionDefinition + 'static>(&mut self, value: F::Settings) {
        self.values.insert(TypeId::of::<F>(), Box::new(value));
    }

    /// Returns the settings associated with function definition type `F`, if configured.
    pub fn get<F: FunctionDefinition + 'static>(&self) -> Option<&F::Settings> {
        self.values.get(&TypeId::of::<F>()).and_then(|value| {
            let value: &(dyn Any + Send + Sync) = value.as_ref();
            value.downcast_ref()
        })
    }
}
