use scheme::{Field, Scheme};
use types::{GetType, LhsValue};

/// An execution context stores an associated [`Scheme`] and a set of runtime
/// values to execute [`Filter`](::Filter) against.
///
/// It acts as a map in terms of public API, but provides a constant-time
/// index-based access to values for a filter during execution.
pub struct ExecutionContext<'e> {
    scheme: &'e Scheme,
    values: Box<[Option<LhsValue<'e>>]>,
}

impl<'e> ExecutionContext<'e> {
    /// Creates an execution context associated with a given scheme.
    ///
    /// This scheme will be used for resolving any field names and indices.
    pub fn new<'s: 'e>(scheme: &'s Scheme) -> Self {
        ExecutionContext {
            scheme,
            values: vec![None; scheme.get_field_count()].into(),
        }
    }

    /// Returns an associated scheme.
    pub fn scheme(&self) -> &'e Scheme {
        self.scheme
    }

    pub(crate) fn get_field_value_unchecked(&self, field: Field<'e>) -> &LhsValue<'e> {
        // This is safe because this code is reachable only from Filter::execute
        // which already performs the scheme compatibility check, but check that
        // invariant holds in the future at least in the debug mode.
        debug_assert!(self.scheme() == field.scheme());

        self.values[field.index()].as_ref().unwrap_or_else(|| {
            panic!(
                "Field {} was registered but not given a value",
                field.name()
            );
        })
    }

    /// Sets a runtime value for a given field name.
    ///
    /// This method assumes that caller takes care to pass only valid values
    /// as defined in the scheme, and will panic if such fields don't exist
    /// or the type of the value mismatches with the registered one.
    pub fn set_field_value<'v: 'e, V: Into<LhsValue<'v>>>(&mut self, name: &str, value: V) {
        let field = self.scheme.get_field_index(name).unwrap();
        let value = value.into();

        let field_ty = field.get_type();
        let value_ty = value.get_type();

        if field_ty != value_ty {
            panic!(
                "Field {} was previously registered with type {:?} but tried to set to {:?}",
                name, field_ty, value_ty
            );
        }

        self.values[field.index()] = Some(value);
    }
}
