use scheme::{Field, Scheme};
use types::{GetType, LhsValue};

pub struct ExecutionContext<'e> {
    scheme: &'e Scheme,
    values: Box<[Option<LhsValue<'e>>]>,
}

impl<'e> ExecutionContext<'e> {
    pub fn new<'s: 'e>(scheme: &'s Scheme) -> Self {
        ExecutionContext {
            scheme,
            values: vec![None; scheme.get_field_count()].into(),
        }
    }

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
