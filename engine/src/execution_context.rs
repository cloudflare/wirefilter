use scheme::Scheme;
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

    pub fn get_field_value_unchecked(&self, index: usize) -> &LhsValue<'e> {
        self.values[index].as_ref().unwrap_or_else(|| {
            panic!(
                "Field {} was registered but not given a value",
                self.scheme.get_field_name(index).unwrap()
            );
        })
    }

    pub fn set_field_value(&mut self, name: &str, value: LhsValue<'e>) {
        let field = self.scheme.get_field_index(name).unwrap();

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
