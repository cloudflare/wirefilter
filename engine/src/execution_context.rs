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
            panic!("Field {} was registered but not given a value");
        })
    }

    pub fn set_field_value(&mut self, name: &str, value: LhsValue<'e>) {
        let (field, prev_ty) = self.scheme.get_field_entry(name).unwrap();

        let cur_ty = value.get_type();

        if prev_ty != cur_ty {
            panic!(
                "Field {} was previously registered with type {:?} but now contains {:?}",
                name, prev_ty, cur_ty
            );
        }

        self.values[field.index()] = Some(value);
    }
}
