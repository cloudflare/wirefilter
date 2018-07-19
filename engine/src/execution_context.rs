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
        let (field, prev_ty) = self
            .scheme
            .get_field_entry(name)
            .unwrap_or_else(|| panic!("Field {} was not found in associated scheme", name));

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

#[cfg(test)]
mod tests {
    use super::*;
    use types::Type;

    use std::net::{IpAddr, Ipv6Addr};

    fn assert_filter(execution_context: &ExecutionContext, filter: &str, expect: bool) {
        let filter = execution_context.scheme.parse(filter).unwrap();
        assert_eq!(filter.execute(execution_context), expect);
    }

    #[test]
    fn compare_ip() {
        let mut scheme = Scheme::default();
        scheme.add_field("ip".to_owned(), Type::Ip);

        let mut execution_context = ExecutionContext::new(&scheme);
        execution_context.set_field_value("ip", LhsValue::Ip(IpAddr::V6(Ipv6Addr::from(2))));

        assert_filter(&execution_context, "ip > ::1", true);
        assert_filter(&execution_context, "ip <= ::3", true);
        assert_filter(&execution_context, "ip > ::2", false);
        assert_filter(&execution_context, "ip < 127.0.0.3", false);
        assert_filter(
            &execution_context,
            "ip >= 127.0.0.1 and ip < 127.0.0.255",
            false,
        );
        assert_filter(&execution_context, "ip == 127.0.0.0/8", false);
        assert_filter(&execution_context, "ip != 127.0.0.0/8", true);
    }

    #[test]
    fn check_bool() {
        let mut scheme = Scheme::default();
        scheme.add_field("true".to_owned(), Type::Bool);
        scheme.add_field("false".to_owned(), Type::Bool);

        let mut execution_context = ExecutionContext::new(&scheme);
        execution_context.set_field_value("true", LhsValue::Bool(true));
        execution_context.set_field_value("false", LhsValue::Bool(false));

        assert_filter(&execution_context, "true", true);
        assert_filter(&execution_context, "not true", false);
        assert_filter(&execution_context, "false", false);
        assert_filter(&execution_context, "!false", true);
    }
}
