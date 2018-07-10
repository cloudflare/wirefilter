use filter::{Filter, FilterField, FilterOp};
use op::{CombiningOp, UnaryOp, UnsignedOp};
use scheme::Scheme;
use types::{GetType, LhsValue, Type};

pub struct ExecutionContext<'a> {
    scheme: &'a Scheme,
    values: Vec<Option<LhsValue<'a>>>,
}

macro_rules! cast_field {
    ($field:ident, $lhs:ident, $ty:ident) => {
        match $lhs {
            LhsValue::$ty(value) => value,
            _ => unreachable!(),
        }
    };
}

impl<'a> ExecutionContext<'a> {
    pub fn new(scheme: &'a Scheme) -> Self {
        ExecutionContext {
            scheme,
            values: vec![None; scheme.get_field_count()],
        }
    }

    fn get_scheme_entry(&self, name: &str) -> (usize, &'a str, Type) {
        self.scheme
            .get_field_entry(name)
            .unwrap_or_else(|| panic!("Could not find previously registered field {}", name))
    }

    pub fn set_field_value(&mut self, name: &str, value: LhsValue<'a>) {
        let (index, name, prev_ty) = self.get_scheme_entry(name);
        let cur_ty = value.get_type();

        if prev_ty != cur_ty {
            panic!(
                "Field {} was previously registered with type {:?} but now contains {:?}",
                name, prev_ty, cur_ty
            );
        }

        self.values[index] = Some(value);
    }

    pub fn execute(&self, filter: &Filter) -> bool {
        match filter {
            Filter::Op(FilterField { field, index }, op) => {
                let lhs = self.values[*index].as_ref().unwrap_or_else(|| {
                    panic!("Field {:?} was registered but not given a value", field)
                });

                match op {
                    FilterOp::Ordering(op, rhs) => lhs.try_cmp(*op, rhs).unwrap(),
                    FilterOp::Unsigned(UnsignedOp::BitwiseAnd, rhs) => {
                        cast_field!(field, lhs, Unsigned) & rhs != 0
                    }
                    FilterOp::Matches(regex) => regex.is_match(cast_field!(field, lhs, Bytes)),
                    FilterOp::OneOf(values) => values.try_contains(lhs).unwrap(),
                }
            }
            Filter::Combine(op, filters) => {
                let mut results = filters.iter().map(|filter| self.execute(filter));
                match op {
                    CombiningOp::And => results.all(|res| res),
                    CombiningOp::Or => results.any(|res| res),
                    CombiningOp::Xor => results.fold(false, |acc, res| acc ^ res),
                }
            }
            Filter::Unary(UnaryOp::Not, filter) => !self.execute(filter),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::net::{IpAddr, Ipv6Addr};

    fn assert_filter(execution_context: &ExecutionContext, filter: &str, expect: bool) {
        let filter = execution_context.scheme.parse(filter).unwrap();
        assert_eq!(execution_context.execute(&filter), expect);
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
