use filter::{Filter, FilterOp};
use fnv::FnvBuildHasher;
use indexmap::IndexMap;
use op::{CombiningOp, UnaryOp, UnsignedOp};
use types::{GetType, LhsValue, Type};

use std::iter::FromIterator;

#[derive(Default)]
pub struct ExecutionContext<'a> {
    values: IndexMap<&'a str, LhsValue<'a>, FnvBuildHasher>,
}

impl<'a> FromIterator<(&'a str, LhsValue<'a>)> for ExecutionContext<'a> {
    fn from_iter<I: IntoIterator<Item = (&'a str, LhsValue<'a>)>>(iter: I) -> Self {
        ExecutionContext {
            values: IndexMap::from_iter(iter),
        }
    }
}

macro_rules! panic_type {
    ($field:expr, $actual:expr, $expected:expr) => {
        panic!(
            "Field {:?} was previously registered with type {:?} but now contains {:?}",
            $field,
            $expected.get_type(),
            $actual.get_type()
        );
    };
}

macro_rules! cast_field {
    ($field:ident, $lhs:ident, $ty:ident) => {
        match $lhs {
            &LhsValue::$ty(ref value) => value,
            other => panic_type!($field, other, Type::$ty),
        }
    };
}

impl<'a> ExecutionContext<'a> {
    fn get_field_value(&self, field_name: &str) -> &LhsValue<'a> {
        self.values
            .get(field_name)
            .unwrap_or_else(|| panic!("Could not find previously registered field {}", field_name))
    }

    pub fn set_field_value(&mut self, field_name: &'a str, value: LhsValue<'a>) {
        self.values.insert(field_name, value);
    }

    pub fn execute(&self, filter: &Filter) -> bool {
        match *filter {
            Filter::Op(field, ref op) => {
                let lhs = self.get_field_value(field.path());

                match *op {
                    FilterOp::Ordering(op, ref rhs) => lhs.try_cmp(op, rhs).unwrap_or_else(|()| {
                        panic_type!(field, lhs, rhs);
                    }),
                    FilterOp::Unsigned(UnsignedOp::BitwiseAnd, rhs) => {
                        cast_field!(field, lhs, Unsigned) & rhs != 0
                    }
                    FilterOp::Matches(ref regex) => regex.is_match(cast_field!(field, lhs, Bytes)),
                    FilterOp::OneOf(ref values) => values
                        .try_contains(lhs)
                        .unwrap_or_else(|()| panic_type!(field, lhs, values)),
                }
            }
            Filter::Combine(op, ref filters) => {
                let mut results = filters.iter().map(|filter| self.execute(filter));
                match op {
                    CombiningOp::And => results.all(|res| res),
                    CombiningOp::Or => results.any(|res| res),
                    CombiningOp::Xor => results.fold(false, |acc, res| acc ^ res),
                }
            }
            Filter::Unary(UnaryOp::Not, ref filter) => !self.execute(filter),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use types::LhsValue;

    use scheme::Scheme;
    use std::net::{IpAddr, Ipv6Addr};

    fn assert_filter(
        scheme: &Scheme,
        execution_context: &ExecutionContext,
        filter: &str,
        expect: bool,
    ) {
        let filter = scheme.parse(filter).unwrap();
        assert_eq!(execution_context.execute(&filter), expect);
    }

    #[test]
    fn compare_ip() {
        let mut scheme = Scheme::default();
        scheme.add_field("ip".to_owned(), Type::Ip);

        let mut execution_context = ExecutionContext::default();
        execution_context.set_field_value("ip", LhsValue::Ip(IpAddr::V6(Ipv6Addr::from(2))));

        assert_filter(&scheme, &execution_context, "ip > ::1", true);
        assert_filter(&scheme, &execution_context, "ip <= ::3", true);
        assert_filter(&scheme, &execution_context, "ip > ::2", false);
        assert_filter(&scheme, &execution_context, "ip < 127.0.0.3", false);
        assert_filter(
            &scheme,
            &execution_context,
            "ip >= 127.0.0.1 and ip < 127.0.0.255",
            false,
        );
        assert_filter(&scheme, &execution_context, "ip == 127.0.0.0/8", false);
        assert_filter(&scheme, &execution_context, "ip != 127.0.0.0/8", true);
    }

    #[test]
    fn check_bool() {
        let mut scheme = Scheme::default();
        scheme.add_field("true".to_owned(), Type::Bool);
        scheme.add_field("false".to_owned(), Type::Bool);

        let mut execution_context = ExecutionContext::default();
        execution_context.set_field_value("true", LhsValue::Bool(true));
        execution_context.set_field_value("false", LhsValue::Bool(false));

        assert_filter(&scheme, &execution_context, "true", true);
        assert_filter(&scheme, &execution_context, "not true", false);
        assert_filter(&scheme, &execution_context, "false", false);
        assert_filter(&scheme, &execution_context, "!false", true);
    }
}
