use crate::{
    scheme::{Field, Scheme},
    types::{GetType, LhsValue, TypeMismatchError},
};
use std::ops::Add;

/// An execution context stores an associated [`Scheme`](struct@Scheme) and a
/// set of runtime values to execute [`Filter`](::Filter) against.
///
/// It acts as a map in terms of public API, but provides a constant-time
/// index-based access to values for a filter during execution.
pub struct ExecutionContext<'e> {
    scheme: &'e Scheme,
    values: Box<[Option<LhsValue<'e>>]>,
}

/// Combines two executionContexts. `rhs` overwrites `self` so it is not really associative, maybe Add is not the best to use
impl<'s> Add for ExecutionContext<'s> {
    type Output = ExecutionContext<'s>;

    fn add(mut self, rhs: Self) -> Self::Output {
        debug_assert!(self.scheme() == rhs.scheme);
        let mut rhs = rhs;
        let values = self.scheme.get_field_count();
        let mut new = ExecutionContext::new(self.scheme);

        for i in 0..values {
            if let Some(v) = (&mut self.values[i]).take() {
                new.values[i] = Some(v)
            }

            if let Some(v) = (&mut rhs.values[i]).take() {
                new.values[i] = Some(v)
            }
        }
        new
    }
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

    pub(crate) fn get_field_value(&'e self, field: Field<'e>) -> Option<LhsValue<'e>> {
        // This is safe because this code is reachable only from Filter::execute
        // which already performs the scheme compatibility check, but check that
        // invariant holds in the future at least in the debug mode.
        debug_assert!(self.scheme() == field.scheme());

        let lhs_value = self.values[field.index()].as_ref();
        lhs_value.map(|e| e.as_ref())
    }

    /// Sets a runtime value for a given field name.
    pub fn set_field_value<'v: 'e, V: Into<LhsValue<'v>>>(
        &mut self,
        name: &str,
        value: V,
    ) -> Result<(), TypeMismatchError> {
        let field = self.scheme.get_field_index(name).unwrap();
        let value = value.into();

        let field_type = field.get_type();
        let value_type = value.get_type();

        if field_type == value_type {
            self.values[field.index()] = Some(value);
            Ok(())
        } else {
            Err(TypeMismatchError {
                expected: field_type,
                actual: value_type,
            })
        }
    }
}

#[test]
fn test_field_value_type_mismatch() {
    use crate::types::Type;

    let scheme = Scheme! { foo: Int };

    let mut ctx = ExecutionContext::new(&scheme);

    assert_eq!(
        ctx.set_field_value("foo", LhsValue::Bool(false)),
        Err(TypeMismatchError {
            expected: Type::Int,
            actual: Type::Bool
        })
    );
}

