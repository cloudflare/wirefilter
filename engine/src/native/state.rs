//! Persistent executor state for contexts whose fields live in native storage.

use crate::{
    EvaluationContext, EvaluationContextMut, HasScheme, List, ListMatcher, ListRef, Scheme, Type,
};

/// Scheme, list matchers, and compiler state retained across native evaluations.
///
/// This type has no field-value slots. The embedding runtime supplies native
/// fields through its context family and can borrow this state while evaluating
/// them. Neither the state nor its list matchers must be rebuilt for each phase.
///
/// This is an optional storage implementation of [`HasScheme`],
/// [`EvaluationContext`], and [`EvaluationContextMut`]. An application context can
/// borrow it and forward those methods while its [`crate::ContextFamily`] supplies
/// getters for application-owned field values. Applications can instead implement
/// the same interfaces using their existing state. See [`crate::native`] for a
/// complete example.
///
/// Forward [`EvaluationContext::get_list_matcher_unchecked`] as well as the
/// checked accessor so list comparisons do not repeat the scheme check already
/// performed by the filter.
///
/// [`crate::ExecutionContext`] already owns equivalent state together with its
/// stored field values and does not need a separate `NativeContextState`. The
/// application is responsible for resetting state when reusing it; [`Self::clear`]
/// clears list contents but retains user data.
#[derive(Debug, PartialEq)]
pub struct NativeContextState<U = ()> {
    scheme: Scheme,
    list_matchers: Box<[Box<dyn ListMatcher>]>,
    user_data: U,
}

impl<U> NativeContextState<U> {
    /// Create persistent state with default user data and the scheme's matchers.
    pub fn new(scheme: &Scheme) -> Self
    where
        U: Default,
    {
        Self::new_with(scheme, U::default)
    }

    /// Create persistent state with the supplied user-data initializer.
    pub fn new_with(scheme: &Scheme, user_data: impl FnOnce() -> U) -> Self {
        Self {
            scheme: scheme.clone(),
            list_matchers: scheme
                .lists()
                .map(|list| list.definition().new_matcher())
                .collect(),
            user_data: user_data(),
        }
    }

    /// Scheme associated with this state.
    #[inline]
    pub fn scheme(&self) -> &Scheme {
        &self.scheme
    }

    /// Compiler-specific execution state.
    #[inline]
    pub fn get_user_data(&self) -> &U {
        &self.user_data
    }

    /// Mutable compiler-specific execution state.
    #[inline]
    pub fn get_user_data_mut(&mut self) -> &mut U {
        &mut self.user_data
    }

    /// Matcher registered for the supplied list.
    #[inline]
    pub fn get_list_matcher(&self, list: ListRef<'_>) -> &dyn ListMatcher {
        assert!(self.scheme() == list.scheme());
        &*self.list_matchers[list.index()]
    }

    /// Matcher registered for the supplied type, if any.
    #[inline]
    pub fn get_list_matcher_from_type(&self, ty: &Type) -> Option<&dyn ListMatcher> {
        let list = self.scheme.get_list(ty)?;
        Some(&*self.list_matchers[list.index()])
    }

    /// Mutable matcher registered for the supplied list.
    #[inline]
    pub fn get_list_matcher_mut(&mut self, list: ListRef<'_>) -> &mut dyn ListMatcher {
        assert!(self.scheme() == list.scheme());
        &mut *self.list_matchers[list.index()]
    }

    /// Mutable matcher registered for the supplied type, if any.
    #[inline]
    pub fn get_list_matcher_mut_from_type(&mut self, ty: &Type) -> Option<&mut dyn ListMatcher> {
        let list = self.scheme.get_list(ty)?;
        Some(&mut *self.list_matchers[list.index()])
    }

    /// Clear list contents while retaining their storage and user data.
    ///
    /// As with [`crate::ExecutionContext::clear`], compiler-specific user-data
    /// cleanup remains the embedding runtime's responsibility.
    pub fn clear(&mut self) {
        self.list_matchers
            .iter_mut()
            .for_each(|matcher| matcher.clear());
    }
}

impl<U> HasScheme for NativeContextState<U> {
    #[inline]
    fn scheme(&self) -> &Scheme {
        self.scheme()
    }
}

impl<U> EvaluationContext for NativeContextState<U> {
    type UserData = U;

    #[inline]
    fn get_user_data(&self) -> &U {
        self.get_user_data()
    }

    #[inline]
    fn get_list_matcher(&self, list: ListRef<'_>) -> &dyn ListMatcher {
        self.get_list_matcher(list)
    }

    #[inline]
    fn get_list_matcher_from_type(&self, ty: &Type) -> Option<&dyn ListMatcher> {
        self.get_list_matcher_from_type(ty)
    }

    #[inline]
    fn get_list_matcher_unchecked(&self, list: &List) -> &dyn ListMatcher {
        debug_assert!(self.scheme() == list.scheme());
        &*self.list_matchers[list.index()]
    }
}

impl<U> EvaluationContextMut for NativeContextState<U> {
    #[inline]
    fn get_user_data_mut(&mut self) -> &mut U {
        self.get_user_data_mut()
    }

    #[inline]
    fn get_list_matcher_mut(&mut self, list: ListRef<'_>) -> &mut dyn ListMatcher {
        self.get_list_matcher_mut(list)
    }

    #[inline]
    fn get_list_matcher_mut_from_type(&mut self, ty: &Type) -> Option<&mut dyn ListMatcher> {
        self.get_list_matcher_mut_from_type(ty)
    }
}

#[cfg(test)]
mod tests {
    use super::NativeContextState;
    use crate::{
        DefaultCompiler, EvaluationContext, EvaluationContextMut, HasScheme, LhsValue, List,
        ListDefinition, ListMatcher, ListRef, Scheme, SchemeBuilder, Type,
    };
    use serde::{Deserialize, Serialize};
    use std::collections::BTreeSet;

    #[derive(Debug)]
    struct ValuesList;

    #[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Default)]
    struct ValuesMatcher {
        values: BTreeSet<i64>,
        clears: usize,
    }

    impl ListDefinition for ValuesList {
        fn deserialize_matcher<'de>(
            &self,
            _: Type,
            deserializer: &mut dyn erased_serde::Deserializer<'de>,
        ) -> Result<Box<dyn ListMatcher>, erased_serde::Error> {
            erased_serde::deserialize::<ValuesMatcher>(deserializer)
                .map(|matcher| Box::new(matcher) as Box<dyn ListMatcher>)
        }

        fn new_matcher(&self) -> Box<dyn ListMatcher> {
            Box::new(ValuesMatcher::default())
        }
    }

    impl ListMatcher for ValuesMatcher {
        fn match_value(&self, name: &str, value: &LhsValue<'_>) -> bool {
            name == "numbers"
                && matches!(value, LhsValue::Int(value) if self.values.contains(value))
        }

        fn clear(&mut self) {
            self.values.clear();
            self.clears += 1;
        }
    }

    fn scheme() -> Scheme {
        let mut builder = SchemeBuilder::new();
        builder.add_field("name", Type::Bytes).unwrap();
        builder
            .add_field("numbers", Type::array(Type::Int))
            .unwrap();
        builder.add_list(Type::Int, ValuesList).unwrap();
        builder.build()
    }

    fn insert(context: &mut impl EvaluationContextMut<UserData = usize>, value: i64) {
        context
            .get_list_matcher_mut_from_type(&Type::Int)
            .unwrap()
            .as_any_mut()
            .downcast_mut::<ValuesMatcher>()
            .unwrap()
            .values
            .insert(value);
        *context.get_user_data_mut() += 1;
    }

    struct StateAdapter<'a>(&'a mut NativeContextState<usize>);

    impl HasScheme for StateAdapter<'_> {
        fn scheme(&self) -> &Scheme {
            self.0.scheme()
        }
    }

    impl EvaluationContext for StateAdapter<'_> {
        type UserData = usize;

        fn get_user_data(&self) -> &usize {
            self.0.get_user_data()
        }

        fn get_list_matcher(&self, list: ListRef<'_>) -> &dyn ListMatcher {
            self.0.get_list_matcher(list)
        }

        fn get_list_matcher_unchecked(&self, list: &List) -> &dyn ListMatcher {
            self.0.get_list_matcher_unchecked(list)
        }
    }

    impl EvaluationContextMut for StateAdapter<'_> {
        fn get_user_data_mut(&mut self) -> &mut usize {
            self.0.get_user_data_mut()
        }

        fn get_list_matcher_mut(&mut self, list: ListRef<'_>) -> &mut dyn ListMatcher {
            self.0.get_list_matcher_mut(list)
        }
    }

    #[test]
    fn test_list_state_reuse_and_generic_mutation() {
        let scheme = scheme();
        let mut state = NativeContextState::new_with(&scheme, || 7usize);
        assert!(state.get_list_matcher_from_type(&Type::Bytes).is_none());
        assert!(state.get_list_matcher_mut_from_type(&Type::Bytes).is_none());
        insert(&mut StateAdapter(&mut state), 41);
        assert_eq!(*state.get_user_data(), 8);
        let matcher = state
            .get_list_matcher(scheme.get_list(&Type::Int).unwrap())
            .as_any()
            .downcast_ref::<ValuesMatcher>()
            .unwrap();
        assert!(matcher.match_value("numbers", &LhsValue::Int(41)));
        let address = matcher as *const ValuesMatcher;
        state.clear();
        let matcher = state
            .get_list_matcher_from_type(&Type::Int)
            .unwrap()
            .as_any()
            .downcast_ref::<ValuesMatcher>()
            .unwrap();
        assert_eq!(matcher as *const ValuesMatcher, address);
        assert!(!matcher.match_value("numbers", &LhsValue::Int(41)));
        assert_eq!(matcher.clears, 1);
        assert_eq!(*state.get_user_data(), 8);
        let adapter = StateAdapter(&mut state);
        assert!(EvaluationContext::get_list_matcher_from_type(&adapter, &Type::Int).is_some());

        let mut stored = crate::ExecutionContext::new_with(&scheme, || 7usize);
        insert(&mut stored, 41);
        assert_eq!(*stored.get_user_data(), 8);
        assert!(
            stored
                .get_list_matcher_from_type(&Type::Int)
                .unwrap()
                .match_value("numbers", &LhsValue::Int(41))
        );
    }

    #[test]
    fn test_explicit_stored_snapshot_preserves_lists_without_populating_fields() {
        let scheme = scheme();
        let mut state = NativeContextState::new_with(&scheme, || 0usize);
        insert(&mut state, 41);
        let snapshot = crate::ExecutionContext::new_from_context(&state, 9usize);
        assert!(
            snapshot
                .get_field_value(scheme.get_field("name").unwrap())
                .is_none()
        );
        assert!(
            snapshot
                .get_field_value(scheme.get_field("numbers").unwrap())
                .is_none()
        );
        state.clear();
        assert!(
            !state
                .get_list_matcher_from_type(&Type::Int)
                .unwrap()
                .match_value("numbers", &LhsValue::Int(41))
        );
        assert!(
            snapshot
                .get_list_matcher_from_type(&Type::Int)
                .unwrap()
                .match_value("numbers", &LhsValue::Int(41))
        );
        assert_eq!(*snapshot.get_user_data(), 9);
        assert_eq!(*state.get_user_data(), 1);
    }

    #[test]
    fn test_list_access_checks_scheme_identity() {
        let scheme = scheme();
        let other = self::scheme();
        let mut state = NativeContextState::<()>::new(&scheme);
        let foreign = other.get_list(&Type::Int).unwrap();
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                state.get_list_matcher(foreign);
            }))
            .is_err()
        );
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                state.get_list_matcher_mut(foreign);
            }))
            .is_err()
        );
    }

    struct Request {
        name: Box<str>,
        numbers: Vec<i64>,
    }

    struct NativeContext<'a> {
        request: &'a Request,
        state: &'a NativeContextState<usize>,
    }

    impl HasScheme for NativeContext<'_> {
        fn scheme(&self) -> &Scheme {
            self.state.scheme()
        }
    }

    impl EvaluationContext for NativeContext<'_> {
        type UserData = usize;

        fn get_user_data(&self) -> &usize {
            self.state.get_user_data()
        }

        fn get_list_matcher(&self, list: ListRef<'_>) -> &dyn ListMatcher {
            self.state.get_list_matcher(list)
        }

        fn get_list_matcher_unchecked(&self, list: &List) -> &dyn ListMatcher {
            self.state.get_list_matcher_unchecked(list)
        }
    }

    crate::wirefilter_fields! {
        impl<'data> NativeFields for NativeContext<'data> {
            "name" => {
                fn(context: &NativeContext<'data>) -> &str {
                    &context.request.name
                }
            },
            "numbers" => {
                fn(context: &NativeContext<'data>) -> &Vec<i64> {
                    &context.request.numbers
                }
            },
        }
    }

    #[test]
    fn test_owned_state_can_move_to_worker_and_borrow_native_fields_there() {
        let scheme = scheme();
        NativeFields::validate_scheme(&scheme).unwrap();
        let mut compiler = DefaultCompiler::<usize, NativeFields>::new();
        let filter = scheme
            .parse(r#"name == "first" and any(numbers[*] in $numbers)"#)
            .unwrap()
            .compile_with_compiler(&mut compiler);
        let value = scheme
            .parse_value("name")
            .unwrap()
            .compile_with_compiler(&mut compiler);
        let mut state = NativeContextState::new_with(&scheme, || 0usize);
        insert(&mut state, 41);
        let request = Request {
            name: "first".into(),
            numbers: vec![40, 41],
        };
        let caller = std::thread::current().id();
        let (mut request, state, filter) = std::thread::spawn(move || {
            assert_ne!(std::thread::current().id(), caller);
            let context = NativeContext {
                request: &request,
                state: &state,
            };
            assert!(filter.execute(&context).unwrap());
            let LhsValue::Bytes(bytes) = value.execute(&context).unwrap().unwrap() else {
                panic!("expected bytes");
            };
            assert_eq!(bytes.as_ref().as_ptr(), request.name.as_ptr());
            assert_eq!(*context.get_user_data(), 1);
            (request, state, filter)
        })
        .join()
        .unwrap();
        request.name = "second".into();
        assert!(
            !filter
                .execute(&NativeContext {
                    request: &request,
                    state: &state,
                })
                .unwrap()
        );
        assert_eq!(*state.get_user_data(), 1);
        assert!(
            state
                .get_list_matcher_from_type(&Type::Int)
                .unwrap()
                .match_value("numbers", &LhsValue::Int(41))
        );
    }
}
