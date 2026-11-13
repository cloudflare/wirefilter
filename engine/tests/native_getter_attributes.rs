#![deny(unused_variables)]

use std::cell::Cell;
use wirefilter::values::{self, SliceView};
use wirefilter::{
    DefaultCompiler, EvaluationContext, Field, HasScheme, LhsValue, ListMatcher, ListRef,
    ProviderFamily, Scheme, SchemeBuilder, Type,
};

struct Request<'data> {
    scheme: &'data Scheme,
    names: &'data [Box<str>],
    number: Option<i64>,
    accesses: Cell<usize>,
}

#[test]
fn default_compiler_traits_do_not_require_user_data_or_family_traits() {
    struct UserData;

    fn assert_compiler_traits<C: wirefilter::Compiler + Clone + Copy + std::fmt::Debug>() {}

    assert_compiler_traits::<DefaultCompiler<()>>();
    assert_compiler_traits::<DefaultCompiler<UserData>>();
    assert_compiler_traits::<DefaultCompiler<(), RequestFields>>();
}

impl Request<'_> {
    fn record_access(&self) {
        self.accesses.set(self.accesses.get() + 1);
    }
}

impl HasScheme for Request<'_> {
    fn scheme(&self) -> &Scheme {
        self.scheme
    }
}

impl EvaluationContext for Request<'_> {
    type UserData = ();

    fn get_user_data(&self) -> &() {
        &()
    }

    fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
        unreachable!("the test scheme has no lists")
    }
}

struct NamesProvider;

impl ProviderFamily for NamesProvider {
    type Storage<'data> = &'data [Box<str>];
    type Value<'ctx, 'data>
        = SliceView<'data, Box<str>>
    where
        'data: 'ctx;
    type ValueType = values::Array<values::Bytes>;

    fn reborrow<'ctx, 'data: 'ctx>(value: &'ctx Self::Storage<'data>) -> Self::Value<'ctx, 'data> {
        SliceView(value)
    }
}

// The unused locals require attributes to reach the function containing each
// getter body; applying them only to the FieldGetter adapter is insufficient.
wirefilter::wirefilter_fields! {
    impl<'data> RequestFields for Request<'data> {
        "name" => {
            provider wirefilter::BorrowedValueProvider<str>;
            #[inline(never)]
            #[allow(unused_variables)]
            fn(request: &Request<'data>, field: &Field) -> &str {
                let intentionally_unused = ();
                assert_eq!(field.name(), "name");
                request.record_access();
                if let Some(name) = request.names.first() {
                    return name.as_ref();
                }
                ""
            }
        },
        "count" => {
            #[inline(always)]
            #[cfg_attr(test, allow(unused_variables))]
            fn(request: &Request<'data>) -> i64 {
                let intentionally_unused = ();
                request.record_access();
                request.names.len() as i64
            }
        },
        "maybe_name" => {
            #[inline(never)]
            #[cfg_attr(test, allow(unused_variables))]
            fn(request: &Request<'data>) -> Option<&str> {
                let intentionally_unused = ();
                request.record_access();
                let name = request.names.first()?;
                if name.is_empty() {
                    return None;
                }
                Some(name.as_ref())
            }
        },
        "maybe_number" => {
            #[inline(always)]
            #[allow(unused_variables)]
            fn(request: &Request<'data>) -> Option<i64> {
                let intentionally_unused = ();
                request.record_access();
                let number = request.number?;
                if number < 0 {
                    return None;
                }
                Some(number)
            }
        },
        "selection" => {
            provider NamesProvider;
            #[inline(never)]
            #[cfg_attr(test, allow(unused_variables))]
            fn(request: &Request<'data>, field: &Field) -> Option<SliceView<'data, Box<str>>> {
                let intentionally_unused = ();
                assert_eq!(field.name(), "selection");
                request.record_access();
                request.names.first()?;
                Some(SliceView(request.names))
            }
        },
    }
}

fn scheme() -> Scheme {
    let mut builder = SchemeBuilder::new();
    builder.add_field("name", Type::Bytes).unwrap();
    builder.add_field("count", Type::Int).unwrap();
    builder
        .add_optional_field("maybe_name", Type::Bytes)
        .unwrap();
    builder
        .add_optional_field("maybe_number", Type::Int)
        .unwrap();
    builder
        .add_optional_field("selection", Type::array(Type::Bytes))
        .unwrap();
    let scheme = builder.build();
    RequestFields::validate_scheme(&scheme).unwrap();
    scheme
}

#[test]
fn test_attributed_getters_preserve_returns_and_optional_control_flow() {
    let scheme = scheme();
    let names = [Box::<str>::from("alpha"), Box::<str>::from("beta")];
    let empty_name = [Box::<str>::from("")];
    let mut compiler = DefaultCompiler::<(), RequestFields>::new();
    let filters = [
        r#"name eq "alpha""#,
        "count eq 2",
        r#"maybe_name eq "alpha""#,
        "maybe_number eq 7",
        r#"any(selection[*] eq "alpha")"#,
    ]
    .map(|expression| {
        scheme
            .parse(expression)
            .unwrap()
            .compile_with_compiler(&mut compiler)
    });

    for (names, number, expected) in [
        (names.as_slice(), Some(7), [true, true, true, true, true]),
        (names.as_slice(), None, [true, true, true, false, true]),
        (names.as_slice(), Some(-1), [true, true, true, false, true]),
        ([].as_slice(), Some(7), [false, false, false, true, false]),
        (
            empty_name.as_slice(),
            Some(7),
            [false, false, false, true, false],
        ),
    ] {
        let request = Request {
            scheme: &scheme,
            names,
            number,
            accesses: Cell::new(0),
        };
        for (index, (filter, expected)) in filters.iter().zip(expected).enumerate() {
            assert_eq!(filter.execute(&request).unwrap(), expected);
            assert_eq!(request.accesses.get(), index + 1);
        }
    }
}

#[test]
fn test_attributed_getters_preserve_borrowed_payloads() {
    let scheme = scheme();
    let names = [Box::<str>::from("alpha")];
    let request = Request {
        scheme: &scheme,
        names: &names,
        number: None,
        accesses: Cell::new(0),
    };
    let mut compiler = DefaultCompiler::<(), RequestFields>::new();
    for field in ["name", "maybe_name", "selection"] {
        let filter = scheme
            .parse_value(field)
            .unwrap()
            .compile_with_compiler(&mut compiler);
        let value = filter.execute(&request).unwrap().unwrap();
        let bytes = match &value {
            LhsValue::Bytes(bytes) => bytes,
            LhsValue::Array(values) => match values.get(0).unwrap() {
                LhsValue::Bytes(bytes) => bytes,
                _ => panic!("expected array of byte strings"),
            },
            _ => panic!("expected bytes or array"),
        };
        assert_eq!(bytes.as_ref().as_ptr(), names[0].as_ptr(), "{field}");
    }
}
