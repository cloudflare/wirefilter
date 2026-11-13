use wirefilter::{
    DefaultCompiler, EvaluationContext, Field, HasScheme, LhsValue, ListMatcher, ListRef, Scheme,
    SchemeBuilder, Type,
};

// These names belong to the application. Generated getter helpers must not
// replace them when resolving the context type or expressions in a getter body.
struct Getter<'data> {
    scheme: &'data Scheme,
    number: i64,
    optional: Option<i64>,
    name: &'data str,
}

impl Getter<'_> {
    fn read(&self) -> i64 {
        self.number
    }

    fn read_optional(&self) -> Option<i64> {
        self.optional
    }

    fn name(&self) -> &str {
        self.name
    }
}

impl HasScheme for Getter<'_> {
    fn scheme(&self) -> &Scheme {
        self.scheme
    }
}

impl EvaluationContext for Getter<'_> {
    type UserData = ();

    fn get_user_data(&self) -> &() {
        &()
    }

    fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
        unreachable!("this test has no lists")
    }
}

fn value(context: &Getter<'_>) -> i64 {
    context.number + 1
}

fn call(context: &Getter<'_>) -> i64 {
    context.number + 2
}

fn __wirefilter_call(context: &Getter<'_>) -> i64 {
    context.number + 3
}

wirefilter::wirefilter_fields! {
    impl<'data> Fields for Getter<'data> {
        "required" => {
            fn(field: &Getter<'data>, metadata: &Field) -> i64 {
                assert_eq!(metadata.name(), "required");
                Getter::read(field) + value(field) + call(field) + __wirefilter_call(field)
            }
        },
        "optional" => {
            fn(consumer: &Getter<'data>, field: &Field) -> Option<i64> {
                assert_eq!(field.name(), "optional");
                assert!(field.optional());
                let number = Getter::read_optional(consumer)?;
                Some(number + value(consumer) + call(consumer) + __wirefilter_call(consumer))
            }
        },
        "name" => {
            fn(context: &Getter<'data>) -> &str {
                Getter::name(context)
            }
        },
    }
}

#[test]
fn test_getter_bodies_resolve_application_items() {
    let mut builder = SchemeBuilder::new();
    builder.add_field("required", Type::Int).unwrap();
    builder.add_optional_field("optional", Type::Int).unwrap();
    builder.add_field("name", Type::Bytes).unwrap();
    let scheme = builder.build();
    Fields::validate_scheme(&scheme).unwrap();
    let mut compiler = DefaultCompiler::<(), Fields>::new();
    let values = ["required", "optional", "name"].map(|field| {
        scheme
            .parse_value(field)
            .unwrap()
            .compile_with_compiler(&mut compiler)
    });
    let comparison = scheme
        .parse(r#"required eq 34 and optional eq 38 and name eq "example""#)
        .unwrap()
        .compile_with_compiler(&mut compiler);

    for (number, optional, expected_required, expected_optional, matches) in [
        (7, Some(11), 34, Some(38), true),
        (7, None, 34, None, false),
        (-2, Some(3), -2, Some(3), false),
    ] {
        let context = Getter {
            scheme: &scheme,
            number,
            optional,
            name: "example",
        };
        assert_eq!(
            values[0].execute(&context).unwrap(),
            Ok(LhsValue::Int(expected_required)),
        );
        assert_eq!(
            values[1].execute(&context).unwrap(),
            expected_optional.map(LhsValue::Int).ok_or(Type::Int),
        );
        assert_eq!(
            values[2].execute(&context).unwrap(),
            Ok(LhsValue::from("example")),
        );
        assert_eq!(comparison.execute(&context).unwrap(), matches);
    }
}
