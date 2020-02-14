#[macro_use]
extern crate afl;
extern crate wirefilter;
#[macro_use]
extern crate lazy_static;

use wirefilter::{
    FunctionArgKind, FunctionArgs, LhsValue, SimpleFunctionDefinition, SimpleFunctionImpl,
    SimpleFunctionParam, Type,
};

#[cfg(fuzzing)]
fn main() {
    use wirefilter::{ExecutionContext, Map, Scheme};

    fuzz!(|key: &[u8]| {
        let mut scheme = Scheme! { foo: Map(Bytes) };
        scheme
            .add_function("first".to_string(), FIRST_FN.clone())
            .unwrap();

        let filter = scheme.parse("first(foo) == \"abc\"").unwrap().compile();

        let value: &[u8] = b"abc";
        let mut map = Map::new(Type::Bytes);
        map.insert(key, LhsValue::Bytes(value.into())).unwrap();

        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value("foo", map).unwrap();

        assert!(filter.execute(&ctx).unwrap());
    });
}

#[cfg(not(fuzzing))]
fn main() {
    panic!("must compile with `cargo afl build`, not `cargo build`")
}

/// A function which, given an array of bool, returns true if any one of the
/// arguments is true, otherwise false.
///
/// It expects one argument and will panic if given an incorrect number of
/// arguments or an incorrect LhsValue.
fn first_impl<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let arg = args.next().expect("expected 1 argument, got 0");
    if args.next().is_some() {
        panic!(format!("expected 1 argument, got {}", 2 + args.count()));
    }
    match arg {
        Ok(LhsValue::Map(m)) => {
            let bytes = m.into_iter().next().unwrap().1;

            Some(bytes)
        }
        _ => unreachable!(),
    }
}

lazy_static! {
    // ANY_FN is a function which returns true if any arguments passed to the
    // function are true.
    pub static ref FIRST_FN: SimpleFunctionDefinition = SimpleFunctionDefinition {
        params: vec![SimpleFunctionParam {
            arg_kind: FunctionArgKind::Field,
            val_type: Type::Map(Box::new(Type::Bytes)),
        }],
        opt_params: vec![],
        return_type: Type::Bytes,
        implementation: SimpleFunctionImpl::new(first_impl)
    };
}
