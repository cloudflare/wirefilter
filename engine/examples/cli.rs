use std::env::args;
use wirefilter::{
    FunctionArgs, LhsValue, Scheme, SimpleFunctionArgKind, SimpleFunctionDefinition,
    SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam, Type,
};

fn panic_function<'a>(_: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    panic!();
}

fn main() {
    let filter = args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let mut builder = Scheme! {
        ip: Ip,
        str: Bytes,
        int: Int,
        bool: Bool,
        str_arr: Array(Bytes),
        str_map: Map(Bytes),
        bool_arr: Array(Bool),
    };

    builder
        .add_function(
            "panic",
            SimpleFunctionDefinition {
                params: vec![SimpleFunctionParam {
                    arg_kind: SimpleFunctionArgKind::Field,
                    val_type: Type::Bytes,
                }],
                opt_params: vec![SimpleFunctionOptParam {
                    arg_kind: SimpleFunctionArgKind::Literal,
                    default_value: "".into(),
                }],
                return_type: Type::Bytes,
                implementation: SimpleFunctionImpl::new(panic_function),
            },
        )
        .unwrap();

    let scheme = builder.build();

    match scheme.parse(&filter) {
        Ok(res) => println!("{res:#?}"),
        Err(err) => println!("{err}"),
    }
}
