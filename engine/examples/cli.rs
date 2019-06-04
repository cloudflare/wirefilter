use std::env::args;
use wirefilter::{
    Function, FunctionArgKind, FunctionArgs, FunctionImpl, FunctionOptParam, FunctionParam,
    LhsValue, Scheme, Type,
};

fn panic_function<'a>(_: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    panic!();
}

fn main() {
    let filter = args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let mut scheme = Scheme! {
        ip: Ip,
        str: Bytes,
        int: Int,
        bool: Bool,
        str_arr: Array(Bytes),
        str_map: Map(Bytes)
    };

    scheme
        .add_function(
            "panic".into(),
            Function {
                params: vec![FunctionParam {
                    arg_kind: FunctionArgKind::Field,
                    val_type: Type::Bytes,
                }],
                opt_params: vec![FunctionOptParam {
                    arg_kind: FunctionArgKind::Literal,
                    default_value: "".into(),
                }],
                return_type: Type::Bytes,
                implementation: FunctionImpl::new(panic_function),
            },
        )
        .unwrap();

    match scheme.parse(&filter) {
        Ok(res) => println!("{:#?}", res),
        Err(err) => println!("{}", err),
    }
}
