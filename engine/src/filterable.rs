use crate::scheme::Scheme;
use crate::ExecutionContext;

extern crate proc_macro;
use proc_macro::TokenStream;

pub trait Filterable {
    fn filter_context<'s>(&self, schema: &'s Scheme) -> Result<ExecutionContext<'s>, errors::Error>;
}

#[proc_macro_derive(Filterable)]
pub fn derive_answer_fn(_item: TokenStream) -> TokenStream {
    "fn answer() -> u32 { 42 }".parse().unwrap()
}