use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{parse_macro_input, parse_quote, Data, DeriveInput, Fields, GenericParam, Generics, Index};
use wirefilter::filterable::Filterable;
use wirefilter::errors::Error;
use wirefilter::{Scheme, ExecutionContext};

//https://github.com/dtolnay/syn/blob/master/examples/heapsize/heapsize_derive/src/lib.rs
//https://doc.rust-lang.org/book/ch19-06-macros.html#how-to-write-a-custom-derive-macro

#[proc_macro_derive(Filterable)]
pub fn derive_filterable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Parse the input tokens into a syntax tree.
    let input = parse_macro_input!(input as DeriveInput);
    make_filterable(&input).into()


}

// non recursive for now
fn make_filterable(input: &DeriveInput) -> TokenStream {
    let name = &input.ident;
    let data = &input.data;
    let members = iter_members(data);

    quote! {
        impl Filterable for #name {
            fn filter_context<'s>(&self, schema: &'s Scheme) -> Result<ExecutionContext<'s>, Error> {
                let mut ctx = ExecutionContext::new(schema);
                #members
                Ok(ctx)
            }
        }
    }
}

fn iter_members(data: &Data) -> TokenStream {
    match *data {
        Data::Struct(ref data) => {
            match data.fields {
                Fields::Named(ref fields) => {
                    let recurse = fields.named.iter().map(|f| {
                        let name = &f.ident;
                        let ty = &f.ty;
                        let check = quote_spanned! {f.span() =>
                            &self.#name.generate_context(&mut ctx, stringify!(#name));
                            println!("Type is {}", stringify!(#ty));
                        };
                        quote_spanned! {f.span() =>
                            #check
                        }
                    });
                    quote! {
                        #(#recurse)*
                    }
                }
                Fields::Unit | Fields::Unnamed(_) => unimplemented!(),
            }
        }
        Data::Enum(_) | Data::Union(_) => unimplemented!(),
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Filterable)]
    struct Empty;

    #[test]
    fn it_works() {
        let scheme = Scheme!(
          blah: Bytes
        );
        let e = Empty{};
        let exc = e.filter_context(scheme).unwrap();


        assert_eq!(2 + 2, 4);
    }
}
