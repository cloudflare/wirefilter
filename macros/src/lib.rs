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
                println!("HELLO from {}", stringify!(#name));
                println!("Code {:?}", stringify!(#input));
                #members
                println!("BYE from {}", stringify!(#name));

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
                    // Expands to an expression like
                    //
                    //     0 + self.x.heap_size() + self.y.heap_size() + self.z.heap_size()
                    //
                    // but using fully qualified function call syntax.
                    //
                    // We take some care to use the span of each `syn::Field` as
                    // the span of the corresponding `heap_size_of_children`
                    // call. This way if one of the field types does not
                    // implement `HeapSize` then the compiler's error message
                    // underlines which field it is. An example is shown in the
                    // readme of the parent directory.
                    let recurse = fields.named.iter().map(|f| {
                        let name = &f.ident;
                        let quoted_name = stringify!(#name);
                        let ty = &f.ty;
                        let check = quote_spanned! {f.span() =>
                            //println!(stringify!(&self.#name.generate_context(schema, #quoted_name)));

                            &self.#name.generate_context(schema, #quoted_name);
                            println!("Type is {}", stringify!(#ty));


                        };
                        quote_spanned! {f.span() =>
                            #check
                            //heapsize::HeapSize::heap_size_of_children(&self.#name)
                        }
                    });
                    quote! {
                        #(#recurse)*
                    }
                }
                Fields::Unnamed(ref fields) => {
                    // // Expands to an expression like
                    // //
                    // //     0 + self.0.heap_size() + self.1.heap_size() + self.2.heap_size()
                    // let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    //     let index = Index::from(i);
                    //     quote_spanned! {f.span()=>
                    //         heapsize::HeapSize::heap_size_of_children(&self.#index)
                    //     }
                    // });
                    // quote! {
                    //     0 #(+ #recurse)*
                    // }
                    quote!()
                }
                Fields::Unit => {
                    // Unit structs cannot own more than 0 bytes of heap memory.
                    quote!()
                }
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
