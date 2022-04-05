// proc-macro-workshop の Builder
// https://github.com/dtolnay/proc-macro-workshop/tree/master/builder

// proc_macro_workshopでRustの手続き的マクロに入門する 前編 - CADDi Tech Blog
// https://caddi.tech/archives/3555

use proc_macro::TokenStream;
use quote::quote;
use syn::DeriveInput;

#[proc_macro_derive(Builder)]
pub fn derive(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree
    let _input = syn::parse_macro_input!(input as DeriveInput);

    let a = quote! {};
    a.into()
}
