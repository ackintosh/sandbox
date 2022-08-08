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

    let expand = quote! {
        pub struct CommandBuilder {
            executable: Option<String>,
            args: Option<Vec<String>>,
            env: Option<Vec<String>>,
            current_dir: Option<Vec<String>>,
        }

        impl Command {
            pub fn builder() -> CommandBuilder {
                CommandBuilder {
                    executable: None,
                    args: None,
                    env: None,
                    current_dir: None,
                }
            }
        }
    };

    proc_macro::TokenStream::from(expand)
}
