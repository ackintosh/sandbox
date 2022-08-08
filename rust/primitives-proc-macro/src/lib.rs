// //////////////////////////
// 手続き的 (procedural)マクロ
// 参考:
//   - https://caddi.tech/archives/3555
//   - 公式ドキュメント: https://doc.rust-jp.rs/book-ja/ch19-06-macros.html
//   - 手続き的マクロの教材
//       - https://github.com/dtolnay/proc-macro-workshop
//           - 解説: https://zenn.dev/magurotuna/articles/bab4db5999ebfa
//                  https://caddi.tech/archives/3555
//
//  3種類の 手続き的マクロ
//    1. `#[derive]` マクロ
//        - 構造体やenumに付与することでその構造体やenumに追加の処理を実装できる
//    2. 属性風マクロ
//        - deriveマクロと同様に付与した対象に対して追加の処理を実装できますが、こちらは構造体やenumだけでなく関数などにも適用できます
//        - テストを書くときに用いる `#[test]` アトリビュートなどがこれにあたります
//    3. 関数風マクロ
//        - 関数風マクロは宣言的マクロのように関数呼び出しと似た形で使用できるマクロです。宣言的マクロと比較するとより複雑な処理を記述できる
// //////////////////////////

// *** 手続き型マクロの処理の流れ ***
// 1. トークン列を入力として受け取る
// 2. 受け取ったトークン列を構文木に変換する
// 3. 変換した構文木をもとに処理を行い所望の構文木を得る
// 4. 得られた構文木をトークン列に変換して返す
//
// * トークン列と構文木の相互変換にはsynクレートとquoteクレートがよく使われる
//   synクレートはトークン列から構文木への変換に使用
//   また、synクレートには構文木に関する構造体が定義されており、パースして得られた構文木はこれらの構造体のインスタンスとして保持される
// * quoteクレートは構文木からトークン列への変換に使用する

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{Data, DeriveInput, Fields, Ident, Type};

// *** 下記記事の 02-create-builder まで実装した状態 ***
// https://caddi.tech/archives/3555
#[proc_macro_derive(Builder)]
pub fn derive(input: TokenStream) -> TokenStream {
    //        ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑
    // `proc_macro::TokenStream` を引数として受け取る

    // `syn::parse_macro_input!` マクロでパースして構文木にする
    let ast = syn::parse_macro_input!(input as DeriveInput);
    // derive マクロの入力をパースすると以下のような `syn::DeriveInput` 構造体が得られる
    // * vis: 構造体の可視性の情報を保持しています
    // * ident: identifier の略で、変数名などの Rust コード中の識別子の情報を保持しています。ここでは derive マクロが付与された構造体/enum の名前を保持しています
    // * data: 構造体の保持するフィールドの情報を持っています

    // 生成するビルダー名は `{対象の構造体名}Builder` とする
    let builder_name = format_ident!("{}Builder", ast.ident);

    // 対象の構造体が持つフィールドの名前と型を入力から取得する
    let (idents, types): (Vec<Ident>, Vec<Type>) = match ast.data {
        Data::Struct(data) => match data.fields {
            Fields::Named(fields) => fields
                .named
                .into_iter()
                .map(|field| {
                    let ident = field.ident;
                    let ty = field.ty;
                    (ident.unwrap(), ty)
                })
                .unzip(),
            Fields::Unnamed(_) => {
                unimplemented!()
            }
            Fields::Unit => {
                unimplemented!()
            }
        },
        Data::Enum(_) => {
            unimplemented!()
        }
        Data::Union(_) => {
            unimplemented!()
        }
    };

    // * トークン列を生成するためには `quote` クレートの `quote!` マクロを使う
    //   * Rustのコードと(ほぼ)同じ構文で記述でき、この内容がトークン列に変換される
    //
    // * `quote!` マクロを使うと `proc_macro::TokenStream` ではなく `proc_macro2::TokenStream` が生成される
    //   * `proc_macro2::TokenStream` は、 `proc_macro2` クレートによって提供されるトークン列
    //   * `proc_macro::TokenStream` が Rust コンパイラの使用するトークン列
    //
    // * `quote!` マクロの内部では特殊な記法を使える
    //   * `quote::ToTokens` トレイトを実装する変数に `quote!` マクロの中で#をつけるとその変数の内容が挿入される
    //   * これを使って適切な名前や型のフィールドを持った構造体を動的に生成します
    //     * `syn::Ident` などの構造体は `quote::ToTokens` トレイトを実装しているので特に気にせず使える
    //   * 以下では、 `#ident`, `#vis`, `#builder_name` といった変数で利用している
    let ident = ast.ident;
    let vis = ast.vis;

    // * `#(...)*` のような形で `IntoIterator` を実装した型の変数を繰り返して挿入できる
    //   * 以下では、`#idents`, `#types` といった変数で利用している

    let expand = quote! {
        #vis struct #builder_name {
            #(#idents: Option<#types>),*
        }

        impl #ident {
            pub fn builder() -> #builder_name {
                CommandBuilder {
                    #(#idents: None),*
                }
            }
        }
    };

    // proc_macro2 から proc_macro の TokenStream に変換する
    proc_macro::TokenStream::from(expand)
}
