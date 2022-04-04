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
