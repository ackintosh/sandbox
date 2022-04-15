// ////////////////////////////////////////////////////////////
// 公式ドキュメント
// * APIドキュメント
//   Sized in std::marker - Rust
//   https://doc.rust-lang.org/std/marker/trait.Sized.html
// * The Book
//   Unsized Types
//   https://doc.rust-lang.org/book/unsized-types.html
// * The Rustonomicon
//   Exotically Sized Types - The Rustonomicon
//   https://doc.rust-lang.org/nomicon/exotic-sizes.html]
//   日本語訳
//   https://doc.rust-jp.rs/rust-nomicon-ja/exotic-sizes.html
// ////////////////////////////////////////////////////////////

// 参考
// RustのSizedとfatポインタ - 簡潔なQ https://qnighy.hatenablog.com/entry/2017/03/04/131311

// * RustにはSizedというトレイトがあり、一部の例外を除いて暗黙のうちに実装されている
// * Sizedが実装されていない型は Dynamically Sized Type(DST) と呼ばれ、これらのデータはfatポインタを経由してアクセスする
// * Sizedトレイトは2つの意味を持つ
//   1. Sizedを実装する型は、全て同じバイト数である
//      C言語のsizeofに相当するstd::mem::size_of が使える。(Sizedでない場合は値によって異なるため、std::mem::size_of_valを使う)
//   2. Sizedを実装する型は、データ本体以外の余計な情報を持たない
//      (逆に、Sizedでない場合は、余計な情報が必要になる。それらの余計な情報を持つためにfat pointerが採用される)

// * Sizedは実装を持たない「マーカートレイト」の一種であり、言語処理系によって特別扱いされている
