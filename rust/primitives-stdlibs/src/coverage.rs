// Rust 1.60で source-based code coverage が安定化された

// Rust 1.60を早めに深掘り - OPTiM TECH BLOG
// https://tech-blog.optim.co.jp/entry/2022/04/08/080000)

// Rustの新しいコードカバレッジ/Source-based code coverage
//   -> 2022/4/8 追記
//      coverageを扱えるツールとしては cargo-llvm-cov があり...
// https://qiita.com/dalance/items/69e18fe300760f8d7de0#202248-%E8%BF%BD%E8%A8%98

// ///////////////////////////////////////////
// 実行方法
//
// # *** cargo-llvm-cov のインストール ***
// $ cargo install cargo-llvm-cov
// $ rustup component add llvm-tools-preview
//
// # *** 実行 ***
// $ cd sandbox/rust
// # 下記でテストの実行とカバレッジの計測を行う
// $ cargo llvm-cov --package primitives
// # HTMLで結果を出力する
//   * 出力先については --help を参照
//   * コードのどこがカバーされていないか確認できる
// $ cargo llvm-cov --package primitives --html --open
// # テキストで標準出力に出力する
// $ cargo llvm-cov --package primitives --text
// ///////////////////////////////////////////

#[test]
fn cov() {
    assert!(true);
}
