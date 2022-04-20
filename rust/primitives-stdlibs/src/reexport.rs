// Guidance around reexporting · Discussion #176 · rust-lang/api-guidelines
// https://github.com/rust-lang/api-guidelines/discussions/176

// 公開APIのインターフェースで利用している外部クレートはRe-exportする（と良さそう） - Qiita
// https://qiita.com/tasshi/items/c6548fb38f842c769d85

// 下記で `primitives::reexport::Regex` として公開される
pub use regex::Regex;

#[test]
fn test() {
    // crate::reexport::Regex;
}
