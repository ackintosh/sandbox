#[test]
fn assertions() {
    let a = 1;
    let b = 2;

    // assert! でも意味は同じだけど、
    // assert_ne! なら、panic時にそれぞれの値をデバッグ出力してくれる
    // assert!(a != b);
    assert_ne!(a, b);
}

// ドキュメントのサンプル
// https://doc.rust-jp.rs/the-rust-programming-language-ja/1.6/book/macros.html
macro_rules! foo {
    (x => $e:expr) => (println!("mode X: {}", $e));
    (y => $e:expr) => (println!("mode Y: {}", $e));
}

#[test]
fn test_foo() {
    foo!(x => 3); // mode X: 3
    foo!(y => 3); // mode Y: 3

    // zはマクロに定義していないのでコンパイルエラー
    // foo!(z => 3);
    // error: no rules expected the token `z`
    //   --> macros/src/lib.rs:23:10
    //    |
    // 14 | macro_rules! foo {
    //    | ---------------- when calling this macro
    // ...
    // 23 |     foo!(z => 3);
    //    |          ^ no rules expected this token in macro call
}