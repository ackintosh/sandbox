// * コンパイル条件として `#![cfg(not(debug_assertions))]` を指定しているので、
//   `--release` を指定しない限り、このコードはコンパイル対象にならない
// * このテストを実行するには、 `cargo test --release --test sandbox_tests` のように `--release` オプションをつける
// * debug_assertionsについてのドキュメント
//   https://doc.rust-lang.org/reference/conditional-compilation.html#debug_assertions
// * インテグレーションテストのように広範囲のコードがテストで実行対象になる場合、
//   debug_assertionsによって生成されるデバッグコードによって実行コストが問題になる場合がある
//   その場合は `#![cfg(not(debug_assertions))]` を指定して改善できる

#![cfg(not(debug_assertions))]

#[test]
fn integration_test() {
    println!("integration_test");
    assert!(true);
}
