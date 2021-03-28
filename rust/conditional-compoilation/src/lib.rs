// cargo test --features test_conditional_compilation
// でfeatureを有効にするとテストが失敗する
#[test]
fn test() {
    let s = if cfg!(feature = "test_conditional_compilation") {
        "enabled"
    } else {
        "disabled"
    };

    assert_eq!("disabled", s);
}
