// cargo test --features test_conditional_compilation
// cargo test --all-features test_conditional_compilation
// でfeatureを有効にする
#[test]
fn test() {
    let s = if cfg!(feature = "test_conditional_compilation") {
        "enabled"
    } else {
        "disabled"
    };


    println!("{}", s);
    // assert_eq!("disabled", s);
}
