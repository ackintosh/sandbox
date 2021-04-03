#[test]
fn assertions() {
    let a = 1;
    let b = 2;

    // assert! でも意味は同じだけど、
    // assert_ne! なら、panic時にそれぞれの値をデバッグ出力してくれる
    // assert!(a != b);
    assert_ne!(a, b);
}
