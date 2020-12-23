#[test]
fn format() {
    // 10進数 -> 16進数
    assert_eq!("20", format!("{:x}", 32));
}
