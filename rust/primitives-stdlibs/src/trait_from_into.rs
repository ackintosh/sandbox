// ドキュメント
// https://doc.rust-lang.org/rust-by-example/conversion/from_into.html

#[derive(Debug)]
struct Number {
    value: i32,
}

impl From<i32> for Number {
    fn from(value: i32) -> Self {
        Number { value }
    }
}

#[test]
fn from_i32_to_number() {
    let n = Number::from(10);
    assert_eq!(10, n.value);
}

#[test]
fn i32_into_number() {
    let n: Number = 10_i32.into();
    assert_eq!(10, n.value);
}
