use std::fmt::Debug;

// Composite trait for a request id.
pub trait ReqId: Debug + Copy + Clone {}
impl<T> ReqId for T where T: Debug + Copy + Clone {}

#[derive(Debug, Copy, Clone)]
struct Foo;

#[test]
fn test() {
    let s = Foo;
    // Foo は Debug, Copy, Clone を実装しているので引数に渡せる
    foo(s);
}

fn foo<T: ReqId>(req: T) {
    println!("{:?}", req);
}
