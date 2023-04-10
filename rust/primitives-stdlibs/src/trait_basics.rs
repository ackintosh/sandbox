use std::fmt::Debug;

// Composite trait for a request id.
pub trait ReqId: Debug + Copy {}
impl<T> ReqId for T where T: Debug + Copy {}

#[derive(Debug, Copy, Clone)]
struct Foo;

#[derive(Debug, Copy, Clone)]
enum Bar {
    A,
    B,
}

#[test]
fn test() {
    let s = Foo;
    // Foo や Bar は Debug, Copy を実装しているので引数に渡せる
    foo(s);
    foo(Bar::A);
    foo(Bar::B);
}

fn foo<T: ReqId>(req: T) {
    println!("{:?}", req);
}
