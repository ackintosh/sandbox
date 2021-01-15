// Why all the types in rust libraries have `inner` type ? : rust
// https://www.reddit.com/r/rust/comments/8q0il3/why_all_the_types_in_rust_libraries_have_inner/

// 例
// https://github.com/sigp/lighthouse/blob/a62dc65ca49676e4f2d812bca21294aed6ef2d9c/testing/simulator/src/local_network.rs#L24

use std::sync::Arc;
use std::ops::Deref;

#[derive(Debug)]
struct Foo {
    inner: Arc<Inner>,
}

impl Foo {
    fn new() -> Self {
        Self {
            inner: Arc::new(Inner {
                elements: vec![],
            }),
        }
    }
}

// Deref(Target = Inner)を実装することで、暗黙的にFooがInnerの(イミュータブルな)メソッドを実装することになる
// https://doc.rust-lang.org/stable/std/ops/trait.Deref.html#more-on-deref-coercion
// 例
// https://github.com/sigp/lighthouse/blob/a62dc65ca49676e4f2d812bca21294aed6ef2d9c/testing/simulator/src/local_network.rs#L36
impl Deref for Foo {
    type Target = Inner;

    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

#[derive(Debug)]
struct Inner {
    elements: Vec<i32>,
}

#[test]
fn test() {
    let foo_instance = Foo::new();
    println!("{:?}", foo_instance);

    // Deref(Target = Inner)を実装しているので、`inner` を挟まずにelementsにアクセス可能
    println!("{:?}", foo_instance.elements);
}
