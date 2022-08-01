////////////////////////////////////////////
// 2つの構造体がお互いをフィールドに保持する再帰構造
////////////////////////////////////////////

// error[E0072]: recursive type `trait_box::Foo` has infinite size
//   --> references-borrowing/src/trait_box.rs:18:1
//    |
// 18 | struct Foo {
//    | ^^^^^^^^^^ recursive type has infinite size
// 19 |     inner: Bar,
//    |            --- recursive without indirection
//    |
// help: insert some indirection (e.g., a `Box`, `Rc`, or `&`) to make `trait_box::Foo` representable
//    |
// 19 |     inner: Box<Bar>,
//    |            ^^^^   ^

#[allow(unused)]
#[derive(Debug)]
struct Foo {
    inner: Box<Bar>, // Boxで包むことで、コンパイル時にサイズが決まる必要がなくなるので、コンパイルエラーが出なくなる
}

#[derive(Debug)]
enum Bar {
    BarWithFoo(Foo), // Fooを再帰的に持っている
    BarWithBaz(Baz),
}

#[derive(Debug)]
struct Baz {}

#[test]
fn test() {
    println!(
        "{:?}",
        Foo {
            inner: Box::new(Bar::BarWithFoo(Foo {
                inner: Box::new(Bar::BarWithBaz(Baz {}))
            }))
        }
    );
}
