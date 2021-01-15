#[test]
fn assertions() {
    let a = 1;
    let b = 2;

    // assert! でも意味は同じだけど、
    // assert_ne! なら、panic時にそれぞれの値をデバッグ出力してくれる
    // assert!(a != b);
    assert_ne!(a, b);
}

// ドキュメントのサンプル
// https://doc.rust-jp.rs/the-rust-programming-language-ja/1.6/book/macros.html
#[cfg(test)]
macro_rules! foo {
    (x => $e:expr) => (println!("mode X: {}", $e));
    (y => $e:expr) => (println!("mode Y: {}", $e));
}

#[test]
fn test_foo() {
    foo!(x => 3); // mode X: 3
    foo!(y => 3); // mode Y: 3

    // zはマクロに定義していないのでコンパイルエラー
    // foo!(z => 3);
    // error: no rules expected the token `z`
    //   --> macros/src/lib.rs:23:10
    //    |
    // 14 | macro_rules! foo {
    //    | ---------------- when calling this macro
    // ...
    // 23 |     foo!(z => 3);
    //    |          ^ no rules expected this token in macro call
}

// パターン(pat)
#[cfg(test)]
macro_rules! pat {
    ( $e:expr , $pat:pat ) => {
        match $e {
            $pat => (),
            ref e => panic!("error: {:?}", e)
        }
    };
    ( $e:expr , $pat:pat => $arm:expr ) => {
        match $e {
            $pat => $arm,
            ref e => panic!("error: {:?}", e)
        }
    };
}

#[test]
fn test_pat() {
    #[derive(Debug)]
    enum Foo {
        A,
        B { s: String },
        C { n: u32, s: String },
    }

    ///////////
    // A
    ///////////
    let foo = Foo::A;
    pat!(foo, Foo::A);

    ///////////
    // B
    ///////////
    let foo = Foo::B {s: "foo:s".to_owned()};
    pat!(foo, Foo::B { s });

    let foo = Foo::B {s: "foo:s".to_owned()};
    let s = pat!(foo, Foo::B { s } => s);
    assert_eq!(
        "foo:s".to_owned(),
        s
    );

    let foo = Foo::B {s: "foo:s".to_owned()};
    pat!(foo, Foo::B { s } => assert!(true));

    ///////////
    // C
    ///////////
    let foo = Foo::C {n: 1, s: "foo:s".to_owned()};
    pat!(foo, Foo::C { n, s } => assert!(true));
}
