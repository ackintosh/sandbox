// //////////////////////////
// 宣言的(declarative)マクロ
// 参考:
//   - https://caddi.tech/archives/3555
//   - 公式ドキュメント: https://doc.rust-jp.rs/book-ja/ch19-06-macros.html
//
// - 宣言的マクロは macro_rules! 構文を使用して定義されるマクロで、match 式に似た形で処理内容を定義する
// - vec! や println! など普段良く使うマクロも宣言的マクロ
// //////////////////////////

// ドキュメントのサンプル
// https://doc.rust-jp.rs/the-rust-programming-language-ja/1.6/book/macros.html
#[cfg(test)]
macro_rules! foo {
    (x => $e:expr) => {
        println!("mode X: {}", $e)
    };
    (y => $e:expr) => {
        println!("mode Y: {}", $e)
    };
}

#[test]
fn test_foo() {
    foo!(x => 3); // mode X: 3
    foo!(y => 3); // mode Y: 3

    // zはマクロに定義していないのでコンパイルエラー
    // foo!(z => 3);
    // error: no rules expected the token `z`
    //   --> macros/src/aaa:23:10
    //    |
    // 14 | macro_rules! foo {
    //    | ---------------- when calling this macro
    // ...
    // 23 |     foo!(z => 3);
    //    |          ^ no rules expected this token in macro call
}

// 返り値があるマクロ
#[test]
fn test_return_value() {
    // 文字列を返すだけのマクロ
    macro_rules! return_value {
        () => {{
            let a = "bb";
            format!("{} foo_return_value", a)
        }};
    }

    println!("{}", return_value!());
}

// 第一引数が、第二引数のパターンにマッチするかどうか
#[cfg(test)]
macro_rules! pattern_match {
    // マッチしなければpanic
    ( $e:expr , $pat:pat ) => {
        match $e {
            $pat => (),
            ref e => panic!("error: {:?}", e),
        }
    };
    // マッチした場合の処理を指定できる
    ( $e:expr , $pat:pat => $arm:expr ) => {
        match $e {
            $pat => $arm,
            ref e => panic!("error: {:?}", e),
        }
    };
}

#[test]
#[allow(unused_variables)]
fn test_pattern_match_macro() {
    #[derive(Debug)]
    enum TestEnum {
        A,
        B { s: String },
        C { n: u32, s: String },
    }

    ///////////
    // A
    ///////////
    {
        let a = TestEnum::A;
        pattern_match!(a, TestEnum::A);
    }

    ///////////
    // B
    ///////////
    {
        let b = TestEnum::B {
            s: "foo:s".to_owned(),
        };
        pattern_match!(b, TestEnum::B { s });
    }

    {
        let b = TestEnum::B {
            s: "foo:s".to_owned(),
        };
        let s = pattern_match!(b, TestEnum::B { s } => s);
        assert_eq!("foo:s".to_owned(), s);
    }

    ///////////
    // C
    ///////////
    {
        let c = TestEnum::C {
            n: 1,
            s: "foo:s".to_owned(),
        };
        let msg = pattern_match!(c, TestEnum::C { n, s } => "ok");
        assert_eq!("ok", msg);
    }
}
