// Ownership and moves - Rust By Example
// https://doc.rust-lang.org/rust-by-example/scope/move.html

mod example {
    #[test]
    fn test() {
        ////////////////////////////////////////////////////////////////
        // スタックに変数が配置される
        let a = 5u32;
        // 関数に *コピー* が渡される (変数 a の所有権の移動は起きない)
        take_ownership(a);
        // aはmoveしていないので利用できる
        println!("main: {}", a);


        ////////////////////////////////////////////////////////////////
        // ヒープに配置する
        let boxed = Box::new(5u32);
        // 変数boxedの所有権が移動する
        take_ownership2(boxed);
        // boxedはmoveしているので使用不可能
        // println!("{}", boxed);
        // error[E0382]: borrow of moved value: `boxed`
        //   --> primitives/src/ownership.rs:17:20
        //    |
        // 14 |     let boxed = Box::new(5u32);
        //    |         ----- move occurs because `boxed` has type `std::boxed::Box<u32>`, which does not implement the `Copy` trait
        // 15 |     take_ownership2(boxed);
        //    |                     ----- value moved here
        // 16 |
        // 17 |     println!("{}", boxed);
        //    |                    ^^^^^ value borrowed here after move
    }

    fn take_ownership(a: u32) {
        println!("take_ownership: {}", a);
    }

    fn take_ownership2(a: Box<u32>) {
        println!("take_ownership2: {}", a);
    }
}


mod example2 {
    // use std::collections::HashMap;

    // 下記の `Introduction` にある map の例の Rust バージョン
    // Data Race Detector - The Go Programming Language
    // https://golang.org/doc/articles/race_detector.html

    // 下記のエラーでコンパイルできない
    // error[E0382]: borrow of moved value: `m`
    //   --> primitives/src/ownership.rs:55:9
    //    |
    // 49 |         let mut m = HashMap::new();
    //    |             ----- move occurs because `m` has type `std::collections::HashMap<&str, &str>`, which does not implement the `Copy` trait
    // 50 |
    // 51 |         let h = std::thread::spawn(move || {
    //    |                                    ------- value moved into closure here
    // 52 |             m.insert("1", "a");
    //    |             - variable moved due to use in closure
    // ...
    // 55 |         m.insert("2", "b");
    //    |         ^ value borrowed here after move

    // #[test]
    // fn test() {
    //     let mut m = HashMap::new();
    //
    //     let h = std::thread::spawn(move || {
    //         m.insert("1", "a");
    //     });
    //
    //     m.insert("2", "b");
    //     h.join();
    //     println!("{:?}", m);
    // }
}
