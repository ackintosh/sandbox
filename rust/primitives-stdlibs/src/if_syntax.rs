#[test]
fn basics() {
    // | も || もこの場合は同じ結果
    // 付録B：演算子と記号 - The Rust Programming Language 日本語版
    // https://doc.rust-jp.rs/book-ja/appendix-02-operators.html#%E6%BC%94%E7%AE%97%E5%AD%90
    if true | true {
        println!("0");
    }

    if true | false {
        println!("1");
    }

    if false | true {
        println!("2");
    }

    if false | false {
        println!("3");
    }
}
