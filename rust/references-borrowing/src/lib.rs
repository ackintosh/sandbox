fn borrowing() {
    // 引数に参照を受け取る ( = 借用)
    // 可変の参照を受け取る
    fn decorate(s: &mut String) {
        s.push_str(", world");
        println!("{}", s)
        // Hello, world
    }

    // 可変の変数
    let mut s = String::from("Hello");

    // 可変の参照
    let ref_s = &mut s;
    // 同一スコープ、同一変数の可変参照は1つしか持てない ( -> データ競合を回避)
    // let ref_s2 = &mut s; // コンパイルエラー
    decorate(ref_s);

    println!("{}", s);
    // Hello, world
}

#[cfg(test)]
mod tests {
    #[test]
    fn borrowing() {
        super::borrowing();
    }
}
