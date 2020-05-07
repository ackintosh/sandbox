use std::time::Duration;

mod lifetime;

#[test]
fn borrowing() {
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

#[test]
fn borrowing_threading() {
    // 可変の変数
    let mut s = String::from("Hello");
    // 可変の参照
    // let ref_s = &mut s;


    let handle = {
        let mut cloned_s = s.clone();

        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(3));

            // `s` の参照(ref_s)だとコンパイルエラー
            // error[E0597]: `s` does not live long enough
            // decorate(ref_s);

            // moveキーワードで、`s` をcloneした文字列(cloned_s)の所有権を持っているのでコンパイルできる
            decorate(&mut cloned_s);

            println!("cloned_s: {}", cloned_s);
        })
    };

    handle.join().unwrap();
    println!("s: {}", s);
}

// 引数に参照を受け取る ( = 借用)
// 可変の参照を受け取る
fn decorate(s: &mut String) {
    s.push_str(", world");
    println!("{}", s);
    // Hello, world
}

