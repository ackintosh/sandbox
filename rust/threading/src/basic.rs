#[test]
fn test() {
    let handle = std::thread::spawn(|| {
        println!("Hello, world!");
    });

    dbg!(handle.join());
}

// スレッドに変数を渡す
#[test]
fn move_variants() {
    let mut handles = vec![];

    for x in 0..10 {
        // `move` で所有権をスレッドに移さないとコンパイルエラーになってしまう
        //   -> スレッドの生存期間はわからないので、変数 x への参照を保証できない
        handles.push(std::thread::spawn(move || {
            println!("Hello, world!: {}", x);
        }));
    }

    for h in handles {
        let _ = h.join();
    }
}
