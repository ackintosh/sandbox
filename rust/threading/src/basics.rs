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
            // printされる順番は実行するごとに変わるかもしれない
            //   -> それぞれのスレッドがどのような順番で実行されるかについて何ら保証が無いことに注意が必要
            println!("Hello, world!: {}, thread: {:?}", x, std::thread::current());
        }));
    }

    for h in handles {
        let _ = h.join();
    }
}
