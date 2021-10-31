// https://www.oreilly.co.jp/books/9784873119595/
// 3.8.4 バリア同期

use std::sync::{Arc, Barrier};

#[test]
fn test() {
    // スレッドハンドラを保存するベクタ
    let mut handlers = vec![];

    // 10スレッド分のバリア同期をArcで包む
    let barrier = Arc::new(Barrier::new(10));

    // 10スレッド起動
    for _ in 0..10 {
        let b = barrier.clone();
        let th = std::thread::spawn(move || {
            println!("waiting for barrier...");
            b.wait(); // バリア同期
            println!("finished barrier");
        });
        handlers.push(th);
    }

    for th in handlers {
        th.join().unwrap();
    }
}
