// P.112 デッドロックとなるRwLock その2

use std::sync::{Arc, RwLock};

#[test]
fn test() {
    // デッドロックしてしまうので実行していない
    // deadlock();
    no_deadlock();
}

#[allow(dead_code)]
fn deadlock() {
    let val = Arc::new(RwLock::new(true));

    let handle = std::thread::spawn(move || {
        // Readロックの値を _flag に代入
        let _flag = val.read().unwrap();

        // _flagにReadロックからリターンされた値を保持している
        // そのため、この変数のスコープが外れるまでロックが解放されず、Writeロックを獲得しようとするとデッドロックとなってしまう
        *val.write().unwrap() = false;
        println!("flag is true");
    });

    handle.join().unwrap();
}

// deadlockを解決したコード
fn no_deadlock() {
    let val = Arc::new(RwLock::new(true));

    let handle = std::thread::spawn(move || {
        // Rust は _ という変数に保持された値は即座に破棄する
        // したがって、Read ロックは即座に解放されるため、Write ロックを獲得しようとしてもデッドロックとはならない
        let _ = val.read().unwrap();

        *val.write().unwrap() = false;
        println!("flag is true");
    });

    handle.join().unwrap();
}
