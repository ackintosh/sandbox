// P.111 デッドロックとなるRwLock その1

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
        // Readロックを獲得
        let flag = val.read().unwrap();

        if *flag {
            // Readロック獲得中にWriteロックを獲得しようとしてデッドロックしてしまう
            *val.write().unwrap() = false;
            println!("flag is true");
        }
    });

    handle.join().unwrap();
}

// deadlockを解決したコード
fn no_deadlock() {
    let val = Arc::new(RwLock::new(true));

    let handle = std::thread::spawn(move || {
        // *** Readロックを獲得して、値を取り出したあとに即座にReadロックを解放する ***
        let flag = *val.read().unwrap();

        if flag {
            *val.write().unwrap() = false;
            println!("flag is true");
        }
    });

    handle.join().unwrap();
}
