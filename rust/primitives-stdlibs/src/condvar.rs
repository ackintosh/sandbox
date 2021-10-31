// https://www.oreilly.co.jp/books/9784873119595/
// 3.8.2 条件変数

use std::sync::{Arc, Condvar, Mutex};

// Condvar型の変数が条件変数であり、
// MutexとCondvarを含むタプルがArcに包んで渡される
fn child(id: u64, p: Arc<(Mutex<bool>, Condvar)>) {
    let &(ref lock, ref cvar) = &*p;

    // まず、ミューテックスロックを行う
    let mut started = lock.lock().unwrap();
    while !*started {
        // Mutex中の共有変数が false の間ループする
        // 通知があるまでwaitで待機する
        println!("child {}: waiting for cvar...", id);
        started = cvar.wait(started).unwrap();
    }

    // 以下のように wait_while を使うことも可能
    // cvar.wait_while(started, |started| !*started).unwrap();

    println!("child {}", id);
}

// 通知スレッド用関数
fn parent(p: Arc<(Mutex<bool>, Condvar)>) {
    let &(ref lock, ref cvar) = &*p;

    // まず、ミューテックスロックを行う
    let mut started = lock.lock().unwrap();
    *started = true; // 共有変数を更新する
    println!("parent: notify_all");
    cvar.notify_all(); // 通知する
}

#[test]
#[allow(clippy::mutex_atomic)] // Mutex<bool> の代わりに AtomicBool を使うよう警告が出るので抑制しておく
fn test() {
    // ミューテックスと条件変数を作成する
    // 補足: Mutex<bool> の場合は、代わりに AtomicBool を使うのが推奨されている
    //      https://rust-lang.github.io/rust-clippy/master/index.html#mutex_atomic
    let pair0 = Arc::new((Mutex::new(false), Condvar::new()));
    let pair1 = pair0.clone();
    let pair2 = pair0.clone();

    let c0 = std::thread::spawn(move || child(0, pair0));
    let c1 = std::thread::spawn(move || child(1, pair1));
    let p = std::thread::spawn(move || parent(pair2));

    c0.join().unwrap();
    c1.join().unwrap();
    p.join().unwrap();
}
