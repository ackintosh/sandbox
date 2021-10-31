// https://www.oreilly.co.jp/books/9784873119595/
// 3.8.1 ミューテックス

use std::sync::{Arc, Mutex};

fn some_func(lock: Arc<Mutex<u64>>) {
    loop {
        // ロックしないとMutex型の中の値は参照不可
        let mut val = lock.lock().unwrap();
        *val += 1;
        println!("{}", *val);
    }
}

#[test]
fn test() {
    // * Mutex用の変数は保護対象のデータを保持するようになっており、ロックしなければ保護対象データにアクセスできなようになっている
    //   * これによって、コンパイル時に共有リソースへの不正なアクセスを防ぐことができるように設計されている
    //   * さらに、保護対象データがスコープを外れたときに、自動的にロックを開放するようになっている。そのため、ロックの解放忘れを防げる
    let lock0 = Arc::new(Mutex::new(0));

    // 参照カウンタがインクリメントされるのみで中身はクローンされない
    let lock1 = lock0.clone();

    // スレッド生成
    // クロージャ内変数へmove
    let th0 = std::thread::spawn(move || {
        some_func(lock0);
    });

    // スレッド生成
    // クロージャ内変数へmove
    let th1 = std::thread::spawn(move || {
        some_func(lock1);
    });

    // 待ち合わせ
    th0.join().unwrap();
    th1.join().unwrap();
}
