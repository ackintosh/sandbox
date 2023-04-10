// 4.1 デッドロック

// 食事する哲学者問題
// 最後まで実行される場合もあるが、デッドロックとなってしまい実行が進まなくなってしまう場合もある

use std::sync::{Arc, Mutex};

// デッドロックの可能性があるのでコメントアウトしておく
// #[test]
// fn test() {
//     dining_philosophers_problem();
// }

#[allow(dead_code)]
#[allow(clippy::let_underscore_lock)]
fn dining_philosophers_problem() {
    // 箸が2本
    let chopstick1_philosopher1 = Arc::new(Mutex::new(()));
    let chopstick2_philosopher1 = Arc::new(Mutex::new(()));

    let chopstick1_philosopher2 = chopstick1_philosopher1.clone();
    let chopstick2_philosopher2 = chopstick2_philosopher1.clone();

    // 哲学者1
    let philosopher1 = std::thread::spawn(move || {
        for _ in 0..100000 {
            // 1 -> 2 の順に箸を取る(哲学者1から見て左の箸から取る)
            let _unused = chopstick1_philosopher1.lock().unwrap(); // clippy::let_underscore_lock のエラーが出るが抑制している
            let _unused = chopstick2_philosopher1.lock().unwrap();
            println!("philosopher1: eating");
        }
    });

    // 哲学者2
    let philosopher2 = std::thread::spawn(move || {
        for _ in 0..100000 {
            // 哲学者1とは逆に 2 -> 1 の順に箸を取る(哲学者2から見て左の箸から取る)
            let _unused = chopstick2_philosopher2.lock().unwrap();
            let _unused = chopstick1_philosopher2.lock().unwrap();
            println!("philosopher2: eating");
        }
    });

    philosopher1.join().unwrap();
    philosopher2.join().unwrap();
}
