// 並行プログラミング入門 https://www.oreilly.co.jp/books/9784873119595/
// 5.4 非同期ライブラリ

// ブロッキング関数
fn do_block(n: u64) -> u64 {
    let ten_secs = std::time::Duration::from_secs(10);

    // std::thread::sleep() を利用しているため、スリープ中であってもワーカスレッドを占有してしまう
    // しかし、spawn_blocking 関数でブロッキング用のスレッドを生成し、そこでこの関数を呼び出しているため、デッドロックに陥ることはない。
    std::thread::sleep(ten_secs);
    n
}

// async関数
async fn do_print() {
    let sec = std::time::Duration::from_secs(1);

    for _ in 0..20 {
        tokio::time::sleep(sec).await;
        println!("wake up");
    }
}

#[tokio::main]
async fn main() {
    // ブロッキング関数の呼び出し
    let mut handles = vec![];
    for n in 0..32 {
        // ブロッキング関数を、ブロッキング処理専用スレッドで呼び出す
        let t = tokio::task::spawn_blocking(move || do_block(n));
        handles.push(t);
    }

    // async関数の呼び出し
    let handle_async = tokio::spawn(do_print());

    for t in handles {
        let n = t.await.unwrap();
        println!("finished: {}", n);
    }

    handle_async.await.unwrap();
}
