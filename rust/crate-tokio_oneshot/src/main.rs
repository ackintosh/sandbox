// 並行プログラミング入門 https://www.oreilly.co.jp/books/9784873119595/
// 5.4 非同期ライブラリ

// 将来のどこかのタイミングで値が決定される関数を定義している
async fn set_val_later(tx: tokio::sync::oneshot::Sender<i32>) {
    // 単純にスリープのみ
    let ten_secs = std::time::Duration::from_secs(10);
    tokio::time::sleep(ten_secs).await; // tokioが用意する sleep を使う。標準のsleepを使ってしまうとスレッドを無駄に専有してしまうので注意

    if let Err(e) = tx.send(100) {
        println!("Failed to send: {}", e);
    }
}

// oneshotを用いると、将来のどこかのタイミングで値が決定される変数を、通常の変数のように扱うことができる
// ただし、送信か受信側の片方のみが破棄された場合は逆側の端点で受信/送信を行おうとするとエラーになる
#[tokio::main]
async fn main() {
    let (tx, rx) = tokio::sync::oneshot::channel();

    tokio::spawn(set_val_later(tx));

    match rx.await {
        Ok(n) => {
            println!("n = {}", n);
        }
        Err(e) => {
            println!("Failed to receive: {}", e);
        }
    }
}
