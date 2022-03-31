// ////////////////////////////////////////
// https://github.com/tokio-rs/console
//
// Announcing Tokio Console 0.1 | Tokio - An asynchronous Rust runtime
// https://tokio.rs/blog/2021-12-announcing-tokio-console
//
// 公式サンプル
// https://github.com/tokio-rs/console/tree/main/console-subscriber/examples
// - `cd examples`
// - `cargo run --example app`
// - 別ウィンドウで `tokio-console`
// ////////////////////////////////////////

// 参考:
// tokio-console: topみたいなRustのコマンドラインツール
// https://zenn.dev/tfutada/articles/4dbb9659bb8102

// *** tokio-consoleの利用手順 ***
// https://github.com/tokio-rs/console#using-it
// - Cargo.toml に `console-subscriber` を追加
// - .cargo/config.toml の設定を追加
// - main関数に `console_subscriber::init()` を追加
// - tokio-consoleツールをインストールする
//   - `cargo install tokio-console`

use std::time::Duration;

// *** tokioはデフォルトで論理CPU数分のワーカースレッドを生成する ***
// CPU数を確認するコマンド(MacOS)
// $ sysctl hw.physicalcpu hw.logicalcpu
//    hw.physicalcpu: 10
//    hw.logicalcpu: 10
#[tokio::main]
// *** ワーカースレッド数をtokio::mainで変更することが可能 ***
// #[tokio::main(flavor = "multi_thread", worker_threads = 10)]
// *** Node.jsのようにシングルスレッドにすることも可能 ***
// #[tokio::main(flavor = "current_thread")]
async fn main() {
    // /////////////////////////
    // 下記記事のサンプルコード
    // https://zenn.dev/tfutada/articles/4dbb9659bb8102#%E3%82%B5%E3%83%B3%E3%83%97%E3%83%AB%E3%83%97%E3%83%AD%E3%82%B0%E3%83%A9%E3%83%A0
    // /////////////////////////

    console_subscriber::init();

    // 論理CPU数の取得
    let cpus = num_cpus::get();

    let mut handles = vec![];

    // Task A: ノンブロッキング スリープ
    let task_a = tokio::task::Builder::new().name("Task A").spawn(async {
        loop {
            println!(
                "      =Task A sleeping... {:?}",
                std::thread::current().id()
            );
            // ノンブロッキングの sleep (tokio::time の sleep)
            tokio::time::sleep(Duration::from_secs(1)).await;
            println!("      =Task A woke up.");
        }
    });
    handles.push(task_a);

    // Task B-n: ブロッキング スリープ
    for i in 0..cpus + 1 {
        let task_b = tokio::task::Builder::new()
            .name(&format!("Task B-{}", i))
            .spawn(async move {
                loop {
                    println!(
                        "#Task B-{} sleeping... {:?}",
                        i,
                        std::thread::current().id()
                    );
                    // ブロッキングの sleep (標準ライブラリの sleep)
                    std::thread::sleep(Duration::from_secs(5));
                    println!("#Task B-{} woke up.", i);
                }
            });
        handles.push(task_b);
    }

    futures::future::join_all(handles).await;
}
