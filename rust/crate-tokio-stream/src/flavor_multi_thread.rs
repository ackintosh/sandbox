// https://zenn.dev/tfutada/articles/5e87d6e7131e8e#2-3-%E3%82%BF%E3%82%B9%E3%82%AF%E3%82%92%EF%BC%92%E3%81%A4%E7%94%9F%E6%88%90%E3%81%97%E3%81%A6%E3%81%BF%E3%82%8B%E3%82%88

use std::time::Duration;

// `worker_threads = 1` を指定しているので
// `メインスレッド` + `ワーカースレッド1` になる
#[tokio::test(flavor = "multi_thread", worker_threads = 1)]
async fn multi_thread() {
    println!("logical cores: {}", num_cpus::get());

    tokio::spawn(async move {
        println!("task 1 started...");
        // 同期スリープ
        std::thread::sleep(Duration::from_secs(3));
        println!("task 1 woke up!");
    });

    tokio::spawn(async move {
        println!("task 2 started...");
        // 同期スリープ
        std::thread::sleep(Duration::from_secs(1));
        println!("task 2 woke up!");
    });

    // この時点でtask2は走らない。空きスレッドがないから。
    std::thread::sleep(Duration::from_secs(5)); // 3秒後にtask2は走る

    println!("Done");
}
