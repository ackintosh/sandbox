use futures::task::SpawnExt;
use futures::executor::block_on;
use futures::FutureExt;

// https://crates.io/crates/futures
// M:Nモデルのスレッドプール
#[test]
fn test() {
    handle();
    tx_rx();
}

// //////////////////////////////////////////////////////////
// handleを使ってスレッドの処理が終わるのを待つパターン
// //////////////////////////////////////////////////////////
fn handle() {
    let thread_pool = futures::executor::ThreadPool::builder()
        .pool_size(5)
        .name_prefix("ackintosh-sandbox-")
        .create()
        .unwrap();

    // async関数
    async fn print_number(n: u32) {
        println!("print_number: {}", n);
    }

    let mut futures = Vec::new();
    for n in 0..4 {
        futures.push(
            thread_pool.spawn_with_handle(print_number(n)).unwrap()
        );
    }
    // 各スレッドの処理が終わるの待つ
    block_on(futures::future::join_all(futures));
}

// //////////////////////////////////////////////////////////
// channelでやり取りするパターン
// //////////////////////////////////////////////////////////
fn tx_rx() {
    let thread_pool = futures::executor::ThreadPool::builder()
        .pool_size(5)
        .name_prefix("ackintosh-sandbox-")
        .create().unwrap();

    let (mut sender, receiver) = futures::channel::oneshot::channel::<String>();

    thread_pool.spawn_ok(async {
        sender.send("ok".to_owned());
    });

    let r = async {
        receiver.await.unwrap();
    }.left_future::<String>();
}
