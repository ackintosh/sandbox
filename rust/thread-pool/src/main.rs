use futures::FutureExt;

fn main() {
    // https://crates.io/crates/futures
    // M:Nモデルのスレッドプール
    let thread_pool = futures::executor::ThreadPool::builder()
        .pool_size(5)
        .name_prefix("ackintosh-sandbox-")
        .create().unwrap();

    let (mut sender, receiver) = futures::channel::oneshot::channel::<String>();

    thread_pool.spawn_ok(async {
        let _ = sender.send("foo".to_owned());
    });

    async move {
        let r = receiver.await;
        println!("{:?}", r);
    }.left_future();
}
