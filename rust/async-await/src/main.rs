use futures::executor::{ThreadPool, block_on};
use futures::task::SpawnExt;

// async関数
async fn get() -> u32 {
    10
}

async fn get_and_plus_1() -> u32 {
    // async関数はFutureを返す
    // Futureはawaitが呼ばれるまで実行されない
    let future = get();

    // awaitはasync関数またはブロックの中でしか呼べない
    future.await + 1
}

async fn print_async_fn_result() {
    println!("{}", get_and_plus_1().await);
}

// awaitはasync関数またはブロックの中でしか呼べないので、
// main関数から呼び出すために futures クレートを使う
fn main() {
    // ////////////////////////////////////////////////////////
    // main関数と同じスレッドで呼び出す
    // ////////////////////////////////////////////////////////
    futures::executor::block_on(print_async_fn_result());


    // ////////////////////////////////////////////////////////
    // thread poolを使って非同期に処理する
    // ////////////////////////////////////////////////////////
    let thread_pool = ThreadPool::builder()
        .pool_size(5)
        .create()
        .unwrap();

    let mut futures = Vec::new();

    for _ in 0..4 {
        futures.push(
            // スレッドをjoinするために spawn_with_handle を使う
            thread_pool.spawn_with_handle(print_async_fn_result()).unwrap()
        );
    }

    // すべてのスレッドの処理が終わるのを待つ
    block_on(futures::future::join_all(futures));
}

