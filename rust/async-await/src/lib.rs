use futures::executor::ThreadPool;
use futures::task::SpawnExt;

// ////////////////////////////////////////////////////////
// async関数
// ////////////////////////////////////////////////////////
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
    // awaitはFutureが完了するのを待つ
    // スレッドはブロックせずに、非同期に待機する
    println!("{}", get_and_plus_1().await);
}

// ////////////////////////////////////////////////////////
// main関数と同じスレッドで呼び出す
// ////////////////////////////////////////////////////////
#[test]
fn block_on() {
    // main関数から呼び出すために futures クレートを使う
    futures::executor::block_on(print_async_fn_result());
}

// ////////////////////////////////////////////////////////
// join
// https://rust-lang.github.io/async-book/01_getting_started/04_async_await_primer.html
// ////////////////////////////////////////////////////////
mod join {
    async fn learn_song() {
        println!("learn_song!");
    }

    async fn sing_song() {
        println!("sing_song!");
    }

    async fn learn_and_sing() {
        // 必ず、learn_song() のあとに sing_song() を実行する
        learn_song().await;
        sing_song().await;
    }

    async fn dance() {
        println!("dance!");
    }

    async fn async_main() {
        // learn_and_sing() と dance() は非同期に行う
        let future1 = learn_and_sing();
        let future2 = dance();

        // join
        futures::future::join(future1, future2);
    }

    #[test]
    fn join() {
        futures::executor::block_on(async_main());
    }
}

// ////////////////////////////////////////////////////////
// thread poolを使って非同期に処理する
// ////////////////////////////////////////////////////////
#[test]
fn thread_pool() {
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
    futures::executor::block_on(futures::future::join_all(futures));
}

// ////////////////////////////////////////////////////////
// asyncブロックはそれぞれに独自の型を持つ
// ////////////////////////////////////////////////////////
#[test]
fn async_blocks_have_their_own_types() {
    // https://users.rust-lang.org/t/storing-futures/34564
    let f1 = async { println!("f1") };
    let f2 = async { println!("f2") };

    // asyncブロックはそれぞれに独自の型を持つので、コンパイルエラーになる
    // let futures = vec![f1, f2];
    // 67 |     let futures = vec![f1, f2];
    //    |                            ^^ expected generator, found a different generator
    //    |
    //    = note: expected type `impl core::future::future::Future` (generator)
    //               found type `impl core::future::future::Future` (generator)
}
