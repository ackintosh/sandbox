#[test]
fn test() {
    let runtime = tokio::runtime::Runtime::new().unwrap();

    runtime.block_on(basic());
    runtime.block_on(stream());
}

///////////////////////////////////////////////
// 基本
///////////////////////////////////////////////
async fn basic() {
    // 先に完了したブランチ(関数)のブロックが実行される
    tokio::select! {
        _ = async_work1() => {
            println!("async_work1() completed first")
        }
        _ = async_work2() => {
            println!("async_work2() completed first")
        }
    }
}

async fn async_work1() {
    println!("hello from async_work1");
}

async fn async_work2() {
    println!("hello from async_work2");
}

///////////////////////////////////////////////
// ストリーム
///////////////////////////////////////////////
// tokio 1.0 で、stream が別のクレート(tokio-stream)に分離したので
// tokio-stream が必要
// https://docs.rs/tokio/1.0.1/tokio/stream/index.html#why-was-stream-not-included-in-tokio-10
use tokio_stream::StreamExt; // ストリームをselectするために必要

async fn stream() {
    let mut stream1 = tokio_stream::iter(vec![1, 2, 3]);
    let mut stream2 = tokio_stream::iter(vec![4, 5, 6]);

    let next = tokio::select! {
        v = stream1.next() => v.unwrap(),
        v = stream2.next() => v.unwrap(),
    };

    // どちらかのストリームの先頭の要素が返る
    assert!(next == 1 || next == 4);
}
