use futures::{FutureExt, StreamExt};
use futures::future::Either;
use rand::Rng;

fn main() {
    futures::executor::block_on(either(1));
    futures::executor::block_on(either(11));

    let mut tokio_runtime = tokio::runtime::Runtime::new().unwrap();
    tokio_runtime.block_on(futures_ordered());
    tokio_runtime.block_on(futures_unordered());
}

async fn either(n: u32) {
    println!("/// either ///");
    let future = if n < 10 {
        async { true }.left_future()
    } else {
        async { false }.right_future()
    };

    if let Either::Left(r) = future {
        let boolean = r.await;
        println!("boolean: {:?}", boolean);
        assert_eq!(boolean, true);
    } else {
        let boolean = future.await;
        println!("boolean: {:?}", boolean);
        assert_eq!(boolean, false);
    }
}

async fn futures_ordered() {
    println!("/// futures_ordered ///");
    let nums = vec![1, 2, 3, 4, 5];

    let futures = nums.iter()
        .map(|n| {
            async move {
                // ランダムな時間待つ
                let mut rng = rand::thread_rng();
                tokio::time::delay_for(
                    std::time::Duration::from_millis(rng.gen_range(1, 1000))
                ).await;

                format!("futures_ordered: {}", n)
            }
        })
        // FuturesOrdered を使うので結果の順番が保証される
        .collect::<futures::stream::FuturesOrdered<_>>();

    futures.collect::<Vec<_>>().then(|a| {
        async move {
            println!("{:?}", a);
        }
    }).await;
    // ***出力***
    // ["futures_ordered: 1", "futures_ordered: 2", "futures_ordered: 3", "futures_ordered: 4", "futures_ordered: 5"]
}

async fn futures_unordered() {
    println!("/// futures_unordered ///");
    let nums = vec![1, 2, 3, 4, 5];

    let futures = nums.iter()
        .map(|n| {
            async move {
                // ランダムな時間待つ
                let mut rng = rand::thread_rng();
                tokio::time::delay_for(
                    std::time::Duration::from_millis(rng.gen_range(1, 1000))
                ).await;

                format!("futures_unordered: {}", n)
            }
        })
        // FuturesUnordered なので結果の順番は保証されない
        .collect::<futures::stream::FuturesUnordered<_>>();

    futures.collect::<Vec<_>>().then(|a| {
        async move {
            println!("{:?}", a);
        }
    }).await;
    // ***出力例***
    // ["futures_unordered: 3", "futures_unordered: 4", "futures_unordered: 1", "futures_unordered: 2", "futures_unordered: 5"]
}
