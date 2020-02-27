use futures::{FutureExt, StreamExt, TryFutureExt};
use futures::future::{Either, BoxFuture};
use rand::Rng;
use futures::stream::FuturesOrdered;

fn main() {
    futures::executor::block_on(either(1));
    futures::executor::block_on(either(11));

    let e = EitherTest {};
    futures::executor::block_on(e.either_functions(vec![0, 1, 2, 3, 4, 5]));

    let mut tokio_runtime = tokio::runtime::Runtime::new().unwrap();
    tokio_runtime.block_on(futures_ordered());
    tokio_runtime.block_on(futures_unordered());

    futures::executor::block_on(futures_boxed(11));
    futures::executor::block_on(futures_ordered_boxed());

    futures::executor::block_on(then());
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

struct EitherTest {
}

impl EitherTest {
    async fn either_functions(self, nums: Vec<i32>) -> Either<BoxFuture<'static, String>, BoxFuture<'static, String>> {
        let mut futures_ordered
            = FuturesOrdered::new();

        for (_i, n) in nums.clone().iter().enumerate() {
            let f = match n {
                1..=3 => {
                    f_plus1(n.clone()).left_future()
                },
                4..=5 => {
                    // f_plus1000 は f_plus1 と返り値の型は同じだけど、下記エラーでコンパイルできない
                    // "expected opaque type, found a different opaque type"
                    // f_plus1000(n.clone()).left_future()

                    f_plus1(n.clone()).left_future()
                },
                0 => futures::future::ready(Ok(999)).right_future(),
                _ => unreachable!()
            };
            futures_ordered.push(f);
        }

        let a = futures_ordered.collect::<Vec<_>>()
            .then(|a| async move {
                println!("{:?}", a);
                "FOO".to_owned()
            });

        a.boxed().right_future()
    }
}

async fn f_plus1(n: i32) -> Result<i32, ()> {
    Ok(n + 1)
}
#[allow(dead_code)]
async fn f_plus1000(n: i32) -> Result<i32, ()> {
    Ok(n + 1000)
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

async fn futures_boxed(n: i32) {
    println!("/// futures_boxed ///");
    // 各asyncブロックはそれぞれ異なる型を持つので、型不一致のエラーになってしまう
    // let f = if n > 10 {
    //     async { true }
    // } else {
    //     async { false }
    // };

    // ** incompatible types エラー **
    // 17 |       let f = if n > 10 {
    //    |  _____________-
    // 18 | |         async { true }
    //    | |         -------------- expected because of this
    // 19 | |     } else {
    // 20 | |         async { false }
    //    | |         ^^^^^^^^^^^^^^^ expected generator, found a different generator
    // 21 | |     };
    //    | |_____- if and else have incompatible types
    //       |
    //    = note: expected type `impl core::future::future::Future` (generator)
    //               found type `impl core::future::future::Future` (generator)

    // boxed() を使うことで、Type erasing できる
    let f = if n > 10 {
        async { true }.boxed()
    } else {
        async { false }.boxed()
    };

    println!("f: {:?}", f.await);
    // f: true
}

async fn futures_ordered_boxed() {
    println!("/// futures_ordered_boxed ///");
    let mut futures_ordered: futures::stream::FuturesOrdered<BoxFuture<i32>> = futures::stream::FuturesOrdered::new();
    futures_ordered.push(async { 1 }.boxed());
    futures_ordered.push(async { 2 }.boxed());
    futures_ordered.push(async { 3 }.boxed());
    futures_ordered.push(async { 4 }.boxed());
    futures_ordered.push(async { 5 }.boxed());

    futures_ordered.collect::<Vec<i32>>().then(|numbers| {
        async move {
            println!("{:?}", numbers);
        }
    }).await;
    // [1, 2, 3, 4, 5]
}

async fn then() {
    ///////////////////////////////////////////////////////////////////////////
    // then()
    ///////////////////////////////////////////////////////////////////////////
    {
        let f = async { 1 };
        assert_eq!(f.then(|x| async move { x + 100 }).await, 101);
    }

    ///////////////////////////////////////////////////////////////////////////
    // and_then()
    ///////////////////////////////////////////////////////////////////////////
    {
        let f = async { Ok::<i32, i32>(1) };
        // f は Ok を返すので and_then() が実行される
        let f = f.and_then(|x| async move { Ok::<i32, i32>(x + 3) });
        assert_eq!(f.await, Ok(4));
    }

    {
        let f = async { Err::<i32, i32>(1) };
        // f は Err を返すので and_then() は実行されない
        let f = f.and_then(|x| async move { Ok::<i32, i32>(x + 3) });
        assert_eq!(f.await, Err(1));
    }

    {
        async fn f1(n: i32) -> Result<i32, i32> {
            if n == 1 {
                Ok(1)
            } else {
                Err(2)
            }
        }
        async fn f2(n: i32) -> Result<i32, i32> {
            Ok(n + 100)
        }

        let f = f1(1).and_then(|x| f2(x));
        assert_eq!(f.await, Ok(101));
    }
}

