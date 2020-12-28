async fn async_add(left: i32, right: i32) -> i32 {
    left + right
}

// async fn は、impl Futureのシンタックスシュガー
// fn something_great_async_function() -> impl Future<Output = i32> {
async fn something_great_async_function() -> i32 {
    // awaitはsync functionの中あるいはasyncブロックの中でしか呼び出せない
    // awaitで、この時点で5という値を取り出せる
    let ans = async_add(2, 3).await;
    println!("ans: {}", ans);
    ans
}

#[test]
fn test() {
    // executor::block_on が、async functionを実行するために必要な関数
    // -> ランタイムの起動ポイント
    //    ランタイムの中でFutureが実行され、評価結果を得ることができる
    futures::executor::block_on(something_great_async_function());
}

