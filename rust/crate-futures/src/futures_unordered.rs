use std::time::Duration;
use futures::stream::{FuturesUnordered, StreamExt};
use tokio::time::{Instant, sleep};

async fn wait(millis: u64) -> u64 {
    sleep(Duration::from_millis(millis)).await;
    millis
}

// https://stackoverflow.com/a/70778511
#[tokio::test]
async fn test() {
    // Futureの集合
    let mut futures = FuturesUnordered::new();
    futures.push(wait(500));
    futures.push(wait(300));
    futures.push(wait(100));
    futures.push(wait(300));

    let start_time = Instant::now();

    let mut num_added = 0;
    while let Some(wait_time) = futures.next().await {
        println!("Waited {}ms", wait_time);
        if num_added < 3 {
            num_added += 1;
            futures.push(wait(200));
        }
    }

    println!("Completed all work in {}ms", start_time.elapsed().as_millis());
}