// https://docs.rs/async-stream/latest/async_stream/

use std::time::Duration;
use async_stream::stream;
use futures_util::{pin_mut, StreamExt};

#[tokio::test]
async fn ex1() {
    let stream = stream! {
        let mut i = 0;
        loop {
            tokio::time::sleep(Duration::from_millis(100)).await;
            yield i;
            i += 1;
        }
    };

    pin_mut!(stream); // needed for iteration

    while let Some(value) = stream.next().await {
        println!("got {}", value);
        if value == 10 {
            println!("returning.");
            return;
        }
    }
}