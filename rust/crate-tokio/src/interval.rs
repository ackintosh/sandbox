use tokio::time::Duration;
use futures::StreamExt;

#[test]
fn interval() {
    let mut count = 0;
    let mut runtime = tokio::runtime::Runtime::new().unwrap();
    runtime.block_on(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(2));
        while interval.next().await.is_some() {
            dbg!();
            count += 1;
            if count == 5 {
                break;
            }
        }
    });
}
