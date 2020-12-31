use tokio::time::Duration;

#[test]
fn interval() {
    let mut count = 0;
    let runtime = tokio::runtime::Runtime::new().unwrap();
    runtime.block_on(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(2));
        loop {
            interval.tick().await;
            dbg!();
            count += 1;
            if count == 5 {
                break;
            }
        }
    });
}
