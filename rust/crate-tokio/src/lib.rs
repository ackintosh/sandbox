use tokio::runtime::Runtime;

mod channel;
mod either_future;
mod interval;
mod select;

#[test]
fn test() {
    let rt = Runtime::new().unwrap();
    let h = rt.spawn_blocking( {
        println!("aaaaaa");
    });
    // h.await.unwrap();
    rt.shutdown_timeout()
}
