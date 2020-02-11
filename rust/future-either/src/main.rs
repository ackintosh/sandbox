use futures::{FutureExt, Future};
use futures::future::Either;

fn main() {
    futures::executor::block_on(either(1));
    futures::executor::block_on(either(11));
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
