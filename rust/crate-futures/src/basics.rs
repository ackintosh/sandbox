use std::pin::Pin;

struct CountDown(u32);

impl std::future::Future for CountDown {
    type Output = String;

    fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context) -> std::task::Poll<String> {
        if self.0 == 0 {
            std::task::Poll::Ready("Zero!".to_owned())
        } else {
            // スレッドIDも確認
            println!(
                "poll: {}, thread: {:?}",
                self.0,
                std::thread::current().id()
            );
            self.0 -= 1;
            cx.waker().wake_by_ref();
            std::task::Poll::Pending
        }
    }
}

#[test]
fn test() {
    let countdown_future1 = CountDown(10);
    let countdown_future2 = CountDown(20);

    let countdown_set = futures::future::join_all(vec![countdown_future1, countdown_future2]);
    // futures::executor::block_on()
    // 渡したFutureが完了になるまでブロックして待つ
    let results = futures::executor::block_on(countdown_set);

    for (i, s) in results.iter().enumerate() {
        println!("{}: {}", i, s);
    }
}
