use futures::core_reexport::task::{Poll, Context};

#[test]
fn test() {
    futures::executor::block_on(async {
        let hello_future = futures::future::poll_fn(hello_world);
        println!("{}", hello_future.await);
    });
}

fn hello_world(_cx: &mut Context<'_>) -> Poll<String> {
    // 処理が進行中なら Poll:Pending、処理が完了していれば値と共に Poll::Ready を返す
    // Poll::Pending
    Poll::Ready("Hello, World!".into())
}
