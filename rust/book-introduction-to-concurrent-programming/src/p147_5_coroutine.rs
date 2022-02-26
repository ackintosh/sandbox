// 並行プログラミング入門 https://www.oreilly.co.jp/books/9784873119595/
// 5.2.1 コルーチン

// Rust言語にはコルーチンはないが、同等の動作をする関数は実装可能

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 関数の状態を保持する型
struct Hello {
    state: StateHello,
    // 必要に応じて、変数も持たせる
}

// 関数の実行状態を示す
enum StateHello {
    HELLO,
    WORLD,
    END,
}

impl Hello {
    fn new() -> Self {
        Hello {
            state: StateHello::HELLO, // 初期状態
        }
    }
}

impl Future for Hello {
    type Output = ();

    // 実行関数: 実際の関数呼び出し
    // * poll 関数では関数の状態に応じて必要なコードを実行して内部的に状態遷移を行っている
    // * 関数が再実行可能な場合 poll 関数は Poll::Pending を返し、全て終了した場合は Poll::Ready に返り血を含んでリターンする
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        match (*self).state {
            StateHello::HELLO => {
                print!("Hello, ");
                // WORLD状態に遷移
                (*self).state = StateHello::WORLD;
                Poll::Pending // 再度呼び出し可能
            }
            StateHello::WORLD => {
                print!("World!");
                // END状態に遷移
                (*self).state = StateHello::END;
                Poll::Pending // 再度呼び出し可能
            }
            StateHello::END => {
                Poll::Ready(()) // 終了
            }
        }
    }
}

// ////////////////////
// Hello, Worldを実行する
// ////////////////////
#[cfg(test)]
mod tests {
    use super::*;
    use futures::future::BoxFuture;
    use futures::task::{waker_ref, ArcWake};
    use futures::FutureExt;
    use std::sync::{Arc, Mutex};

    // 実行単位
    struct Task {
        hello: Mutex<BoxFuture<'static, ()>>,
    }

    impl Task {
        fn new() -> Self {
            let hello = Hello::new();
            Task {
                hello: Mutex::new(hello.boxed()),
            }
        }
    }

    // 何もしない
    impl ArcWake for Task {
        fn wake_by_ref(_arc_self: &Arc<Self>) {
            // 何もしない
        }
    }

    #[test]
    fn test() {
        // 初期化
        let task = Arc::new(Task::new());
        let waker = waker_ref(&task);
        let mut ctx = Context::from_waker(&waker);
        let mut hello = task.hello.lock().unwrap();

        // 停止と再開の繰り返し
        {
            let poll = hello.as_mut().poll(&mut ctx);
            // "Hello, " が出力され、 Poll::Pending が返ってくる
            assert!(poll.is_pending());
        }
        {
            let poll = hello.as_mut().poll(&mut ctx);
            // "World!" が出力され、 Poll::Pending が返ってくる
            assert!(poll.is_pending());
        }
        {
            let poll = hello.as_mut().poll(&mut ctx);
            // Poll::Ready が返ってくる
            assert!(poll.is_ready());
            if let Poll::Ready(result) = poll {
                // 返り値は `()`
                assert_eq!((), result);
            } else {
                unreachable!()
            }
        }
    }
}
