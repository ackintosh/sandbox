// 並行プログラミング入門 https://www.oreilly.co.jp/books/9784873119595/
// 5.2.2 スケジューリング
// 非対称コルーチンをスケジューリング実行することで、（粒度の高い制御はできなくなるが、）プログラマはコルーチンの管理から解放されより抽象度の高い並行計算が可能になる

use futures::future::BoxFuture;
use futures::task::{waker_ref, ArcWake};
use futures::FutureExt;
use hello::*;
use std::future::Future;
use std::sync::mpsc::{sync_channel, Receiver, SyncSender};
use std::sync::{Arc, Mutex};
use std::task::Context;

// //////////
// Task
// //////////
struct Task {
    // 実行するコルーチン
    // この Future の実行が完了するまで Executor が実行を行う
    future: Mutex<BoxFuture<'static, ()>>,
    // Executor へ Task を渡し、スケジューリングを行うためのチャネル
    sender: SyncSender<Arc<Task>>,
}

// //////////
// Waker
// //////////
// 簡略化のため、Task自身がWakerとなるようにしている
impl ArcWake for Task {
    fn wake_by_ref(arc_self: &Arc<Self>) {
        // 自分自身の Arc 参照を Executor に送信してスケジューリングする
        let self0 = arc_self.clone();
        arc_self.sender.send(self0).unwrap();
    }
}

// //////////
// Spawner
// * Futureを受け取り Task に包んで、実行キューにエンキュー（チャネルに送信）するための型
// * チャネルの送信側端点を保持しているだけ
// //////////
struct Spawner {
    sender: SyncSender<Arc<Task>>,
}

impl Spawner {
    fn spawn(&self, future: impl Future<Output = ()> + 'static + Send) {
        // FutureをBox化
        let future = future.boxed();
        // Taskを生成
        let task = Arc::new(Task {
            future: Mutex::new(future),
            sender: self.sender.clone(),
        });

        // 実行キューにエンキュー
        self.sender.send(task).unwrap();
    }
}

// //////////
// Executor
// //////////
struct Executor {
    // 実行キュー
    sender: SyncSender<Arc<Task>>,
    receiver: Receiver<Arc<Task>>,
}

impl Executor {
    fn new() -> Self {
        // チャネルを生成。キューのサイズは最大 1024 個
        let (sender, receiver) = sync_channel(1024);
        Executor {
            sender: sender.clone(),
            receiver,
        }
    }

    // 新たに Task を生成するための Spawner を作成
    fn get_spawner(&self) -> Spawner {
        // Rustのスレッド生成関数である spawn 関数に相当する動作を行うためのオブジェクトになる
        Spawner {
            sender: self.sender.clone(),
        }
    }

    fn run(&self) {
        // チャネルから Task を受信して実行を行う
        while let Ok(task) = self.receiver.recv() {
            // コンテキストを生成
            let mut future = task.future.lock().unwrap();
            // 本実装では Task と Waker は同じであるため、Task から Waker を生成する
            let waker = waker_ref(&task);
            let mut ctx = Context::from_waker(&waker);

            // poll を呼び出し実行
            let _ = future.as_mut().poll(&mut ctx);
        }
    }
}

// p147_5_coroutine.rs を少し変更した -> Future::poll() 関数に2行追加した
mod hello {
    use std::future::Future;
    use std::pin::Pin;
    use std::task::{Context, Poll};

    // 関数の状態を保持する型
    pub struct Hello {
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
        pub fn new() -> Self {
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
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            match (*self).state {
                StateHello::HELLO => {
                    print!("Hello, ");
                    // WORLD状態に遷移
                    (*self).state = StateHello::WORLD;

                    // //////////////////////////////////////
                    // [追加] 自分自身を実行キューにエンキューする
                    // 補足: 本実装では Task と Waker は同じであるため、`cx.waker()` が Task を返す
                    // //////////////////////////////////////
                    cx.waker().wake_by_ref();

                    Poll::Pending // 再度呼び出し可能
                }
                StateHello::WORLD => {
                    print!("World!");
                    // END状態に遷移
                    (*self).state = StateHello::END;

                    // //////////////////////////////////////
                    // [追加] 自分自身を実行キューにエンキューする
                    // 補足: 本実装では Task と Waker は同じであるため、`cx.waker()` が Task を返す
                    // //////////////////////////////////////
                    cx.waker().wake_by_ref();

                    Poll::Pending // 再度呼び出し可能
                }
                StateHello::END => {
                    Poll::Ready(()) // 終了
                }
            }
        }
    }
}

// /////////////
// メインメソッド
// (無限ループなのでコメントアウトしている)
// /////////////
// メインメソッド
// #[test]
// fn test() {
//     let executor = Executor::new();
//     executor.get_spawner().spawn(Hello::new());
//     executor.run();
// }
