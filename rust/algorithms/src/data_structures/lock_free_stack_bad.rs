// 並行プログラミング入門 https://www.oreilly.co.jp/books/9784873119595/
// 7.3.1 ロックフリースタック
// ロックフリースタックでは、push と pop 操作は CAS 操作を用いてアトミックに行われるため、
// 排他ロックを用いずに複数のプロセス間でのデータ共有と更新ができる

// *************************************************
// ※このコードは正しく動作しない場合がある※
// -> ある特殊な条件が揃ったときにABA問題が発生する
//    ABA問題を回避する方法のひとつは、LL/SC命令を用いるために、ポインタ操作をインラインアセンブリで実装する必要がある
// -> https://kumagi.hatenablog.com/entry/concurrent-programming-book
//    ロックフリースタックにおいてABA問題が発生する真の理由は解放済みメモリを使いまわしている事であり、GCが適切に走ればここに問題は起きない。
//    なので「LL/SCを用いればLock-Free StackのABA問題が解決できる」という説明順序にはせず、EBRで良いので簡単な局所GCを実装してABA問題を解決して欲しかった、
//    またタグを使ったABA避けはポインタ内でのタグが循環すると依然としてABA問題は（特にポインタに埋め込む方法だと）確率的に起きうるのでこれは解決ではなく緩和である。
//    実はLL/SCを使うとそもそも絶対にロックフリーにはならないので、LL/SCを用いたロックフリースタックは存在し得ない。
//    なぜならLoadLinked命令で付けられた目印は書き換えが起きなくてもキャッシュが揮発したり同じキャッシュラインで全く別件の書き込みがあったりすると消えるので論理衝突がなくてもStoreConditionalが失敗することはありえて、
//    スケジューラがちょっと悪さをすれば進行保証は守れなくなるのである。
// *************************************************

use std::ptr::null_mut;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Arc;

// スタックのノード. リスト構造で管理する
struct Node<T> {
    // 次ノードへのポインタ
    next: AtomicPtr<Node<T>>,
    data: T,
}

pub struct Stack<T> {
    // スタックの先頭ノードへのポインタ
    // この変数の値をアトミックに更新することで、アトミックなスタックの push と pop を実現する
    head: AtomicPtr<Node<T>>,
}

impl<T> Stack<T> {
    pub fn new() -> Self {
        Stack {
            head: AtomicPtr::new(null_mut()),
        }
    }

    // *** push ***
    // スタックに追加する Node を作成し、下記操作をアトミックに行う
    // 1. その新規 Node の next に、現在の head を設定する
    // 2. head に、新規 Node を設定する
    pub fn push(&self, v: T) {
        // 追加するノードを作成
        let node = Box::new(Node {
            next: AtomicPtr::new(null_mut()),
            data: v,
        });

        // Box型の値からポインタを取り出す
        let ptr = Box::into_raw(node);

        unsafe {
            // アトミックにヘッドを更新する
            loop {
                // headの値を取得
                let head = self.head.load(Ordering::Relaxed);

                // 追加するノードの next を、現在の head に設定する
                (*ptr).next.store(head, Ordering::Relaxed);

                // headの値が更新されていなければ、追加するノードに更新する
                // CAS操作を行う
                // -> head の値が変わっていないことを調べることで、head 変数の取得と更新中に他のノードによって
                //    head 変数が更新されていないことを確認できる
                if let Ok(_) = self.head.compare_exchange_weak(
                    head,              // 値が head なら
                    ptr,               // ptr に更新する
                    Ordering::Release, // 成功時のオーダー
                    Ordering::Relaxed, // 失敗時のオーダー
                ) {
                    break;
                }
            }
        }
    }

    // *** pop ***
    // 下記の操作をアトミックに行う
    // 1. 現在の head.next を、head に設定する
    // 2. 古い head を dealloc する
    pub fn pop(&self) -> Option<T> {
        unsafe {
            // アトミックにヘッドを更新する
            loop {
                // headの値を取得
                let head = self.head.load(Ordering::Relaxed);
                if head == null_mut() {
                    // head が null なのでスタックに何もデータが無い
                    return None;
                }

                // head.nextを取得
                let next = (*head).next.load(Ordering::Relaxed);

                // CAS操作で head の値を更新する
                // headの値が更新されていなければ、
                // head.nextを新たな head に更新する
                if let Ok(_) = self.head.compare_exchange_weak(
                    head,              // 値が head なら
                    next,              // next に更新する
                    Ordering::Acquire, // 成功時のオーダー
                    Ordering::Relaxed, // 失敗時のオーダー
                ) {
                    // ポインタを Box に戻して、中の値を返す
                    // このようにすることで、ヒープ上にあるデータのライフタイムが、再び Rust のコンパイラによって管理されるようになる
                    let h = Box::from_raw(head);
                    return Some((*h).data);
                }
            }
        }
    }
}

impl<T> Drop for Stack<T> {
    fn drop(&mut self) {
        // データ削除
        let mut node = self.head.load(Ordering::Relaxed);
        while node != null_mut() {
            // ポインタを Box に戻す操作を繰り返す
            let n = unsafe { Box::from_raw(node) };
            node = n.next.load(Ordering::Relaxed);
        }
    }
}

const NUM_LOOP: usize = 1000000;
const NUM_THREADS: usize = 4;

// 下記のテストを実行すればABA問題が発生するはず
// (NUM_LOOPを少ない数に変えるとテストがパスする)
// #[test]
fn test() {
    let stack = Arc::new(Stack::<usize>::new());
    let mut handles = vec![];

    for i in 0..NUM_THREADS {
        let stack0 = stack.clone();

        let h = std::thread::spawn(move || {
            if i & 1 == 0 {
                // 偶数スレッドは push
                for j in 0..NUM_LOOP {
                    let k = i * NUM_LOOP + j;
                    stack0.push(k);
                    println!("push: {}", k);
                }
                println!("finished push: #{}", i);
            } else {
                // 奇数スレッドは pop
                for _ in 0..NUM_LOOP {
                    loop {
                        // pop の結果が None の場合はやり直す
                        if let Some(k) = stack0.pop() {
                            println!("pop: {}", k);
                            break;
                        }
                    }
                }
                println!("finished pop: #{}", i);
            }
        });

        handles.push(h);
    }

    for h in handles {
        h.join().unwrap();
    }

    assert!(stack.pop() == None);
}
