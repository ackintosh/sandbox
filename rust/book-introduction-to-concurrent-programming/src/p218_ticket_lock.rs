// 並行プログラミング入門 https://www.oreilly.co.jp/books/9784873119595/
// 7.1.2 チケットロック
// チケットロックでは、ticket の獲得時にスピンを行わないため、他のスレッドとのコンテンションを軽減できる
//    -> 弱い公平性(p212_fair_lock.rs)よりもコンテンションを軽減できる
use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{fence, AtomicUsize, Ordering};
use std::sync::Arc;

// /////////////////////////////////////////////////////////////////////////
// TicketLock
// /////////////////////////////////////////////////////////////////////////
// チケットロック用の型
struct TicketLock<T> {
    // 次のチケット番号を記憶する変数
    // スレッドがチケットを取得する際には、この変数をアトミックにインクリメントする
    ticket: AtomicUsize,
    // 現在実行が許可されているチケット番号
    // ロック獲得を行うスレッドは、この値を監視して自分のチケット番号となったらクリティカルセクションを実行する
    turn: AtomicUsize,
    data: UnsafeCell<T>,
}

impl<T> TicketLock<T> {
    fn new(v: T) -> Self {
        TicketLock {
            ticket: AtomicUsize::new(0),
            turn: AtomicUsize::new(0),
            data: UnsafeCell::new(v),
        }
    }

    // ////////////////////
    // ロック獲得用の関数
    // ////////////////////
    fn lock(&self) -> TicketLockGuard<T> {
        // チケットを取得
        let ticket = self.ticket.fetch_add(1, Ordering::Relaxed);
        // 所有するチケットの順番になるまでスピン
        while self.turn.load(Ordering::Relaxed) != ticket {}
        fence(Ordering::Acquire);

        TicketLockGuard { ticket_lock: self }
    }
}

// TicketLock型はスレッド間で共有可能に設定する
unsafe impl<T> Sync for TicketLock<T> {} // スレッド間でデータが共有可能になる
unsafe impl<T> Send for TicketLock<T> {} // スレッド間で所有権を送受信可能になる

// /////////////////////////////////////////////////////////////////////////
// TicketLockGuard
// /////////////////////////////////////////////////////////////////////////
// ロック解放と、保護対象データへのアクセスを行うための型
struct TicketLockGuard<'a, T> {
    ticket_lock: &'a TicketLock<T>,
}

// /////////////////////
// アンロックの実装
// /////////////////////
// ロック獲得後に自動で解放されるように Drop トレイトを実装する
impl<'a, T> Drop for TicketLockGuard<'a, T> {
    fn drop(&mut self) {
        // 次のチケットを実行可能に設定する
        self.ticket_lock.turn.fetch_add(1, Ordering::Release);
    }
}

// /////////////////////
// Deref と DerefMut を実装することで、ロック獲得中に保護データへアクセス可能になる
// /////////////////////
// 保護対象データの immutable な参照外し
impl<'a, T> Deref for TicketLockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ticket_lock.data.get() }
    }
}

// 保護対象データの mutable な参照外し
impl<'a, T> DerefMut for TicketLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.ticket_lock.data.get() }
    }
}

// /////////////////////////////////////////////////////////////////////////
// チケットロックの利用例
// /////////////////////////////////////////////////////////////////////////
const NUM_LOOP: usize = 100000;
const NUM_THREADS: usize = 4;
#[test]
fn test() {
    let lock = Arc::new(TicketLock::new(0));
    let mut handles = vec![];

    for _ in 0..NUM_THREADS {
        let lock0 = lock.clone();
        let handle = std::thread::spawn(move || {
            for _ in 0..NUM_LOOP {
                // スレッド番号を渡してロックを獲得する
                let mut data = lock0.lock();
                *data += 1; // TicketLockGuardが Deref, DerefMut を実装しているので参照外しが可能
            }
        });

        handles.push(handle);
    }

    for h in handles {
        h.join().unwrap();
    }

    // COUNT と expected が両方とも同じ値になる
    println!(
        "COUNT = {} (expected = {})",
        *lock.lock(),
        NUM_LOOP * NUM_THREADS
    );
}
