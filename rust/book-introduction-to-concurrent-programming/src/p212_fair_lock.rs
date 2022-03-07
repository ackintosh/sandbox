// 並行プログラミング入門 https://www.oreilly.co.jp/books/9784873119595/
// 7.1.1 弱い公平性を担保するロック

use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{fence, AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

// スレッドの最大数
const NUM_LOCK: usize = 8;

// NUM_LOCK の剰余を求めるためのビットマスク
// x % NUM_LOCK を計算するためのビットマスク
// すなわち、 x % NUM_LOCK = x & MASK となる
// よって、 NUM_LOCK は 2n 倍でなければならない
const MASK: usize = NUM_LOCK - 1;

// /////////////////////////////////////////////////////////////////////////
// FairLock
// /////////////////////////////////////////////////////////////////////////
// 公平なロック用の型
struct FairLock<T> {
    // n 番目のスレッドがロック獲得試行中かどうかを示すベクタ
    // n 番目のスレッドがロックを獲得する際は、この waiting[n] を true に設定する
    // また、n 番目以外のスレッドがロック解放を行い、n 番目のスレッドに実行権限を譲るためには waiting[n] を false に設定する
    waiting: Vec<AtomicBool>,
    // スピンロックのための変数
    lock: AtomicBool,
    // ロック獲得を優先するスレッド
    // もし turn 変数の値が 3 だった場合は、3番目のスレッドが優先的にロックを獲得する
    turn: AtomicUsize,
    // 保護対象データを保持する変数
    data: UnsafeCell<T>,
}

// FairLock型はスレッド間で共有可能に設定する
unsafe impl<T> Sync for FairLock<T> {} // スレッド間でデータが共有可能になる
unsafe impl<T> Send for FairLock<T> {} // スレッド間で所有権を送受信可能になる

impl<T> FairLock<T> {
    fn new(v: T) -> Self {
        let mut waiting = vec![];
        for _ in 0..NUM_LOCK {
            waiting.push(AtomicBool::new(false));
        }

        FairLock {
            waiting,
            lock: AtomicBool::new(false),
            data: UnsafeCell::new(v),
            turn: AtomicUsize::new(0),
        }
    }

    // ////////////////////
    // ロック獲得用の関数
    // ////////////////////
    fn lock(&self, thread_idx: usize) -> FairLockGuard<T> {
        assert!(thread_idx < NUM_LOCK);

        // 自身のスレッドをロック獲得試行中に設定する
        self.waiting[thread_idx].store(true, Ordering::Relaxed);

        loop {
            // waitingの自身の値が false になっている場合、
            // 他のスレッドが false を設定した、つまり、他のスレッドが自身に実行権限を移譲したことを意味する
            if !self.waiting[thread_idx].load(Ordering::Relaxed) {
                break;
            }

            // waitingが true のままの場合は、TTASを実行し、共有変数を用いてロック獲得を試みる
            // 他に実行中のスレッドがいない場合や、優先すべきスレッドがロック獲得を試みていない場合は、lock変数を用いたロック獲得を行う
            if !self.lock.load(Ordering::Relaxed) {
                if let Ok(_) = self.lock.compare_exchange_weak(
                    false,             // false なら
                    true,              // true を書き込む
                    Ordering::Relaxed, // 成功時のオーダー
                    Ordering::Relaxed, // 失敗時のオーダー
                ) {
                    break; // ロック獲得
                }
            }
        }

        fence(Ordering::Acquire);

        FairLockGuard {
            fair_lock: self,
            thread_idx,
        }
    }
}

// /////////////////////////////////////////////////////////////////////////
// FairLockGuard
// /////////////////////////////////////////////////////////////////////////
// ロックの解放と、保護対象データへのアクセスを行うための型
struct FairLockGuard<'a, T> {
    fair_lock: &'a FairLock<T>,
    thread_idx: usize, // スレッド番号
}

// /////////////////////
// アンロックの実装
// /////////////////////
impl<'a, T> Drop for FairLockGuard<'a, T> {
    // 実行権限の移譲または、ロックを解放を行う
    fn drop(&mut self) {
        let fair_lock = self.fair_lock;

        // 自身のスレッドを非ロック獲得試行中に設定
        fair_lock.waiting[self.thread_idx].store(false, Ordering::Relaxed);

        // 現在のロック獲得優先スレッドが自分ならば次のスレッドに設定する
        let turn = fair_lock.turn.load(Ordering::Relaxed);
        let next = if turn == self.thread_idx {
            (turn + 1) & MASK
        } else {
            turn
        };

        if fair_lock.waiting[next].load(Ordering::Relaxed) {
            // 次のロック獲得優先スレッドがロック獲得試行中の場合
            // そのスレッドにロックを渡す
            fair_lock.turn.store(next, Ordering::Relaxed);
            fair_lock.waiting[next].store(false, Ordering::Release);
        } else {
            // 次のロック獲得優先スレッドがロック獲得試行中でない場合
            // 次の次のスレッドをロック獲得優先スレッドに設定してロックを解放する
            fair_lock.turn.store((next + 1) & MASK, Ordering::Relaxed);
            fair_lock.lock.store(false, Ordering::Release); // ロックを解放する
        }
    }
}

// /////////////////////
// Deref と DerefMut を実装することで、ロック獲得中に保護データへアクセス可能になる
// /////////////////////
// 保護対象データの immutable な参照外し
impl<'a, T> Deref for FairLockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.fair_lock.data.get() }
    }
}

// 保護対象データの mutable な参照外し
impl<'a, T> DerefMut for FairLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.fair_lock.data.get() }
    }
}

// /////////////////////////////////////////////////////////////////////////
// 公平なロックの利用例
// 基本的には Mutex などと同じだが、ロックを獲得する際に、自身のスレッド番号を指定しなければならない
// /////////////////////////////////////////////////////////////////////////
const NUM_LOOP: usize = 100000;
const NUM_THREADS: usize = 4;
#[test]
fn test() {
    let lock = Arc::new(FairLock::new(0));
    let mut handles = vec![];

    for thread_idx in 0..NUM_THREADS {
        let lock0 = lock.clone();
        let handle = std::thread::spawn(move || {
            for _ in 0..NUM_LOOP {
                // スレッド番号を渡してロックを獲得する
                let mut data = lock0.lock(thread_idx);
                *data += 1; // FairLockGuardが Deref, DerefMut を実装しているので参照外しが可能
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
        *lock.lock(0),
        NUM_LOOP * NUM_THREADS
    );
}
