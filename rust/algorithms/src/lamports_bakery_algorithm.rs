// パン屋のアルゴリズム (Lamport's bakery algorithm)
// https://www.oreilly.co.jp/books/9784873119595/
// 3.9 パン屋のアルゴリズム

// 最適化抑制読み書き用
use std::ptr::{read_volatile, write_volatile};
// メモリバリア用
use std::sync::atomic::{fence, Ordering};

const NUM_THREADS: usize = 4;
const NUM_LOOP: usize = 100000; // 各スレッドでのループ数

// ///////////////////////
// グローバル変数
// ///////////////////////
static mut LOCK: BakeryLock = BakeryLock {
    entering: [false; NUM_THREADS],
    tickets: [None; NUM_THREADS],
};

static mut COUNT: u64 = 0;

// ///////////////////////
// volatile用マクロ
// ///////////////////////
macro_rules! read_mem {
    ($addr: expr) => {
        unsafe { read_volatile($addr) }
    };
}

macro_rules! write_mem {
    ($addr: expr, $val: expr) => {
        unsafe { write_volatile($addr, $val) }
    };
}

// ///////////////////////
// パン屋のアルゴリズム用の型
// ///////////////////////
struct BakeryLock {
    entering: [bool; NUM_THREADS],
    tickets: [Option<u64>; NUM_THREADS],
}

impl BakeryLock {
    // ロック関数。idxはスレッド番号
    fn lock(&mut self, idx: usize) -> LockGuard {
        // //////////////////////////////////////////
        // ここからチケット取得処理
        // //////////////////////////////////////////
        fence(Ordering::SeqCst);
        write_mem!(&mut self.entering[idx], true);
        fence(Ordering::SeqCst);

        // 現在配布されているチケットの最大値を取得
        let mut max = 0;
        for i in 0..NUM_THREADS {
            if let Some(t) = read_mem!(&self.tickets[i]) {
                max = max.max(t);
            }
        }

        // 最大値 +1 を自分のチケット番号とする
        let ticket = max + 1;
        write_mem!(&mut self.tickets[idx], Some(ticket));

        fence(Ordering::SeqCst);
        write_mem!(&mut self.entering[idx], false);
        fence(Ordering::SeqCst);

        // //////////////////////////////////////////
        // ここから待機処理
        // //////////////////////////////////////////
        for i in 0..NUM_THREADS {
            if i == idx {
                continue;
            }

            // スレッド i がチケット取得中なら待機
            while read_mem!(&self.entering[i]) {}

            loop {
                // スレッド i と自分の優先順位を比較して
                // 自分のほうが優先順位が高いか、
                // スレッド i が処理中でない場合に待機を終了する
                match read_mem!(&self.tickets[i]) {
                    Some(t) => {
                        // スレッド i のチケット番号より
                        // 自分の番号の方が若いか、
                        // チケット番号が同じでかつ、
                        // 自分の方がスレッド番号が若い場合に
                        // 待機終了する
                        if ticket < t || (ticket == t && idx < i) {
                            break;
                        }
                    }
                    None => {
                        // スレッド i が処理中でない場合は
                        // 待機終了する
                        break;
                    }
                }
            }
        }

        fence(Ordering::SeqCst);
        LockGuard { idx }
    }
}

// ///////////////////////
// ロック管理用の型
// ///////////////////////
struct LockGuard {
    idx: usize,
}

impl Drop for LockGuard {
    // ロック解放処理
    fn drop(&mut self) {
        fence(Ordering::SeqCst);
        write_mem!(&mut LOCK.tickets[self.idx], None);
    }
}

#[test]
fn test() {
    // NUM_THREADSだけスレッドを生成
    let mut handles = vec![];
    for i in 0..NUM_THREADS {
        let th = std::thread::spawn(move || {
            // NUM_LOOPだけループし、COUNTをインクリメントする
            for _ in 0..NUM_LOOP {
                // ロック獲得
                let _lock = unsafe { LOCK.lock(i) };
                unsafe {
                    let count = read_volatile(&COUNT);
                    write_volatile(&mut COUNT, count + 1);
                }
            }
        });
        handles.push(th);
    }

    for th in handles {
        th.join().unwrap();
    }

    println!(
        "COUNT = {} (expected = {})",
        unsafe { COUNT },
        NUM_LOOP * NUM_THREADS,
    );
}
