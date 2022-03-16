// 並行プログラミング入門 7.2.3 TL2の実装
// https://www.oreilly.co.jp/books/9784873119595/

use crate::algorithms::transaction_locking_2::stm::{STMResult, STM};
use std::sync::Arc;
use std::time;

mod memory;
mod read_trans;
mod stm;
mod write_trans;

// ストライプのサイズ
const STRIPE_SIZE: usize = 8;

// メモリの合計サイズ
// この設定では 512 / 8 = 64個 のストライプが利用可能
const MEM_SIZE: usize = 512;

// /////////////////////////////
// TL2を用いた食事する哲学者問題
// /////////////////////////////
// メモリ読み込み用のマクロ
#[macro_export]
macro_rules! load {
    ($t:ident, $a:expr) => {
        if let Some(v) = ($t).load($a) {
            v
        } else {
            // 読み込みに失敗したらリトライ
            return crate::algorithms::transaction_locking_2::stm::STMResult::Retry;
        }
    };
}

// メモリ書き込み用のマクロ
#[macro_export]
macro_rules! store {
    ($t:ident, $a:expr, $v:expr) => {
        $t.store($a, $v)
    };
}

const NUM_PHILOSOPHERS: usize = 8;

// 哲学者
// 第２引数の n は、哲学者の番号
fn philosopher(stm: Arc<STM>, n: usize) {
    // 左と右の箸用のメモリ
    // 自身の番号に対応する箸のアドレスを計算する
    let left = 8 * n;
    let right = 8 * ((n + 1) % NUM_PHILOSOPHERS);

    for _ in 0..500000 {
        // 箸を取り上げる
        while !stm
            .write_transaction(|tr| {
                let mut f1 = load!(tr, left); // 左の箸
                let mut f2 = load!(tr, right); // 右の箸

                if f1[0] == 0 && f2[0] == 0 {
                    // 両方あいていれば 1 に設定
                    f1[0] = 1;
                    f2[0] = 1;
                    store!(tr, left, f1);
                    store!(tr, right, f2);
                    STMResult::Ok(true)
                } else {
                    // 両方取れない場合、取得失敗
                    STMResult::Ok(false)
                }
            })
            .unwrap()
        {}

        // 箸を置く
        stm.write_transaction(|tr| {
            let mut f1 = load!(tr, left); // 左の箸
            let mut f2 = load!(tr, right); // 右の箸
            f1[0] = 0;
            f2[0] = 0;
            store!(tr, left, f1);
            store!(tr, right, f2);
            STMResult::Ok(())
        });
    }
}

// 観測者
fn observer(stm: Arc<STM>) {
    for _ in 0..10000 {
        // 箸の現在の状態を取得する
        let chopsticks = stm
            .read_transaction(|tr| {
                let mut v = [0; NUM_PHILOSOPHERS];
                for i in 0..NUM_PHILOSOPHERS {
                    v[i] = load!(tr, 8 * i)[0]; // 最上位ビットをロックに利用しているので 0 番目のみ取得している
                }

                STMResult::Ok(v)
            })
            .unwrap();

        println!("{:?}", chopsticks);

        // 取り上げられている箸が奇数の場合は不正
        // -> 箸の数が奇数の場合は中間状態を取得している( = アトミックな処理になっていない)ためパニックする
        let mut n = 0;
        for c in &chopsticks {
            if *c == 1 {
                n += 1;
            }
        }
        if n & 1 != 0 {
            panic!("inconsistent");
        }

        std::thread::sleep(time::Duration::from_micros(100));
    }
}

// TL2を用いた、食事する哲学者問題
#[test]
fn test() {
    let stm = Arc::new(STM::new());
    let mut handlers = vec![];

    // 哲学者のスレッドを生成
    for i in 0..NUM_PHILOSOPHERS {
        let s = stm.clone();
        let handle = std::thread::spawn(move || philosopher(s, i));
        handlers.push(handle);
    }

    // 観測者のスレッドを生成
    let obs = std::thread::spawn(move || observer(stm));

    for h in handlers {
        h.join().unwrap();
    }

    obs.join().unwrap();
}
