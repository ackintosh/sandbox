use crate::algorithms::transaction_locking_2::memory::Memory;
use crate::algorithms::transaction_locking_2::read_trans::ReadTrans;
use crate::algorithms::transaction_locking_2::write_trans::WriteTrans;
use std::cell::UnsafeCell;

// トランザクションを実行するクロージャの返り値の型であり、Option型の変種と考えてよい
pub enum STMResult<T> {
    Ok(T),
    // トランザクションをリトライ
    Retry,
    // トランザクションを中止
    Abort,
}

// トランザクションを実行するための型
// STM型はMutex型のようにスレッド間で共有可能で、この型に実装された関数にクロージャを渡すことでトランザクションを実行する
pub struct STM {
    // 実際のメモリ
    mem: UnsafeCell<Memory>,
}

// STM型をスレッド間で共有可能に設定する
unsafe impl Sync for STM {}
// STM型をチャネルで送受信可能に設定する
unsafe impl Send for STM {}

impl STM {
    pub fn new() -> Self {
        STM {
            mem: UnsafeCell::new(Memory::new()),
        }
    }

    // 読み込みトランザクション
    pub fn read_transaction<F, R>(&self, f: F) -> Option<R>
    where
        F: Fn(&mut ReadTrans) -> STMResult<R>,
    {
        loop {
            // 1. global version-clockを読み込む
            let mut read_trans = ReadTrans::new(unsafe { &*self.mem.get() });

            // 2. 投機的実行
            match f(&mut read_trans) {
                STMResult::Ok(val) => {
                    if read_trans.is_abort {
                        // リトライする
                        continue;
                    }
                    // 3. コミット
                    return Some(val);
                }
                STMResult::Retry => {
                    if read_trans.is_abort {
                        // リトライする
                        continue;
                    }
                    // 中断する
                    return None;
                }
                STMResult::Abort => {
                    // 中断する
                    return None;
                }
            }
        }
    }

    // 書き込みトランザクション
    pub fn write_transaction<F, R>(&self, f: F) -> Option<R>
    where
        F: Fn(&mut WriteTrans) -> STMResult<R>,
    {
        loop {
            // 1. global version-clockを読み込む
            let mut write_trans = WriteTrans::new(unsafe { &mut *self.mem.get() });

            // 2. 投機的実行
            let result;
            match f(&mut write_trans) {
                STMResult::Ok(val) => {
                    if write_trans.is_abort {
                        // リトライする
                        continue;
                    }
                    result = val;
                }
                STMResult::Retry => {
                    if write_trans.is_abort {
                        // リトライする
                        continue;
                    }
                    // 中断する
                    return None;
                }
                STMResult::Abort => {
                    // 中断する
                    return None;
                }
            }

            // 3. write-setのロック
            if !write_trans.lock_write_set() {
                continue;
            }

            // 4. global version-clockのインクリメント
            let ver = 1 + write_trans.mem.inc_global_clock();

            // 5. read-setの検証
            if write_trans.read_ver + 1 != ver && !write_trans.validate_read_set() {
                continue;
            }

            // 6. コミットとリリース
            write_trans.commit(ver);

            return Some(result);
        }
    }
}
