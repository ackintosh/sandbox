use crate::algorithms::transaction_locking_2::memory::Memory;
use crate::algorithms::transaction_locking_2::STRIPE_SIZE;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{fence, Ordering};

pub struct WriteTrans<'a> {
    // read-version
    pub read_ver: u64,
    // read-set
    read_set: HashSet<usize>,
    // write-set
    write_set: HashMap<usize, [u8; STRIPE_SIZE]>,
    // ロック済みアドレス
    // どのアドレスをロックしたかを記録する
    // -> write-setをロックしている途中でトランザクションの競合を検知した場合に、適切にロックを解放するため
    locked: Vec<usize>,
    // 競合を検知した場合にtrue
    pub is_abort: bool,
    // メモリへの参照
    pub mem: &'a mut Memory,
}

// Dropトレイトの実装
// locked変数に記録されたメモリのロックを解放するのみ
impl<'a> Drop for WriteTrans<'a> {
    fn drop(&mut self) {
        // ロック済みアドレスのロックを解放する
        for addr in self.locked.iter() {
            self.mem.unlock_addr(*addr);
        }
    }
}

impl<'a> WriteTrans<'a> {
    pub fn new(mem: &'a mut Memory) -> Self {
        WriteTrans {
            read_set: HashSet::new(),
            write_set: HashMap::new(),
            locked: vec![],
            is_abort: false,
            // global version-clockを読み込む
            read_ver: mem.global_clock.load(Ordering::Acquire),
            mem,
        }
    }

    // メモリ書き込み関数
    pub fn store(&mut self, addr: usize, val: [u8; STRIPE_SIZE]) {
        // アドレスがストライプのアラインメントに沿っているかチェックする
        assert_eq!(addr & (STRIPE_SIZE - 1), 0);
        self.write_set.insert(addr, val);
    }

    // メモリ読み込み関数
    // `読み込みアドレスを保存する` と `write-setにあればそれを読み込む` 以外は ReadTrans と同じ
    pub fn load(&mut self, addr: usize) -> Option<[u8; STRIPE_SIZE]> {
        // 競合を検知した場合は終了
        if self.is_abort {
            return None;
        }

        // アドレスがストライプのアラインメントに沿っているかチェックする
        // ここでは実装を簡単にするためにこのようにしているが、実際に利用する際にはさまざまなアドレスに対応すべき
        assert_eq!(addr & (STRIPE_SIZE - 1), 0);

        // 読み込みアドレスを保存する
        self.read_set.insert(addr);

        // write-setにあればそれを読み込む
        // write-setから読み込む理由は、トランザクション中に書き込まれた場合に、正しくそのデータを読み込むためとなる
        if let Some(m) = self.write_set.get(&addr) {
            return Some(*m);
        }

        // 読み込みメモリがロックされておらず、かつ、read-version以下かどうか判定する
        if !self.mem.test_not_modify(addr, self.read_ver) {
            self.is_abort = true;
            return None;
        }

        fence(Ordering::Acquire);

        // メモリの読み込み。単なるコピー
        // ここではイテレータでコピーしているが、unsafeなメモリコピー手法を医療したほうが高速化できる可能性がある
        let mut mem = [0; STRIPE_SIZE];
        for (dst, src) in mem
            .iter_mut()
            .zip(self.mem.mem[addr..addr + STRIPE_SIZE].iter())
        {
            *dst = *src;
        }

        fence(Ordering::SeqCst);

        // メモリ読み込み後に再びストライプのロックと read-version のチェックを行う
        if !self.mem.test_not_modify(addr, self.read_ver) {
            self.is_abort = true;
            return None;
        }

        // 最後に読み込んだ値を返す
        Some(mem)
    }

    // write-set中のアドレスをロックする
    // すべてのアドレスのロックを獲得できた場合に true を返す
    pub fn lock_write_set(&mut self) -> bool {
        for (addr, _val) in self.write_set.iter() {
            if self.mem.lock_addr(*addr) {
                // ロックを獲得できた場合は、locked に追加する
                self.locked.push(*addr);
            } else {
                // ロックを獲得できなかった場合は、false を返して終了する
                return false;
            }
        }

        true
    }

    // read-setを検証する
    pub fn validate_read_set(&self) -> bool {
        for addr in self.read_set.iter() {
            // write-set中にあるアドレスの場合は
            // 自スレッドがロックを獲得しているはずなので、バージョンのみを検査する
            if self.write_set.contains_key(addr) {
                // バージョンのみ検査する
                let ver = self.mem.get_addr_ver(*addr);
                if ver > self.read_ver {
                    return false;
                }
            } else {
                // 他のスレッドがロックしていないかとバージョンを検査する
                if !self.mem.test_not_modify(*addr, self.read_ver) {
                    return false;
                }
            }
        }

        true
    }

    // コミット
    // メモリ書き込みとロックの解放を別々に行う理由は、ループ中にメモリバリアを行うとCPUパイプライン実行の実行速度が低下してしまう可能性があるため
    // 同じ理由で、ReadTransとWriteTransのload関数で行っている事前と事後の検査を、トランザクションの前後に集約できると、メモリバリアのオーバーヘッドを軽減できる
    pub fn commit(&mut self, ver: u64) {
        // すべてのアドレスに対して書き込み。単なるコピー
        for (addr, val) in self.write_set.iter() {
            let addr = *addr as usize;
            for (dst, src) in self.mem.mem[addr..addr + STRIPE_SIZE].iter_mut().zip(val) {
                *dst = *src;
            }
        }

        fence(Ordering::Release);

        // すべてのアドレスのロック解放 & バージョン更新
        for (addr, _val) in self.write_set.iter() {
            let idx = addr >> self.mem.shift_size;
            self.mem.lock_ver[idx].store(ver, Ordering::Relaxed);
        }

        // ロック済みアドレス集合をクリアする
        self.locked.clear();
    }
}
