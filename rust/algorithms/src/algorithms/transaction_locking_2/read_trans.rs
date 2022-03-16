use crate::algorithms::transaction_locking_2::memory::Memory;
use crate::algorithms::transaction_locking_2::STRIPE_SIZE;
use std::sync::atomic::{fence, Ordering};

// 読み込みトランザクション時にメモリ読み込みを行う型
pub struct ReadTrans<'a> {
    // read-version
    read_ver: u64,
    // 競合を検知した場合にtrue
    pub is_abort: bool,
    // メモリへの参照
    mem: &'a Memory,
}

impl<'a> ReadTrans<'a> {
    pub fn new(mem: &'a Memory) -> Self {
        ReadTrans {
            // global version-clockを読み込む
            read_ver: mem.global_clock.load(Ordering::Acquire),
            is_abort: false,
            mem,
        }
    }

    // メモリを読み込む関数
    // TL2では、データ読み込みの前後で対象メモリ（ストライプ）がロックされているかと、バージョンが更新されていないかをチェックしているが、
    // これは、確実に read-version 以下のバージョンのデータを読み込むためである
    // -> 詳細は P.237, 238 の表7-3, 7-4を参照
    pub fn load(&mut self, addr: usize) -> Option<[u8; STRIPE_SIZE]> {
        // 競合を検知した場合は終了する
        if self.is_abort {
            return None;
        }

        // アドレスがストライプのアラインメントに沿っているかチェックする
        // ここでは実装を簡単にするためにこのようにしているが、実際に利用する際にはさまざまなアドレスに対応すべき
        assert_eq!(addr & (STRIPE_SIZE - 1), 0);

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
}
