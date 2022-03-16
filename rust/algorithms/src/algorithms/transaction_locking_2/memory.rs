use crate::algorithms::transaction_locking_2::{MEM_SIZE, STRIPE_SIZE};
use std::sync::atomic::{AtomicU64, Ordering};

// メモリの管理をする型
pub struct Memory {
    // 実際のメモリ
    pub mem: Vec<u8>,
    // ストライプに対応するロックとバージョン
    pub lock_ver: Vec<AtomicU64>,
    // global version-clock
    pub global_clock: AtomicU64,
    // アドレスからストライプ番号に変換するシフト量
    // 例えば、
    //   * ストライプサイズが 1 バイトなら、メモリとストライプは 1 対 1 の ためシフト量は 0
    //   * ストライプサイズが 2 バイトなら、アドレスを 2 で割った値がストライプ番号のため、シフト量は 1 となる
    //   * 同様に、ストライプサイズが 4 バイトならシフト量は 2、ストライプサイズが 8 バイトならシフト量は 3 となる
    //   * そのため、ストライプとメモリのサイズは 2^n バイトでなければならない
    pub shift_size: u32,
}

// Memory型にはトランザクションを実行する基礎的な関数が定義される
impl Memory {
    pub fn new() -> Self {
        // メモリ領域を生成
        let mem = [0].repeat(MEM_SIZE);

        // アドレスからストライプ番号へ変換するシフト量を計算する
        // ストライプのサイズは 2^n にアライメントされている必要がある
        let shift_size = STRIPE_SIZE.trailing_zeros();

        // lock&versionを初期化する
        let mut lock_ver = vec![];
        for _ in 0..MEM_SIZE >> shift_size {
            lock_ver.push(AtomicU64::new(0));
        }

        Memory {
            mem,
            lock_ver,
            global_clock: AtomicU64::new(0),
            shift_size,
        }
    }

    // global version-clock をインクリメントする
    pub fn inc_global_clock(&mut self) -> u64 {
        self.global_clock.fetch_add(1, Ordering::AcqRel)
    }

    // 対象のアドレスのバージョンを取得する
    pub fn get_addr_ver(&self, addr: usize) -> u64 {
        let idx = addr >> self.shift_size;
        let n = self.lock_ver[idx].load(Ordering::Relaxed);

        // 最上位ビットを 0 とした値を返す
        // これは、本実装では 64 ビットアトミック変数のうち、最上位ビットをロック用のビットとして利用し、
        // 下位の 63 ビットをバージョンとして利用するためである
        n & !(1 << 63)
    }

    // 対象のアドレスとバージョンを引数にとり、そのアドレスに対応するストライプのバージョンが、
    // 引数で指定されたバージョン以下であり、かつロックが取得されていない場合に true を返す
    pub fn test_not_modify(&self, addr: usize, rv: u64) -> bool {
        let idx = addr >> self.shift_size;
        let n = self.lock_ver[idx].load(Ordering::Relaxed);

        // 最上位ビットをロック用のビットとして利用し、バージョン情報は下位63ビットのみ利用するため、
        // 単に引数の rv と大小比較するだけでロックの確認とバージョンの大小を同時に判定できる
        n <= rv
    }

    // 対象アドレスのロックを獲得する
    pub fn lock_addr(&mut self, addr: usize) -> bool {
        let idx = addr >> self.shift_size;

        // fetch_update 関数で最上位ビットを 1 に設定する
        // fetch_update 関数は、第1引数に書き込み時のメモリオーダー、第2引数に読み込み時のメモリオーダー、第3引数にアトミックに実行するクロージャを指定する
        match self.lock_ver[idx].fetch_update(
            Ordering::Relaxed, // 書き込み時のオーダー
            Ordering::Relaxed, // 読み込み時のオーダー
            |val| {
                // 最上位ビットの値をテスト&セット
                let n = val & (1 << 63);
                if n == 0 {
                    // fetch_update関数に渡したクロージャがSomeを返すと、fetch_update関数は値を更新してからOkで以前の値をリターンする
                    Some(val | (1 << 63))
                } else {
                    // すでにロック獲得されているのでクロージャはNoneを返す
                    // クロージャがNoneを返すと、fetch_update関数は何もせずにErrで以前の値をリターンする
                    None
                }
            },
        ) {
            // fetch_update関数に渡したクロージャがSomeを返すと、fetch_update関数は値を更新してからOkで以前の値をリターンする
            Ok(_) => true,
            // fetch_update関数に渡したクロージャがNoneを返すと、Errで以前の値をリターンする
            Err(_) => false,
        }
    }

    // 対象アドレスのロックを解放する
    pub fn unlock_addr(&mut self, addr: usize) {
        let idx = addr >> self.shift_size;
        // アドレスに対応するストライプのロックを解放する
        // -> lock&versionの最上位ビットを 0 に設定する
        self.lock_ver[idx].fetch_and(!(1 << 63), Ordering::Relaxed);
    }
}
