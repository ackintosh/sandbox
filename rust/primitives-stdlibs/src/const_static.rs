// const, static いずれも定数を定義するキーワード
// グローバルでも特定のブロックのスコープでも、任意の場所で利用可能

// <可変性の違い>
// * constは常に変更不可なので、別の値を紐付けようとしたり、変更することはできない
// * staticは mut で変更可能にもできる (ただし、変更可能なグローバル変数を作ることは避けるべき)

// <コンパイル時の扱われ方の違い>
// * constはコンパイラがビルドする時に実際の値に置き換える
// * staticの値はバイナリファイルの特定のセクションに配置される
//   -> もしコンパイル時には決まらないが実行時に決まる定数を定義したい場合は、
//      staticではなく、外部クレートの lazy_static を使う

// グローバルスコープ
const SANDBOX_CONST: u8 = 1;
static SANDBOX_STATIC: u8 = 2;

mod test_mod {
    // モジュール内での宣言
    const SANDBOX_CONST: u8 = 11;
    static SANDBOX_STATIC: u8 = 22;

    #[test]
    fn test() {
        println!("{:?}", SANDBOX_CONST); // 11
        println!("{:?}", SANDBOX_STATIC); // 22
    }
}

// グローバルスコープで定義した可変のstaticの値は、どこからでも変更可能な危険な変数
// そのため、この値を操作するときには unsafe ブロックに入れる必要がある
static mut MUTABLE_SANDBOX_STATIC: u8 = 3;

#[test]
fn test() {
    println!("SANDBOX_CONST: {:?}", SANDBOX_CONST);
    println!("SANDBOX_STATIC: {:?}", SANDBOX_STATIC);

    // mutableな static の値を扱う場合は unsafe ブロックに入れないとコンパイルエラー
    unsafe {
        MUTABLE_SANDBOX_STATIC = 33;
    }

    unsafe {
        println!("MUTABLE_SANDBOX_STATIC: {:?}", MUTABLE_SANDBOX_STATIC); // 33
    }
}
