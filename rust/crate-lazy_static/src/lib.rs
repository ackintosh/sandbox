#[macro_use]
extern crate lazy_static;

// 参考ページ
// https://qiita.com/tatsuya6502/items/bed3702517b36afbdbca


//////////////////////////////////////////////////////////////////
// "イミュータブルな" グローバルデータを作る
//////////////////////////////////////////////////////////////////

// static変数が増えた時に名前が衝突しないように、モジュールを使って名前空間を分けている
mod app_context {
    use std::collections::HashMap;

    // モジュール外からアクセスできるように pub 属性を付けている
    lazy_static!(
        // 要素が1つのHashMapを束縛する
        pub static ref MAP: HashMap<u32, &'static str> = {
            let mut m = HashMap::new();
            m.insert(0, "foo");
            m
        };
    );
}

#[test]
fn test_immutable_global_data() {
    let ref m = app_context::MAP;
    assert_eq!("foo", *m.get(&0).unwrap());
    assert_eq!("", *m.get(&1).unwrap_or(&""));

    // もし mut 属性を持たせようとしても、コンパイルエラーになる
    //   -> イミュータブルであることが守られるので、複数スレッドから同時にアクセスしても、中身が壊れることがなく安全
    // let ref mut m = app_context::MAP;

    // error[E0596]: cannot borrow immutable static item `MAP` as mutable
    //   --> crate-lazy_static/src/main:33:9
    //    |
    // 33 |     let ref mut m = app_context::MAP;
    //    |         ^^^^^^^^^ cannot borrow as mutable
}

//////////////////////////////////////////////////////////////////
// "ミュータブルな" グローバルデータを作る
//////////////////////////////////////////////////////////////////

// https://qiita.com/tatsuya6502/items/bed3702517b36afbdbca#%E3%83%9F%E3%83%A5%E3%83%BC%E3%82%BF%E3%83%96%E3%83%AB%E3%81%AA%E3%82%B0%E3%83%AD%E3%83%BC%E3%83%90%E3%83%AB%E3%83%87%E3%83%BC%E3%82%BF%E3%82%92-lazy_static-%E3%81%A8-rwlock-%E3%81%A7%E5%AE%9F%E7%8F%BE%E3%81%99%E3%82%8B
