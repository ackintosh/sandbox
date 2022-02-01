#[test]
fn array() {
    {
        let array = [99_i32]; // [i32; 1]
        println!("{:?}", array);
    }

    // 宣言時に初期値をセットする
    {
        let array = [3; 3]; // [i32; 3]
        println!("{:?}", array);
        println!("{:?}", [99; 3]);
    }

    // 配列のサイズはコンパイルタイムで確定している必要があるため、サイズを変数で指定することはできない
    // https://stackoverflow.com/questions/34684261/how-to-set-a-rust-array-length-dynamically
    // let arr = [0; length];
    //   -> vectorを使う
    //      let arr = vec![0; length];
}

// /////////////////////////////
// 文字列の配列
// /////////////////////////////
#[test]
fn array_string() {
    // /////////////////////////////
    // 参考: https://stackoverflow.com/questions/44186660/initializing-an-array-of-strings-in-rust
    // /////////////////////////////

    {
        // 長さ 32 までの配列なら Default で初期化できる
        //   -> 32までは手動で Default が実装されている
        let array_string: [String; 32] = Default::default();
        println!("{:?}", array_string);
    }

    {
        // 長さ 32 以上の文字列の配列を初期化する場合
        const EMPTY_STRING: String = String::new();
        let array_string: [String; 100] = [EMPTY_STRING; 100];
        println!("{:?}", array_string);
    }
}

// /////////////////////////////
// サイズが大きい配列
// /////////////////////////////
#[test]
fn large_array() {
    // ///////////////////////
    // 参考: https://stackoverflow.com/questions/60777426/rust-large-array-thread-main-has-overflowed-its-stack?noredirect=1&lq=1
    // ///////////////////////

    // サイズが大きい配列を作ろうとするとスタックオーバーフローが起きる
    // let array = [0; 1000000];
    // println!("{:?}", array);
    // エラーメッセージ:
    //   thread 'array::large_array' has overflowed its stack
    //   fatal runtime error: stack overflow

    // 代わりに vector を使うことでヒープに領域を確保することになるので解決する
    let array = vec![0; 1000000];
    println!("{:?}", array);
}

// ///////////////////////
// 多次元配列
// ///////////////////////
#[test]
fn multidimensional_array() {
    {
        let array = [[1; 3]; 5]; // [[i32; 3]; 5] という型の配列
        println!("{:?}", array);
    }
}
