use std::time::Duration;

mod lifetime;
mod rc;

// ミュータブルな参照
// https://qiita.com/wada314/items/24249418983312795c08
#[test]
fn mutable_reference() {
    // `mut` は、変数 a の値が変更可能であることを示している
    let mut a: i32 = 1;
    {
        let ref_to_a: &mut i32 // `mut` は、変数 ref_to_a が "参照先の値" を変更可能な参照型であることを示している
            = &mut a; // `mut` は、変数 a から "参照先の値" を変更可能な参照を取得することを示している

        // ///////////////////////
        // letのあとに `mut` を入れると、変数 ref_to_a は "参照先" (参照先の値ではなく) を変更可能な変数であることを示す
        //   -> 挙動の違いは mutable_reference2 にて
        // let mut ref_to_a: &mut i32
        // ///////////////////////

        // 変数 ref_to_a は "参照先の値" が変更可能なので、変数 a の値が変わる
        *ref_to_a = 32;
    }
    assert_eq!(a, 32);
}

#[test]
fn mutable_reference2() {
    let mut a: i32 = 1;
    let mut b: i32 = 2;
    {
        // letのあとに `mut` を入れているので、変数 ref_to_a は "参照先" (参照先の値ではなく) を変更可能な変数である
        let mut ref_to_a: &mut i32 = &mut a;

        // 参照先を b に返る
        ref_to_a = &mut b;

        // "参照先の値" を 32 にする
        *ref_to_a = 32;
    }

    // ref_to_a の参照先は b なので、変数 a の値は変わらない
    assert_eq!(a, 1);
    // ref_to_a の参照先は b なので、32 になっている
    assert_eq!(b, 32);
}


#[test]
fn borrowing() {
    // 可変の変数
    let mut s = String::from("Hello");
    // 可変の参照
    let ref_s = &mut s;

    // 同一スコープ、同一変数の可変参照は1つしか持てない ( -> データ競合を回避)
    // let ref_s2 = &mut s; // コンパイルエラー

    decorate(ref_s);
    println!("{}", s);
    // Hello, world
}

#[test]
fn borrowing_threading() {
    // 可変の変数
    let mut s = String::from("Hello");
    // 可変の参照
    // let ref_s = &mut s;


    let handle = {
        let mut cloned_s = s.clone();

        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(3));

            // `s` の参照(ref_s)だとコンパイルエラー
            // error[E0597]: `s` does not live long enough
            // decorate(ref_s);

            // moveキーワードで、`s` をcloneした文字列(cloned_s)の所有権を持っているのでコンパイルできる
            decorate(&mut cloned_s);

            println!("cloned_s: {}", cloned_s);
        })
    };

    handle.join().unwrap();
    println!("s: {}", s);
}

// 引数に参照を受け取る ( = 借用)
// 可変の参照を受け取る
fn decorate(s: &mut String) {
    s.push_str(", world");
    println!("{}", s);
    // Hello, world
}

