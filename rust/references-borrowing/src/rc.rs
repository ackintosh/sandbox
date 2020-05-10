use std::rc::Rc;

// std::rc::Rc (Reference Counted)
// https://doc.rust-lang.org/std/rc/struct.Rc.html
// https://doc.rust-jp.rs/book/second-edition/ch15-04-rc.html

// * ヒープにプログラムの複数箇所で読む何らかのデータを確保したいけれど、 コンパイル時にはどの部分が最後にデータを使用し終わるか決定できない時に使う
// * 参照カウントが 0 になるまで値がdropされない

#[test]
fn rc() {
    // *RCではなく参照を使う場合*
    // fn reference_test() -> &i32 {
    //     // 関数内で作った値の参照を返そうとしている
    //     let i = 32;
    //     &i
    // }
    //
    // コンパイルエラー
    // error[E0106]: missing lifetime specifier
    //     --> references-borrowing/src/rc.rs:10:28
    //     |
    //     10 |     fn reference_test() -> &i32 {
    //     |                            ^ help: consider giving it a 'static lifetime: `&'static`
    //     |
    //     = help: this function's return type contains a borrowed value, but there is no value for it to be borrowed from
    //

    // *RCを使う場合*
    fn rc_test() -> Rc<i32>{
        let i = 32;
        Rc::new(i)
    }


    // 関数 rc_test のスコープを抜けたけど、ヒープにある変数 i の値はまだ参照されているのでdropされない
    let n = rc_test();
    // 参照カウントは 1
    assert_eq!(1, Rc::strong_count(&n));

    // 関数 rc_test が返した参照の値を取得できる
    println!("{}", n);
}

