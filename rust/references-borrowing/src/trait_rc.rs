#[cfg(test)]
use std::rc::Rc;

// std::rc::Rc (Reference Counted)
// https://doc.rust-lang.org/std/rc/struct.Rc.html
// https://doc.rust-jp.rs/book/second-edition/ch15-04-rc.html

// * ヒープにプログラムの複数箇所で読む何らかのデータを確保したいけれど、 コンパイル時にはどの部分が最後にデータを使用し終わるか決定できない時に使う
// * 参照カウントが 0 になるまで値がdropされない

/////////////////////////////////////////////
// 基本
/////////////////////////////////////////////
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
    //     --> references-borrowing/src/trait_rc:10:28
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

/////////////////////////////////////////////
// Rcの "参照先の値" を変更する
//  (Rc::make_mut、Rc::get_mut)
// ※ 注意事項あり
// https://qiita.com/wada314/items/24249418983312795c08#rcmake_mut%E3%81%A8rcget_mut
/////////////////////////////////////////////
#[test]
fn rc_mut() {
    // Rc::make_mut、Rc::get_mutを使うことで、Rcの参照先の値の `&mut T` 型にアクセスできるが、
    // これらの関数には強い制約があるので要注意

    //////////////////////////////////////////
    // <制約>
    // * どちらの関数も「そのRcの参照カウントが1のときだけ」しか、参照先の&mutを返してくれない.
    // * 参照カウントが2以上の場合は、新しいRcとその参照先が作られる
    //   -> (おそらく、マルチスレッド下でデータ競合が起きないことを保証するためと思われる）
    //   -> この制約を受けずに( = 新しい参照先を作らずに)、参照先の値を変更するには `Cell`, `RefCell` を使う
    //      https://qiita.com/wada314/items/24249418983312795c08#cell%E3%82%92%E4%BD%BF%E3%81%86
    //////////////////////////////////////////

    let mut num: Rc<i32> = Rc::new(1);
    assert_eq!(1, Rc::strong_count(&num)); // 参照カウントは1

    *Rc::make_mut(&mut num) += 1; // numの参照先に 1 を足した
    // num = 2
    assert_eq!(2, *num);
    println!("num: {}", num);

    // Rcをコピーしたので参照カウントは 2
    let num2: Rc<i32> = Rc::clone(&num);
    assert_eq!(2, Rc::strong_count(&num));
    assert_eq!(2, Rc::strong_count(&num2));
    assert_eq!(*num, *num2);

    // 再度、Rc::make_mut を使って num の参照先に 1 を足すが、`num`しか値が変わらない
    //   -> 参照カウントが 1 ではないから、新しい Rc とその参照先を作成してしまう
    *Rc::make_mut(&mut num) += 1;
    println!("num: {}, num2: {}", *num, *num2);
    assert_eq!(3, *num); // num は 3 に変わった
    assert_eq!(2, *num2); // num2 は 2 のまま
}
