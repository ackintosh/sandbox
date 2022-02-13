//////////////////////////////////////
// Cell型
// https://doc.rust-jp.rs/the-rust-programming-language-ja/1.6/book/choosing-your-guarantees.html#%E3%82%BB%E3%83%AB%E5%9E%8B
//////////////////////////////////////

// use std::borrow::BorrowMut;
#[cfg(test)]
use std::cell::{Cell, Ref, RefCell};
#[cfg(test)]
use std::collections::HashMap;
#[cfg(test)]
use std::rc::Rc;

////////////////////////////////////////////////////////////////////////////////////////
// std::cell:Cell
//
// https://doc.rust-lang.org/std/cell/struct.Cell.html
// https://qiita.com/wada314/items/24249418983312795c08#cell%E3%82%92%E4%BD%BF%E3%81%86
//
// <Cellの制限>
// 1. Cellの中身の型はCopyをimplしていなければならない (i.e. memcpyでコピーできなければならない)
// 2. Cellは参照やスマートポインタなどを含め、スレッド間でやりとりすることができない
// 3. Cellは中身の参照を取ってくることができない
////////////////////////////////////////////////////////////////////////////////////////
#[test]
fn cell() {
    // 値をCellでラップする
    let num: Rc<Cell<i32>> = Rc::new(Cell::new(1));
    // 参照カウントは1
    assert_eq!(1, Rc::strong_count(&num));
    // 値は1
    assert_eq!(1, (*num).get()); // Rc型が `Deref` トレイトを実装しているので num.get() でもOK

    // num の参照先の値を +1 する
    num.set(num.get() + 1);
    assert_eq!(2, num.get());

    // Rcをコピーしたので参照カウントは2
    let num2 = Rc::clone(&num);
    assert_eq!(2, Rc::strong_count(&num));
    assert_eq!(2, Rc::strong_count(&num2));

    // 再度、num の参照先の値を +1 する
    num.set(num.get() + 1);
    // Rcだけで値をラップするのとは異なり、numとnum2の両方の参照先の値が 3 になった
    assert_eq!(3, num.get());
    assert_eq!(3, num2.get());
}

// HashMapをCellでラップしようとしても、
// HashMapは `Copy` トレイトを実装していないので使えない（コンパイルエラー）
#[test]
fn cell_with_hashmap() {
    // let hashmap: Rc<Cell<HashMap<String, String>>> = Rc::new(Cell::new(HashMap::new()));
    // hashmap.get().insert("hello".to_owned(), "world".to_owned());

    // コンパイルエラー
    // error[E0599]: no method named `get` found for type `std::rc::Rc<std::cell::Cell<std::collections::HashMap<std::string::String, std::string::String>>>` in the current scope
    //   --> references-borrowing/src/cell_refcell.rs:51:13
    //    |
    // 51 |     hashmap.get().insert("hello".to_owned(), "world".to_owned());
    //    |             ^^^ help: there is a method with a similar name: `set`
    //    |
    //    = note: the method `get` exists but the following trait bounds were not satisfied:
    //            `std::collections::HashMap<std::string::String, std::string::String> : std::marker::Copy`
}

////////////////////////////////////////////////////////////////////////////////////////
// std::cell::RefCell
//
// https://doc.rust-lang.org/beta/std/cell/struct.RefCell.html
// https://qiita.com/wada314/items/24249418983312795c08#refcell%E3%82%92%E4%BD%BF%E3%81%86
//
// <Cellの辛いところ> ( = RefCellを使うモチベーション)
// * "Cellの制限"の1で、Copyな型というのは単純な整数型や、整数型のみからなるstructなどに限られ、HashMapなどのように内部にポインタ的なものを含むような型には使えない
// * "Cellの制限"の3で、getやsetするたびにコピーが発生するので非効率
//
// <RefCellのメリット>
// * RefCellの中身の型はだいたい何でもいい (Sized)
// * RefCellは中身を参照やmut参照で取ってくることができる (RefやRefMut経由)
// * RefCellの中身を参照で取れるということは、その参照を他のスレッドに安全に渡すこともできる
//
// <RefCellのデメリット>
// * (((後述)))
////////////////////////////////////////////////////////////////////////////////////////
#[test]
fn refcell() {
    // Cellとは違って、`Copy` トレイトを実装していないHashMapでも使える
    let hashmap: Rc<RefCell<HashMap<String, String>>> = Rc::new(RefCell::new(HashMap::new()));
    hashmap
        .borrow_mut()
        .insert("hello".to_owned(), "world".to_owned());

    println!("{:?}", *hashmap.borrow_mut()); // {"hello": "world"}

    // RefCell::borrow()は、Ref型を返す
    // https://doc.rust-lang.org/beta/std/cell/struct.RefCell.html#method.borrow
    // * Ref型のルール: 通常の参照と同様に、Ref型のオブジェクトは同時に何個でも存在できる
    let hashmap_ref: Ref<HashMap<String, String>> = hashmap.borrow();
    println!("{:?}", hashmap_ref); // {"hello": "world"}

    // RefCell::borrow_mut()は、RefMut型を返す
    // https://doc.rust-lang.org/beta/std/cell/struct.RefCell.html#method.borrow_mut
    // * RefMut型のルール: 通常の参照と同様に、RefMut型のオブジェクトが1つでも存在すると、他のRef型およびRefMut型のオブジェクトは存在できない

    // 実行時エラー(panic)
    // let hashmap_ref_mut: RefMut<HashMap<String, String>> = hashmap.borrow_mut(); // すでに ↑ の hashmap.borrow() で借用済みなのでpanicして落ちてしまう

    ////////////////////////////////////////
    // <RefCellのデメリット>
    // * 前述のRef型、RefMut型のルール違反が起きた場合に、（コンパイルエラーではなく）実行時エラーになってしまう
    // * そのため、RefCellを使う際には、プログラマの責任でborrow_mutの呼び出し場所を管理する必要がある
    //    -> これを多用するとRustでコードを書く意義が薄れてしまうのでできるだけ使わない方が良い
    ////////////////////////////////////////
}

#[test]
fn refcell_sandbox() {
    let num = 1;

    let refcell: Rc<RefCell<i32>> = Rc::new(RefCell::new(num));

    let ptr = refcell.as_ptr();
    println!("ptr: {:?}", ptr); // ポインタのアドレスが出力される

    let refcell2: Rc<RefCell<i32>> = Rc::clone(&refcell);
    let ptr2 = refcell2.as_ptr();
    println!("ptr2: {:?}", ptr2); // `ptr`と同じのアドレスが出力される

    // 値は同じ 1 だけど、別の変数
    let another_num = 1;
    let another_refcell = Rc::new(RefCell::new(another_num));
    let another_ptr = another_refcell.as_ptr();
    println!("another_ptr: {:?}", another_ptr); // 別のアドレスが出力される

    // 同じ値を指しているのでtrue
    assert_eq!(refcell, refcell2);
    // 同じアドレスを指すポインタなので true
    assert_eq!(refcell.as_ptr(), refcell2.as_ptr());

    // 同じ値を指しているのでtrue
    assert_eq!(refcell, another_refcell);
    ///////////////////////////////////////////
    // 別のアドレスを指しているポインタなので一致しない
    ///////////////////////////////////////////
    assert_ne!(refcell.as_ptr(), another_refcell.as_ptr());
}
