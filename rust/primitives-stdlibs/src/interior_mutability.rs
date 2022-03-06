// Interior mutability
// https://stackoverflow.com/a/58599995
// > Interior mutability is a concept you may know from other programming languages in the form of mutexes, atomics and synchronization primitives.
// > In practice, those structures allow you to temporarily guarantee that you are the only accessor of a given variable.

// 公式ドキュメント
// RefCell<T>と内部可変性パターン
// https://doc.rust-jp.rs/book-ja/ch15-05-interior-mutability.html

// use std::borrow::Borrow; この use があると、`data.borrow()`がコンパイルエラーになる
// use std::borrow::BorrowMut; この use があると、`data.borrow_mut()`がコンパイルエラーになる
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn interior_mutability() {
    // マルチスレッドの場合は、下記のように変える
    // * Rc -> Arc
    // * Cell/RefCell -> Mutex か RwLock
    let data = Rc::new(RefCell::new(true));

    {
        // 変数 data は immutable だが、RefCell::borrow_mut() で
        // mutable な参照を得られる
        let mut reference = data.borrow_mut();
        *reference = false;
    }

    assert!(!*data.borrow());
}
