// https://doc.rust-jp.rs/the-rust-programming-language-ja/1.6/book/choosing-your-guarantees.html#%E4%BF%9D%E8%A8%BC
// * Weakは所有せず、借用もしないスマートポインタ
// * &T とも似ていますが、ライフタイムによる制約が無いので Weak<T> は永遠に有効であり続けることができる
//   * しかし、これは所有する Rc のライフタイムを超えて有効である可能性があるため、中身のデータへのアクセスが失敗し、 None を返す可能性がある
// * 循環するデータ構造, 循環参照(circular reference)を実装するときに便利

mod basics {
    use std::borrow::Borrow;
    use std::rc::Rc;

    #[test]
    fn test() {
        let weak = {
            let data = Rc::new(10);
            let weak = Rc::downgrade(&data);

            // 元の値がまだ生きているので Weak::upgrade は Some<Rc<i32>> を返す
            let i = weak.upgrade().unwrap();
            assert_eq!(&10, i.borrow());

            weak
        };

        // ここでは元の値はすでにdropされているので Weak::upgrade は None を返す
        assert_eq!(None, weak.upgrade());
    }
}

// 循環参照の例
// Working with Shared pointers in Rust: Challenges and Solutions [Tutorial]
// https://hub.packtpub.com/shared-pointers-in-rust-challenges-solutions/
mod circular_reference {
    use std::cell::RefCell;
    use std::rc::{Rc, Weak};

    struct Node {
        value: i32,
        parent: Option<Weak<RefCell<Node>>>, // 親への参照を Weak で持っている
        left: Option<Rc<RefCell<Node>>>,
        right: Option<Rc<RefCell<Node>>>,
    }

    #[test]
    fn test() {
        let root = Rc::new(RefCell::new(Node {
            value: 10,
            parent: None,
            left: None,
            right: None,
        }));

        let left = Rc::new(RefCell::new(Node {
            value: 1,
            parent: Some(Rc::downgrade(&root)), // 親への参照
            left: None,
            right: None,
        }));

        let right = Rc::new(RefCell::new(Node {
            value: 11,
            parent: Some(Rc::downgrade(&root)), // 親への参照
            left: None,
            right: None,
        }));

        root.borrow_mut().left = Some(left.clone());
        root.borrow_mut().right = Some(right.clone());

        // root -> left
        assert_eq!(1, root.borrow().left.as_ref().unwrap().borrow().value);
        // root -> right
        assert_eq!(11, root.borrow().right.as_ref().unwrap().borrow().value);
        // left -> root
        assert_eq!(
            10,
            left.borrow()
                .parent
                .as_ref()
                .unwrap()
                .upgrade()
                .unwrap()
                .borrow()
                .value
        );
        // right -> root
        assert_eq!(
            10,
            right
                .borrow()
                .parent
                .as_ref()
                .unwrap()
                .upgrade()
                .unwrap()
                .borrow()
                .value
        );
    }
}
