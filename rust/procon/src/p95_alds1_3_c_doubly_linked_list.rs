// プロコンのためのアルゴリズムとデータ構造
// 4.4 連結リスト


// *入力*
// n: 命令数
// commands: 命令の配列

// [命令]
// insert x: 連結リストの先頭にキーxを持つ要素を継ぎ足す
// delete x: キーxを持つ最初の要素を連結リストから削除する
// deleteFirst: 連結リストの先頭の要素を削除する
// deleteLast: 連結リストの末尾の要素を削除する
// ※キーは整数

// *出力*
// 全ての命令が終了したあとの、連結リスト内のキーを順番に出力する
// 連続するキーは1つの空白文字で区切る

// *制約*
// 命令数は2,000,000を超えない
// delete x命令の回数は20を超えない
// 0 <= キーの値 <= 10^9
// 命令の過程でリストの要素数 10^6 を超えない

use std::rc::Rc;
use std::cell::RefCell;

#[derive(Debug)]
struct Node {
    key: u32,
    prev: Option<Rc<RefCell<Node>>>,
    next: Option<Rc<RefCell<Node>>>,
}

#[derive(Debug)]
struct DoublyLinkedList {
    sentinel: Rc<RefCell<Node>>,
}

impl DoublyLinkedList {
    fn new() -> Self {
        let sentinel = Rc::new(RefCell::new(Node {
            key: 0,
            prev: None,
            next: None,
        }));

        {
            let mut ref_sentinel = sentinel.borrow_mut();
            ref_sentinel.prev = Some(Rc::clone(&sentinel));
            ref_sentinel.next = Some(Rc::clone(&sentinel));
        }

        Self {
            sentinel,
        }
    }

    fn insert(&mut self, key: u32) {
        let node = Rc::new(RefCell::new(Node {
            key,
            prev: None,
            next: None,
        }));

        {
            // 新しいNodeをリストの先頭(sentinelの直後)に入れる
            let mut ref_node = node.borrow_mut();
            ref_node.prev = Some(Rc::clone(&self.sentinel));
            ref_node.next = Some(Rc::clone(&self.sentinel.borrow().next.as_ref().expect("should have next node")));
        }

        {
            let sentinel_ptr = self.sentinel.as_ptr();
            let sentinel_prev_ptr = self.sentinel.borrow().prev.as_ref().unwrap().as_ptr();

            // 初回のinsert(= sentinel.prev が sentinel 自身を指している)の場合は
            // リストの末尾(sentinelのprev)から新しいNodeを参照する
            if sentinel_ptr == sentinel_prev_ptr {
                self.sentinel.borrow_mut().prev = Some(Rc::clone(&node));
            }
        }

        self.sentinel.borrow_mut().next = Some(Rc::clone(&node));
    }

    fn delete(&mut self, key: u32) -> Result<(), String> {
        match self.search(key) {
            Some(node) => {
                let node_ptr = node.as_ptr();
                let sentinel_ptr = self.sentinel.as_ptr();
                if node_ptr == sentinel_ptr {
                    return Err("sentinelは削除不可能".to_owned());
                }

                let a = Rc::clone(node.borrow().prev.as_ref().expect("should have previous node"));
                let b = Rc::clone(node.borrow().next.as_ref().expect("should have next node"));

                a.borrow_mut().next = Some(Rc::clone(
                    node.borrow().next.as_ref().unwrap()
                ));
                b.borrow_mut().prev = Some(Rc::clone(
                    node.borrow().prev.as_ref().unwrap()
                ));

                Ok(())
            },
            None => {
                Err("該当するkeyを持つノードが存在しない".to_owned())
            },
        }
    }

    fn search(&self, key: u32) -> Option<Rc<RefCell<Node>>> {
        let mut current = Rc::clone(&self.sentinel);

        while current.borrow().next.as_ref().unwrap().as_ptr() != self.sentinel.as_ptr() {
            let k = current.borrow().next.as_ref().unwrap().borrow().key;
            if k == key {
                return Some(Rc::clone(current.borrow().next.as_ref().unwrap()));
            } else {
                let next = Rc::clone(current.borrow().next.as_ref().unwrap());
                current = next;
            }
        }

        return None;
    }
}

#[test]
fn test_doubly_linked_list() {
    let mut list = DoublyLinkedList::new();

    list.insert(10);
    list.insert(20);

    {
        let node = list.search(10);
        assert_eq!(10, node.unwrap().borrow().key);
    }

    {
        let node = list.search(999);
        assert!(node.is_none());
    }

    let result = list.delete(10);
    assert_eq!(Ok(()), result);
}
