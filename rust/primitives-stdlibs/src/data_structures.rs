mod binary_tree {
    use std::collections::VecDeque;

    // https://laysakura.github.io/2019/12/22/rust-DataStructures-Algorithm-BinaryTree/
    #[derive(Debug, PartialEq)]
    enum BinaryTree<T> {
        Nil,
        Node {
            val: T,
            left: Box<BinaryTree<T>>,
            right: Box<BinaryTree<T>>,
        },
    }

    impl<T> BinaryTree<T> {
        // *** 要素の追加(置き換え) ***
        // Node が1つのノードでなくサブツリーのルートであれば、二分木に二分木を追加することになる
        // to は self に組み込まれる形で move される
        fn replace(&mut self, to: Self) {
            *self = to;
        }

        // *** 削除 ***
        #[allow(dead_code)]
        fn remove(&mut self) {
            self.replace(Self::Nil);
        }
    }

    // 二分木を簡単に作るためのマクロ
    macro_rules! bin_tree {
        (val: $val:expr, left: $left:expr, right: $right:expr $(,)? ) => {
            BinaryTree::Node {
                val: $val,
                left: Box::new($left),
                right: Box::new($right),
            }
        };

        // leftを省略(Nil)する場合
        (val: $val:expr, right: $right:expr $(,)?) => {
            BinaryTree::Node {
                val: $val,
                left: Box::new(BinaryTree::Nil),
                right: Box::new($right),
            }
        };

        // rightを省略(Nil)する場合
        (val: $val:expr, left: $left:expr $(,)?) => {
            BinaryTree::Node {
                val: $val,
                left: Box::new($left),
                right: Box::new(BinaryTree::Nil),
            }
        };

        // 子を持たないノード
        (val: $val:expr $(,)?) => {
            BinaryTree::Node {
                val: $val,
                left: Box::new(BinaryTree::Nil),
                right: Box::new(BinaryTree::Nil),
            }
        };
    }

    // 二分木の構築 (地道に作るパターン)
    #[test]
    fn test() {
        //       5
        //      / \
        //     4   8
        //    /
        //   11
        let root = BinaryTree::<i32>::Node {
            val: 5,
            left: Box::new(BinaryTree::Node {
                val: 4,
                left: Box::new(BinaryTree::Node {
                    val: 11,
                    left: Box::new(BinaryTree::Nil),
                    right: Box::new(BinaryTree::Nil),
                }),
                right: Box::new(BinaryTree::Nil),
            }),
            right: Box::new(BinaryTree::Node {
                val: 8,
                left: Box::new(BinaryTree::Nil),
                right: Box::new(BinaryTree::Nil),
            }),
        };

        println!("{:?}", root);
    }

    #[test]
    fn test2() {
        //       5
        //      / \
        //     4   8
        //    /
        //   11
        let root = bin_tree!(
            val: 5,
            left: bin_tree!(val: 4, left: bin_tree!(val: 11)),
            right: bin_tree!(val: 8),
        );

        println!("{:?}", root);
    }

    #[test]
    fn test_replace() {
        // tree1:
        //       5
        //      /
        //     4
        //    /
        //   11
        //  /  \
        // 7    2
        //
        // tree2:
        //         8
        //        / \
        //       13  4
        //            \
        //             1
        //
        // tree3 = tree1.root.right + tree2:
        //       5
        //      / \
        //     4   8
        //    /   / \
        //   11  13  4
        //  /  \      \
        // 7    2      1
        //

        // tree1 は後ほどルートの右のNilを置き換えるので、 mut でつくる。
        let mut tree1 = bin_tree! {
            val: 5,
            left: bin_tree! {
                val: 4,
                left: bin_tree! {
                    val: 11,
                    left: bin_tree! { val: 7 },
                    right: bin_tree! { val: 2 },
                },
            },
        };

        let tree2 = bin_tree! {
            val: 8,
            left: bin_tree! { val: 13 },
            right: bin_tree! {
                val: 4,
                right: bin_tree! { val: 1 },
            },
        };

        let tree3 = bin_tree! {
            val: 5,
            left: bin_tree! {
                val: 4,
                left: bin_tree! {
                    val: 11,
                    left: bin_tree! { val: 7 },
                    right: bin_tree! { val: 2 },
                },
            },
            right: bin_tree! {
                val: 8,
                left: bin_tree! { val: 13 },
                right: bin_tree! {
                    val: 4,
                    right: bin_tree!{ val: 1 },
                },
            },
        };

        if let BinaryTree::Node { right, .. } = &mut tree1 {
            // tree1のルートの右を、Nilからtree2のルートに置き換える。
            //
            // 型の解説:
            //   right: &mut Box<BinaryTree>
            //   *right: mut Box<BinaryTree>
            //   **right: mut BinaryTree
            //
            // replaceは &mut BinaryTree をセルフとして受け取るので (&mut **right).replace と書くのが明示的だが、
            // `.` 演算子が暗黙的に借用への変換を行ってくれる。
            (**right).replace(tree2);
        }
        assert_eq!(&tree1, &tree3);
    }

    // 深さ優先探索
    #[test]
    fn test_dfs() {
        //       5
        //      / \
        //     4   8
        //    /   / \
        //   11  13  4
        //  /  \      \
        // 7    2      1
        let tree = bin_tree! {
            val: 5,
            left: bin_tree! {
                val: 4,
                left: bin_tree! {
                    val: 11,
                    left: bin_tree! { val: 7 },
                    right: bin_tree! { val: 2 },
                },
            },
            right: bin_tree! {
                val: 8,
                left: bin_tree! { val: 13 },
                right: bin_tree! {
                    val: 4,
                    right: bin_tree! { val: 1 },
                },
            },
        };

        assert!(dfs(&tree, &13));
        assert!(!dfs(&tree, &99));

        // 再帰関数を使うことで簡潔に実装できる
        fn dfs(node: &BinaryTree<i32>, target: &i32) -> bool {
            if let BinaryTree::Node { val, left, right } = node {
                if val == target {
                    return true;
                }

                if dfs(&left, target) || dfs(&right, target) {
                    return true;
                }
            }

            false
        }
    }

    // 幅優先探索
    #[test]
    fn bfs() {
        //       5
        //      / \
        //     4   8
        //    /   / \
        //   11  13  4
        //  /  \      \
        // 7    2      1
        let tree = bin_tree! {
            val: 5,
            left: bin_tree! {
                val: 4,
                left: bin_tree! {
                    val: 11,
                    left: bin_tree! { val: 7 },
                    right: bin_tree! { val: 2 },
                },
            },
            right: bin_tree! {
                val: 8,
                left: bin_tree! { val: 13 },
                right: bin_tree! {
                    val: 4,
                    right: bin_tree! { val: 1 },
                },
            },
        };

        assert!(bfs(&tree, &13));
        assert!(!bfs(&tree, &99));

        // FIFOなキューに左右の子ノードを順にpushしていき、それをpopしていくループによって実現する
        fn bfs(node: &BinaryTree<i32>, target: &i32) -> bool {
            let mut queue = VecDeque::new();
            queue.push_back(node);

            while let Some(node) = queue.pop_front() {
                if let BinaryTree::Node {val, left, right} = node {
                    if val == target {
                        return true;
                    }

                    queue.push_back(left);
                    queue.push_back(right);
                }
            }

            false
        }
    }
}
