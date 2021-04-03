mod binary_tree {
    // https://laysakura.github.io/2019/12/22/rust-DataStructures-Algorithm-BinaryTree/
    #[derive(Debug)]
    enum BinaryTree<T> {
        Nil,
        Node {
            val: T,
            left: Box<BinaryTree<T>>,
            right: Box<BinaryTree<T>>,
        },
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
}
