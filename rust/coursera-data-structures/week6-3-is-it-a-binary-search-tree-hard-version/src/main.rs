#![recursion_limit = "2000000000"]

use std::ops::Deref;
use std::process::exit;
use std::rc::Rc;

fn main() {
    let n = read_num();
    if n == 0 {
        // Empty tree is considered correct.
        println!("CORRECT");
    }
    let input = read_nodes(n);
    let root_node = build_node(&input, 0);
    if is_bst(&root_node, std::i64::MIN, std::i64::MAX) {
        println!("CORRECT");
    } else {
        println!("INCORRECT");
    }
}

fn read_num<T>() -> T
where
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: std::fmt::Debug, // https://stackoverflow.com/questions/67352894/rust-error-conversion-for-generic-fromstr-unwrap-errors-out-with-unsatisfied-tr
{
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<T>().unwrap()
}

fn read_nodes(number_of_elements: u64) -> Vec<[i64; 3]> {
    let mut nodes = vec![];

    fn get_i64(s: &str) -> i64 {
        match s.parse::<i64>() {
            Ok(i) => i,
            Err(e) => {
                println!("{}", e);
                exit(0);
            }
        }
    }

    for _ in 0..number_of_elements {
        let mut buff = String::new();
        let res = std::io::stdin().read_line(&mut buff);
        if res.is_err() {
            println!("res: {:?}", res);
            exit(0);
        }

        let mut strs = buff.split_whitespace();
        let key = get_i64(strs.next().expect("should have key"));
        let left = get_i64(strs.next().expect("should have left"));
        let right = get_i64(strs.next().expect("should have right"));
        nodes.push([key, left, right]);
    }

    nodes
}

#[derive(Clone, Debug)]
struct Node {
    key: i64,
    left: Option<Rc<Node>>,
    right: Option<Rc<Node>>,
}

impl Node {
    fn new(key: i64) -> Self {
        Self {
            key,
            left: None,
            right: None,
        }
    }
}

fn build_node(input: &Vec<[i64; 3]>, index: usize) -> Node {
    let mut node = Node::new(input[index][0]);

    if input[index][1] != -1 {
        node.left = Some(Rc::new(build_node(input, input[index][1] as usize)));
    }

    if input[index][2] != -1 {
        node.right = Some(Rc::new(build_node(input, input[index][2] as usize)));
    }

    node
}

// ヒント
// https://www.coursera.org/learn/data-structures/discussions/weeks/6/threads/QyTVc_BhEeamuwo9wEiniA/replies/z0IzMN_OEem1gg6_wBWAmA?page=1&sort=upvotesDesc
fn is_bst(node: &Node, min: i64, max: i64) -> bool {
    if node.key < min || node.key > max {
        return false;
    }

    if let Some(left) = &node.left {
        // leftでは同一キーを許可しないので、第3引数(`max`)は -1 した数値を渡している
        if !is_bst(left.deref(), min, node.key - 1) {
            return false;
        }
    }

    if let Some(right) = &node.right {
        if !is_bst(right.deref(), node.key, max) {
            return false;
        }
    }

    true
}

#[test]
fn test() {
    {
        let root = build_node(&vec![[2, 1, 2], [1, -1, -1], [3, -1, -1]], 0);
        assert!(is_bst(&root, std::i64::MIN, std::i64::MAX,));
    }
    {
        let root = build_node(&vec![[1, 1, 2], [2, -1, -1], [3, -1, -1]], 0);
        assert!(!is_bst(&root, std::i64::MIN, std::i64::MAX,));
    }
    {
        let root = build_node(&vec![[2, 1, 2], [1, -1, -1], [2, -1, -1]], 0);
        assert!(is_bst(&root, std::i64::MIN, std::i64::MAX,));
    }
    {
        let root = build_node(&vec![[2, 1, 2], [2, -1, -1], [3, -1, -1]], 0);
        assert!(!is_bst(&root, std::i64::MIN, std::i64::MAX,));
    }
    {
        let root = build_node(&vec![[2147483647, -1, -1]], 0);
        assert!(is_bst(&root, std::i64::MIN, std::i64::MAX,));
    }
    {
        let root = build_node(
            &vec![[1, -1, 1], [2, -1, 2], [3, -1, 3], [4, -1, 4], [5, -1, -1]],
            0,
        );
        assert!(is_bst(&root, std::i64::MIN, std::i64::MAX,));
    }
    {
        // https://www.coursera.org/learn/data-structures/discussions/threads/KNAeZCvbEeiUiBLK9GPa7g/replies/27HecCv8EeibaRLLXg8tTg/comments/hjXhFXMXEei99gpJiLeZ7g
        let root = build_node(
            &vec![
                [4, 1, 2],
                [2, 3, 4],
                [6, 5, 6],
                [1, -1, -1],
                [3, -1, -1],
                [4, -1, -1],
                [7, -1, -1],
            ],
            0,
        );
        // This example should be CORRECT(true)
        // https://www.coursera.org/learn/data-structures/discussions/threads/KNAeZCvbEeiUiBLK9GPa7g/replies/27HecCv8EeibaRLLXg8tTg/comments/giYfXH_9Eeir_w7CDfa8dg
        assert!(is_bst(&root, std::i64::MIN, std::i64::MAX,));
    }
}
