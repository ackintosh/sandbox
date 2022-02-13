#![recursion_limit = "2000000000"]

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
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
    if is_binary_search_tree(
        &root_node,
        Rc::new(Cell::new(std::i64::MIN)),
        Rc::new(RefCell::new(HashMap::new())),
        1,
    ) {
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

// 返り値に配列を使う(stackに領域を確保する)パターン
// fn read_nodes(number_of_elements: u64) -> Vec<[i64; 3]> {
//     let mut nodes = vec![];
//
//     fn get_i64(s: &str) -> i64 {
//         match s.parse::<i64>() {
//             Ok(i) => i,
//             Err(e) => {
//                 println!("{}", e);
//                 exit(0);
//             }
//         }
//     }
//
//     for _ in 0..number_of_elements {
//         let mut buff = String::new();
//         let res = std::io::stdin().read_line(&mut buff);
//         if res.is_err() {
//             println!("res: {:?}", res);
//             exit(0);
//         }
//
//         let mut strs = buff.split_whitespace();
//         let key = get_i64(strs.next().expect("should have key"));
//         let left = get_i64(strs.next().expect("should have left"));
//         let right = get_i64(strs.next().expect("should have right"));
//         nodes.push([key, left, right]);
//     }
//
//     nodes
// }

fn read_nodes(number_of_elements: u64) -> Vec<Vec<i64>> {
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
        nodes.push(vec![key, left, right]);
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

fn build_node(input: &Vec<Vec<i64>>, index: usize) -> Node {
    let mut node = Node::new(input[index][0]);

    if input[index][1] != -1 {
        node.left = Some(Rc::new(build_node(input, input[index][1] as usize)));
    }

    if input[index][2] != -1 {
        node.right = Some(Rc::new(build_node(input, input[index][2] as usize)));
    }

    node
}

fn is_binary_search_tree(
    node: &Node,
    working_key: Rc<Cell<i64>>,
    key_to_level: Rc<RefCell<HashMap<i64, u64>>>,
    level: u64,
) -> bool {
    if let Some(left) = &node.left {
        if !is_binary_search_tree(
            left.deref(),
            working_key.clone(),
            key_to_level.clone(),
            level + 1,
        ) {
            return false;
        }
    }

    if node.key < working_key.get() {
        return false;
    } else if node.key == working_key.get() {
        match key_to_level.borrow().get(&node.key) {
            None => {
                println!("unreachable");
                return false;
            }
            Some(level_of_duplicate) => {
                if level_of_duplicate > &level {
                    return false;
                }
            }
        }
    }
    working_key.set(node.key);
    key_to_level.borrow_mut().insert(node.key, level);

    if let Some(right) = &node.right {
        if !is_binary_search_tree(
            right.deref(),
            working_key.clone(),
            key_to_level.clone(),
            level + 1,
        ) {
            return false;
        }
    }

    true
}

#[test]
fn test() {
    {
        let root = build_node(&vec![vec![2, 1, 2], vec![1, -1, -1], vec![3, -1, -1]], 0);
        assert!(is_binary_search_tree(
            &root,
            Rc::new(Cell::new(0)),
            Rc::new(RefCell::new(HashMap::new())),
            1,
        ));
    }
    {
        let root = build_node(&vec![vec![1, 1, 2], vec![2, -1, -1], vec![3, -1, -1]], 0);
        assert!(!is_binary_search_tree(
            &root,
            Rc::new(Cell::new(0)),
            Rc::new(RefCell::new(HashMap::new())),
            1,
        ));
    }
    {
        let root = build_node(&vec![vec![2, 1, 2], vec![1, -1, -1], vec![2, -1, -1]], 0);
        assert!(is_binary_search_tree(
            &root,
            Rc::new(Cell::new(0)),
            Rc::new(RefCell::new(HashMap::new())),
            1,
        ));
    }
    {
        let root = build_node(&vec![vec![2, 1, 2], vec![2, -1, -1], vec![3, -1, -1]], 0);
        assert!(!is_binary_search_tree(
            &root,
            Rc::new(Cell::new(0)),
            Rc::new(RefCell::new(HashMap::new())),
            1,
        ));
    }
    {
        let root = build_node(&vec![vec![2147483647, -1, -1]], 0);
        assert!(is_binary_search_tree(
            &root,
            Rc::new(Cell::new(0)),
            Rc::new(RefCell::new(HashMap::new())),
            1,
        ));
    }
    {
        let root = build_node(
            &vec![vec![1, -1, 1], vec![2, -1, 2], vec![3, -1, 3], vec![4, -1, 4], vec![5, -1, -1]],
            0,
        );
        assert!(is_binary_search_tree(
            &root,
            Rc::new(Cell::new(0)),
            Rc::new(RefCell::new(HashMap::new())),
            1,
        ));
    }
    {
        // https://www.coursera.org/learn/data-structures/discussions/threads/KNAeZCvbEeiUiBLK9GPa7g/replies/27HecCv8EeibaRLLXg8tTg/comments/hjXhFXMXEei99gpJiLeZ7g
        let root = build_node(
            &vec![
                vec![4, 1, 2],
                vec![2, 3, 4],
                vec![6, 5, 6],
                vec![1, -1, -1],
                vec![3, -1, -1],
                vec![4, -1, -1],
                vec![7, -1, -1],
            ],
            0,
        );
        // This example should be CORRECT(true)
        // https://www.coursera.org/learn/data-structures/discussions/threads/KNAeZCvbEeiUiBLK9GPa7g/replies/27HecCv8EeibaRLLXg8tTg/comments/giYfXH_9Eeir_w7CDfa8dg
        assert!(is_binary_search_tree(
            &root,
            Rc::new(Cell::new(0)),
            Rc::new(RefCell::new(HashMap::new())),
            1,
        ));
    }
}
