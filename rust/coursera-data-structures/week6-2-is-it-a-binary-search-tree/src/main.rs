use std::cell::Cell;
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
    if is_binary_search_tree(&root_node, Rc::new(Cell::new(std::i64::MIN))) {
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
        s.parse::<i64>().expect("should be parsed")
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

fn is_binary_search_tree(node: &Node, working_key: Rc<Cell<i64>>) -> bool {
    if let Some(left) = &node.left {
        if !is_binary_search_tree(left.deref(), working_key.clone()) {
            return false;
        }
    }

    if node.key < working_key.get() {
        return false;
    }
    working_key.set(node.key);

    if let Some(right) = &node.right {
        if !is_binary_search_tree(right.deref(), working_key.clone()) {
            return false;
        }
    }

    true
}

#[test]
fn test() {
    {
        let root = build_node(&vec![[2, 1, 2], [1, -1, -1], [3, -1, -1]], 0);
        assert!(is_binary_search_tree(
            &root,
            Rc::new(Cell::new(std::i64::MIN))
        ));
    }
    {
        let root = build_node(&vec![[1, 1, 2], [2, -1, -1], [3, -1, -1]], 0);
        assert!(!is_binary_search_tree(
            &root,
            Rc::new(Cell::new(std::i64::MIN))
        ));
    }
    {
        let root = build_node(
            &vec![[1, -1, 1], [2, -1, 2], [3, -1, 3], [4, -1, 4], [5, -1, -1]],
            0,
        );
        assert!(is_binary_search_tree(
            &root,
            Rc::new(Cell::new(std::i64::MIN))
        ));
    }
    {
        let root = build_node(
            &vec![
                [4, 1, 2],
                [2, 3, 4],
                [6, 5, 6],
                [1, -1, -1],
                [3, -1, -1],
                [5, -1, -1],
                [7, -1, -1],
            ],
            0,
        );
        assert!(is_binary_search_tree(
            &root,
            Rc::new(Cell::new(std::i64::MIN))
        ));
    }
    {
        let root = build_node(&vec![[4, 1, -1], [2, 2, 3], [1, -1, -1], [5, -1, -1]], 0);
        assert!(!is_binary_search_tree(
            &root,
            Rc::new(Cell::new(std::i64::MIN))
        ));
    }
}
