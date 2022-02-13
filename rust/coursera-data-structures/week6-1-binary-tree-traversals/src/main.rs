use std::convert::TryFrom;
use std::process::exit;
use std::rc::Rc;

fn main() {
    let n: u64 = read_num();
    let input = read_nodes(n);
    let root_node = build_node(&input, 0);

    {
        let mut result = vec![];
        in_order_traversal(Rc::new(root_node.clone()), &mut result);
        print_result(&result);
    }

    {
        let mut result = vec![];
        pre_order_traversal(Rc::new(root_node.clone()), &mut result);
        print_result(&result);
    }

    {
        let mut result = vec![];
        post_order_traversal(Rc::new(root_node), &mut result);
        print_result(&result);
    }

    fn print_result(result: &Vec<u64>) {
        for r in result {
            print!("{} ", r);
        }
        println!();
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
    key: u64,
    left: Option<Rc<Node>>,
    right: Option<Rc<Node>>,
}

impl Node {
    fn new(key: u64) -> Self {
        Self {
            key,
            left: None,
            right: None,
        }
    }
}

fn build_node(input: &Vec<[i64; 3]>, index: usize) -> Node {
    let mut node = Node::new(u64::try_from(input[index][0]).unwrap());

    if input[index][1] != -1 {
        node.left = Some(Rc::new(build_node(input, input[index][1] as usize)));
    }

    if input[index][2] != -1 {
        node.right = Some(Rc::new(build_node(input, input[index][2] as usize)));
    }

    node
}

fn in_order_traversal(node: Rc<Node>, output: &mut Vec<u64>) {
    if let Some(left) = &node.left {
        in_order_traversal(left.clone(), output);
    }

    output.push(node.key);

    if let Some(right) = &node.right {
        in_order_traversal(right.clone(), output);
    }
}

fn pre_order_traversal(node: Rc<Node>, output: &mut Vec<u64>) {
    output.push(node.key);

    if let Some(left) = &node.left {
        pre_order_traversal(left.clone(), output);
    }

    if let Some(right) = &node.right {
        pre_order_traversal(right.clone(), output);
    }
}

fn post_order_traversal(node: Rc<Node>, output: &mut Vec<u64>) {
    if let Some(left) = &node.left {
        post_order_traversal(left.clone(), output);
    }

    if let Some(right) = &node.right {
        post_order_traversal(right.clone(), output);
    }

    output.push(node.key);
}

#[cfg(test)]
mod tests {
    use crate::{build_node, in_order_traversal, post_order_traversal, pre_order_traversal};
    use std::rc::Rc;

    #[test]
    fn test_build_tree() {
        let root = build_node(
            &vec![[4, 1, 2], [2, 3, 4], [5, -1, -1], [1, -1, -1], [3, -1, -1]],
            0,
        );
        println!("{:?}", root);
        //      4
        //    /  \
        //   2    5
        //  / \
        // 1   3
    }

    #[test]
    fn test_in_order_traversal() {
        let root = build_node(
            &vec![[4, 1, 2], [2, 3, 4], [5, -1, -1], [1, -1, -1], [3, -1, -1]],
            0,
        );
        let mut result = vec![];
        in_order_traversal(Rc::new(root), &mut result);
        assert_eq!(vec![1, 2, 3, 4, 5], result);
    }

    #[test]
    fn test_pre_order_traversal() {
        let root = build_node(
            &vec![[4, 1, 2], [2, 3, 4], [5, -1, -1], [1, -1, -1], [3, -1, -1]],
            0,
        );
        let mut result = vec![];
        pre_order_traversal(Rc::new(root), &mut result);
        assert_eq!(vec![4, 2, 1, 3, 5], result);
    }

    #[test]
    fn test_post_order_traversal() {
        let root = build_node(
            &vec![[4, 1, 2], [2, 3, 4], [5, -1, -1], [1, -1, -1], [3, -1, -1]],
            0,
        );
        let mut result = vec![];
        post_order_traversal(Rc::new(root), &mut result);
        assert_eq!(vec![1, 3, 2, 5, 4], result);
    }
}
