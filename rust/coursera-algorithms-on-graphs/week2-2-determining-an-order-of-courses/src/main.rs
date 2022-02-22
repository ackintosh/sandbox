use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::process::exit;
use std::rc::Rc;

const MAX_NODES: usize = 100001; // indexの計算(ゼロオリジンと整合させるために +1 する)を省略するために、 100000 + 1 にしている

fn main() {
    let (number_of_nodes, number_of_edges) = {
        let nums = read_nums(2);
        (usize::try_from(nums[0]).unwrap(), nums[1])
    };
    let edges = read_edges(number_of_edges);
    let graph = build_directed_graph(&edges);

    for v in topological_sort(number_of_nodes, &graph).iter().rev() {
        print!("{} ", v);
    }
}

fn read_edges(number_of_edges: u64) -> Vec<(usize, usize)> {
    let mut edges = vec![];

    for _ in 0..number_of_edges {
        let mut buff = String::new();
        let res = std::io::stdin().read_line(&mut buff);
        if res.is_err() {
            println!("res: {:?}", res);
            exit(0);
        }
        let mut strs = buff.split_whitespace();

        let parsed_u = {
            let str = strs.next();
            if str.is_none() {
                println!("strs.next() is None");
                exit(0);
            }
            let parsed = str.unwrap().parse::<usize>();
            if parsed.is_err() {
                println!("parsed: {:?}", parsed);
                exit(0);
            }
            parsed.unwrap()
        };

        let parsed_v = {
            let str = strs.next();
            if str.is_none() {
                println!("strs.next() is None");
                exit(0);
            }
            let parsed = str.unwrap().parse::<usize>();
            if parsed.is_err() {
                println!("parsed: {:?}", parsed);
                exit(0);
            }
            parsed.unwrap()
        };

        edges.push((parsed_u, parsed_v));
    }

    edges
}

fn read_nums(number_of_elements: u64) -> Vec<u64> {
    let mut buff = String::new();
    let res = std::io::stdin().read_line(&mut buff);
    if res.is_err() {
        println!("res: {:?}", res);
        exit(0);
    }
    let mut strs = buff.split_whitespace();

    let mut nums = vec![];
    for _ in 0..number_of_elements {
        let str = strs.next();
        if str.is_none() {
            println!("strs.next() is None");
            exit(0);
        }
        let parsed = str.unwrap().parse::<u64>();
        if parsed.is_err() {
            println!("parsed: {:?}", parsed);
            exit(0);
        }
        nums.push(parsed.unwrap());
    }
    nums
}

fn build_directed_graph(edges: &Vec<(usize, usize)>) -> HashMap<usize, Vec<usize>> {
    let mut graph: HashMap<usize, Vec<usize>> = HashMap::new();

    for e in edges {
        match graph.entry(e.0) {
            Entry::Occupied(mut entry) => {
                entry.get_mut().push(e.1);
            }
            Entry::Vacant(entry) => {
                entry.insert(vec![e.1]);
            }
        }
    }

    graph
}

fn topological_sort(number_of_nodes: usize, graph: &HashMap<usize, Vec<usize>>) -> Vec<usize> {
    let sorted_nodes: Rc<RefCell<Vec<usize>>> = Rc::new(RefCell::new(vec![]));
    let visited: Rc<RefCell<[bool; MAX_NODES]>> = Rc::new(RefCell::new([false; MAX_NODES]));

    for node in 1_usize..=number_of_nodes {
        if visited.borrow()[node] {
            continue;
        }
        dfs(&node, graph, sorted_nodes.clone(), visited.clone());
    }

    let b = sorted_nodes.borrow_mut();
    b.clone()
}

fn dfs(
    node: &usize,
    graph: &HashMap<usize, Vec<usize>>,
    sorted_nodes: Rc<RefCell<Vec<usize>>>,
    visited: Rc<RefCell<[bool; MAX_NODES]>>,
) {
    visited.borrow_mut()[*node] = true;

    match graph.get(node) {
        None => {
            sorted_nodes.borrow_mut().push(*node);
        }
        Some(edges) => {
            for e in edges {
                if visited.borrow()[*e] {
                    continue;
                }
                dfs(e, graph, sorted_nodes.clone(), visited.clone());
            }

            // Postorder
            sorted_nodes.borrow_mut().push(*node);
        }
    }
}

#[test]
fn test_topological_sort() {
    {
        let g = build_directed_graph(&vec![(1, 2), (4, 1), (3, 1)]);
        println!("{:?}", g);
        let mut s = topological_sort(4, &g);
        s.reverse();
        println!("{:?}", s);
    }
    {
        let g = build_directed_graph(&vec![(3, 1)]);
        println!("{:?}", g);
        let mut s = topological_sort(4, &g);
        s.reverse();
        println!("{:?}", s);
    }
}
