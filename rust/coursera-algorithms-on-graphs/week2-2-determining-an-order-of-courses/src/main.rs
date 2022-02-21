use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::process::exit;
use std::rc::Rc;

fn main() {
    let (number_of_nodes, number_of_edges) = {
        let nums = read_nums(2);
        (nums[0], nums[1])
    };
    let edges = read_edges(number_of_edges);
    let mut graph = initialize_directed_graph(number_of_nodes);
    build_directed_graph(edges, &mut graph);

    for v in topological_sort(&graph) {
        print!("{} ", v);
    }
}

fn read_edges(number_of_edges: u64) -> Vec<(u64, u64)> {
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
            let parsed = str.unwrap().parse::<u64>();
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
            let parsed = str.unwrap().parse::<u64>();
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

fn initialize_directed_graph(number_of_nodes: u64) -> HashMap<u64, Vec<u64>> {
    let mut graph: HashMap<u64, Vec<u64>> = HashMap::new();
    for n in 1..=number_of_nodes {
        graph.insert(n, vec![]);
    }

    graph
}

fn build_directed_graph(edges: Vec<(u64, u64)>, graph: &mut HashMap<u64, Vec<u64>>) {
    for e in edges {
        match graph.entry(e.0) {
            Entry::Occupied(mut entry) => {
                entry.get_mut().push(e.1);
            }
            Entry::Vacant(_) => unreachable!(), // `initialize_directed_graph` でグラフが正しく初期化されていればここには到達しない
        }
    }
}

fn topological_sort(graph: &HashMap<u64, Vec<u64>>) -> Vec<u64> {
    let sorted_nodes: Rc<RefCell<Vec<u64>>> = Rc::new(RefCell::new(vec![]));

    for node in graph.keys() {
        if sorted_nodes.borrow().contains(node) {
            continue;
        }
        dfs(node, graph, sorted_nodes.clone());
    }

    sorted_nodes.borrow_mut().reverse();
    let nodes = sorted_nodes.borrow();
    nodes.clone()
}

fn dfs(node: &u64, graph: &HashMap<u64, Vec<u64>>, sorted_nodes: Rc<RefCell<Vec<u64>>>) {
    match graph.get(node) {
        None => unreachable!(), // `initialize_directed_graph` でグラフが正しく初期化されていればここには到達しない
        Some(edges) => {
            if edges.is_empty() {
                sorted_nodes.borrow_mut().push(*node);
                return;
            }

            for e in edges {
                if sorted_nodes.borrow().contains(e) {
                    continue;
                }
                dfs(e, graph, sorted_nodes.clone());
            }
            sorted_nodes.borrow_mut().push(*node);
        }
    }
}

#[test]
fn test_topological_sort() {
    {
        let mut g = initialize_directed_graph(4);
        build_directed_graph(vec![(1, 2), (4, 1), (3, 1)], &mut g);
        println!("{:?}", g);
        let s = topological_sort(&g);
        println!("{:?}", s);
    }
    {
        let mut g = initialize_directed_graph(4);
        build_directed_graph(vec![(3, 1)], &mut g);
        println!("{:?}", g);
        let s = topological_sort(&g);
        println!("{:?}", s);
    }
}
