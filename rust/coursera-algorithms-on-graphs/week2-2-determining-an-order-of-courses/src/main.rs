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
    // let mut graph = initialize_directed_graph(number_of_nodes);
    let graph = build_directed_graph(&edges);

    topological_sort(&number_of_nodes, &graph);
    // for v in topological_sort(&number_of_nodes, &graph).iter().rev() {
    //     print!("{} ", v);
    // }
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

// fn initialize_directed_graph(number_of_nodes: u64) -> HashMap<u64, Vec<u64>> {
//     let mut graph: HashMap<u64, Vec<u64>> = HashMap::new();
//     for n in 1..=number_of_nodes {
//         graph.insert(n, vec![]);
//     }
//
//     graph
// }

fn build_directed_graph(edges: &Vec<(u64, u64)>) -> HashMap<u64, Vec<u64>>{
    let mut graph: HashMap<u64, Vec<u64>> = HashMap::new();

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

fn topological_sort(number_of_nodes: &u64, graph: &HashMap<u64, Vec<u64>>) {
    let sorted_nodes: Rc<RefCell<Vec<u64>>> = Rc::new(RefCell::new(vec![]));

    for node in 1_u64..=*number_of_nodes {
        if sorted_nodes.borrow().contains(&node) {
            continue;
        }
        dfs(&node, graph, sorted_nodes.clone());
    }

    let mut b = sorted_nodes.borrow_mut();
    // b.clone()
    while let Some(v) = b.pop() {
        print!("{} ", v);
    }
    // for v in b.iter().rev() {
    //     print!("{} ", v);
    // }
}

fn dfs(node: &u64, graph: &HashMap<u64, Vec<u64>>, sorted_nodes: Rc<RefCell<Vec<u64>>>) {
    match graph.get(node) {
        None => {
            sorted_nodes.borrow_mut().push(*node);
        }
        Some(edges) => {
            for e in edges {
                if sorted_nodes.borrow().contains(e) {
                    continue;
                }
                dfs(e, graph, sorted_nodes.clone());
            }

            // Postorder
            sorted_nodes.borrow_mut().push(*node);
        }
    }
}

// #[test]
// fn test_topological_sort() {
//     {
//         // let mut g = initialize_directed_graph(4);
//         let g = build_directed_graph(&vec![(1, 2), (4, 1), (3, 1)]);
//         println!("{:?}", g);
//         let mut s = topological_sort(&4, &g);
//         s.reverse();
//         println!("{:?}", s);
//     }
//     {
//         // let mut g = initialize_directed_graph(4);
//         let g = build_directed_graph(&vec![(3, 1)]);
//         println!("{:?}", g);
//         let mut s = topological_sort(&4, &g);
//         s.reverse();
//         println!("{:?}", s);
//     }
// }
