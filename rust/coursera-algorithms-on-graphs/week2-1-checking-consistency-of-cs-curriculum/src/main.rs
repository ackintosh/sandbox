use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::process::exit;

fn main() {
    let number_of_edges = {
        let nums = read_nums(2);
        nums[1]
    };
    let edges = read_edges(number_of_edges);
    let graph = build_directed_graph(edges);

    if check_consistency(&graph) {
        println!("1");
    } else {
        println!("0");
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

fn build_directed_graph(edges: Vec<(u64, u64)>) -> HashMap<u64, Vec<u64>> {
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

fn check_consistency(graph: &HashMap<u64, Vec<u64>>) -> bool {
    for vertex in graph.keys() {
        if contains_cycle(vertex, graph, vec![]) {
            return true;
        }
    }

    false
}

fn contains_cycle(v: &u64, graph: &HashMap<u64, Vec<u64>>, mut visited: Vec<u64>) -> bool {
    if visited.contains(v) {
        // println!("v: {}, visited: {:?}", v, visited);
        return true;
    }

    visited.append(&mut vec![*v]);

    match graph.get(v) {
        None => {}
        Some(adjacency) => {
            for a in adjacency {
                if contains_cycle(a, graph, visited.clone()) {
                    return true;
                }
            }
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use crate::{build_directed_graph, check_consistency};

    #[test]
    fn test_build_directed_graph() {
        let g = build_directed_graph(vec![(1, 2), (4, 1), (2, 3), (3, 1)]);
        println!("{:?}", g);
    }

    #[test]
    fn test_check_consistency() {
        {
            let g = build_directed_graph(vec![(1, 2), (4, 1), (2, 3), (3, 1)]);
            assert!(check_consistency(&g));
        }
        {
            let g =
                build_directed_graph(vec![(1, 2), (2, 3), (1, 3), (3, 4), (1, 4), (2, 5), (3, 5)]);
            // println!("graph: {:?}", g);
            assert!(!check_consistency(&g));
        }
    }
}
