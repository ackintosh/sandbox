// https://www.coursera.org/learn/algorithms-on-graphs/programming/AUd0k/programming-assignment-1-decomposition-of-graphs/submission
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::process::exit;
use std::rc::Rc;

fn main() {
    let number_of_edges = {
        let nums = read_nums(2);
        nums[1]
    };
    let edges = read_edges(number_of_edges);
    let maze = build_graph(edges);
    let target = {
        let nums = read_nums(2);
        (nums[0], nums[1])
    };

    let visited = Rc::new(RefCell::new(vec![]));
    if finding_an_exit(&maze, &target.0, &target.1, visited) {
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

fn build_graph(input: Vec<(u64, u64)>) -> HashMap<u64, Vec<u64>> {
    fn add_edge(graph: &mut HashMap<u64, Vec<u64>>, u: u64, v: u64) {
        match graph.entry(u) {
            Entry::Occupied(mut entry) => {
                let vertices = entry.get_mut();
                vertices.push(v);
            }
            Entry::Vacant(entry) => {
                entry.insert(vec![v]);
            }
        }
    }

    let mut graph: HashMap<u64, Vec<u64>> = HashMap::new();

    for i in input {
        add_edge(&mut graph, i.0, i.1);
        add_edge(&mut graph, i.1, i.0);
    }

    graph
}

fn finding_an_exit(
    maze: &HashMap<u64, Vec<u64>>,
    v: &u64,
    target: &u64,
    visited: Rc<RefCell<Vec<u64>>>,
) -> bool {
    if visited.borrow().contains(v) {
        return false;
    }

    visited.borrow_mut().push(*v);
    if v == target {
        return true;
    }

    match maze.get(&v) {
        None => {}
        Some(adjacency) => {
            for a in adjacency {
                if finding_an_exit(maze, a, target, visited.clone()) {
                    return true;
                }
            }
        }
    }
    return false;
}

#[cfg(test)]
mod tests {
    use crate::{build_graph, finding_an_exit};
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn test_build_graph() {
        let graph = build_graph(vec![(1, 2), (3, 2), (4, 3), (1, 4)]);
        println!("{:?}", graph);
    }

    #[test]
    fn test_finding_an_exit() {
        {
            let visited = Rc::new(RefCell::new(vec![]));
            let maze = build_graph(vec![(1, 2), (3, 2), (4, 3), (1, 4)]);
            assert!(finding_an_exit(&maze, &1, &4, visited));
        }
        {
            let visited = Rc::new(RefCell::new(vec![]));
            let maze = build_graph(vec![(1, 2), (3, 2)]);
            assert!(!finding_an_exit(&maze, &1, &4, visited));
        }
    }
}
