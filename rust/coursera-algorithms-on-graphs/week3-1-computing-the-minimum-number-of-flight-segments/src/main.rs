use std::collections::hash_map::Entry;
use std::collections::{HashMap, VecDeque};
use std::convert::TryFrom;
use std::process::exit;

fn main() {
    let (_number_of_nodes, number_of_edges) = {
        let nums = read_nums(2);
        (usize::try_from(nums[0]).unwrap(), nums[1])
    };
    let edges = read_edges(number_of_edges);
    let (u, v) = {
        let nums = read_nums(2);
        (
            usize::try_from(nums[0]).unwrap(),
            usize::try_from(nums[1]).unwrap(),
        )
    };

    let graph = build_undirected_graph(&edges);
    let (distance, _prev) = build_shortest_path_tree(&graph, u);
    if let Some(d) = distance.get(&v) {
        println!("{}", d);
    } else {
        println!("-1");
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

fn build_undirected_graph(input: &Vec<(usize, usize)>) -> HashMap<usize, Vec<usize>> {
    fn add_edge(graph: &mut HashMap<usize, Vec<usize>>, u: usize, v: usize) {
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

    let mut graph: HashMap<usize, Vec<usize>> = HashMap::new();

    for i in input {
        add_edge(&mut graph, i.0, i.1);
        add_edge(&mut graph, i.1, i.0);
    }

    graph
}

fn build_shortest_path_tree(
    graph: &HashMap<usize, Vec<usize>>,
    root: usize,
) -> (HashMap<usize, u64>, HashMap<usize, usize>) {
    let mut queue: VecDeque<usize> = VecDeque::new();
    let mut distance: HashMap<usize, u64> = HashMap::new();
    let mut prev: HashMap<usize, usize> = HashMap::new();

    queue.push_front(root);
    distance.insert(root, 0);
    prev.insert(root, 0);

    bfs(&graph, &mut queue, &mut distance, &mut prev);

    // println!("{:?}", distance);
    // println!("{:?}", prev);

    (distance, prev)
}

fn bfs(
    graph: &HashMap<usize, Vec<usize>>,
    queue: &mut VecDeque<usize>,
    distance: &mut HashMap<usize, u64>,
    prev: &mut HashMap<usize, usize>,
) {
    while let Some(node) = queue.pop_back() {
        if let Some(edges) = graph.get(&node) {
            let d = *distance
                .get(&node)
                .expect(format!("should have distance for {}", node).as_str());
            for e in edges {
                if distance.get(e).is_some() {
                    // 探索済みのノードのためスキップする
                    continue;
                }
                queue.push_front(*e);
                distance.insert(*e, d + 1);
                prev.insert(*e, node);
            }
        }
    }
}

#[test]
fn test() {
    {
        let g = build_undirected_graph(&vec![(1, 2), (4, 1), (2, 3), (3, 1)]);
        let (distance, _prev) = build_shortest_path_tree(&g, 2);
        assert_eq!(Some(&2), distance.get(&4))
    }
    {
        let g = build_undirected_graph(&vec![(5, 2), (1, 3), (3, 4), (1, 4)]);
        let (distance, _prev) = build_shortest_path_tree(&g, 3);
        assert_eq!(None, distance.get(&5))
    }
}
