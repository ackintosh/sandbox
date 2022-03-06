// ダイクストラ法の実装
// 参考: BinaryHeapの使用例でダイクストラ法の実装が紹介されている
//      https://doc.rust-lang.org/stable/src/alloc/collections/binary_heap.rs.html#11
use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::{BinaryHeap, HashMap};
use std::convert::TryFrom;
use std::process::exit;

fn main() {
    let (number_of_nodes, number_of_edges) = {
        let nums = read_nums(2);
        (usize::try_from(nums[0]).unwrap(), nums[1])
    };

    let edges = read_edges(number_of_edges);

    let (start, goal) = {
        let nums = read_nums(2);
        (
            usize::try_from(nums[0]).unwrap(),
            usize::try_from(nums[1]).unwrap(),
        )
    };

    let (graph, weight) = build_directed_graph_with_weight(&edges);

    match dijkstra(&graph, &weight, number_of_nodes, start, goal) {
        None => println!("-1"),
        Some(minimum_weight) => println!("{}", minimum_weight),
    };
}

fn read_edges(number_of_edges: u64) -> Vec<(usize, usize, usize)> {
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

        let parsed_w = {
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

        edges.push((parsed_u, parsed_v, parsed_w));
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

fn build_directed_graph_with_weight(
    input: &Vec<(usize, usize, usize)>,
) -> (HashMap<usize, Vec<usize>>, HashMap<(usize, usize), usize>) {
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
    let mut weight = HashMap::new();

    for i in input {
        add_edge(&mut graph, i.0, i.1);
        weight.insert((i.0, i.1), i.2);
    }

    (graph, weight)
}

#[derive(Eq, PartialEq)]
struct State {
    cost: usize,
    position: usize,
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .cost
            .cmp(&self.cost)
            .then_with(|| other.position.cmp(&self.position))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn dijkstra(
    graph: &HashMap<usize, Vec<usize>>,
    weight: &HashMap<(usize, usize), usize>,
    number_of_nodes: usize,
    start: usize,
    goal: usize,
) -> Option<usize> {
    let mut distance: Vec<usize> = (0..=number_of_nodes).map(|_| std::usize::MAX).collect();
    let mut heap: BinaryHeap<State> = BinaryHeap::new();

    distance[start] = 0;
    heap.push(State {
        cost: 0,
        position: start,
    });

    while let Some(state) = heap.pop() {
        // println!("pop: position:{}, cost:{}", state.position, state.cost);
        if state.position == goal {
            return Some(state.cost);
        }

        distance[state.position] = state.cost;
        if let Some(edges) = graph.get(&state.position) {
            for e in edges {
                let w = weight
                    .get(&(state.position, *e))
                    .expect(format!("should have weight: {}, {}", state.position, e).as_str());
                let next_state = State {
                    cost: distance[state.position] + w,
                    position: *e,
                };
                if distance[*e] > next_state.cost {
                    distance[*e] = next_state.cost;
                    // println!("push: position:{}, cost:{}", next_state.position, next_state.cost);
                    heap.push(next_state);
                }
            }
        }
    }

    None
}

#[test]
fn test() {
    // example1
    let (graph, weight) =
        build_directed_graph_with_weight(&vec![(1, 2, 1), (4, 1, 2), (2, 3, 2), (1, 3, 5)]);
    let number_of_nodes = 4;
    assert_eq!(Some(3), dijkstra(&graph, &weight, number_of_nodes, 1, 3));

    // example2
    let (graph, weight) = build_directed_graph_with_weight(&vec![
        (1, 2, 4),
        (1, 3, 2),
        (2, 3, 2),
        (3, 2, 1),
        (2, 4, 2),
        (3, 5, 4),
        (5, 4, 1),
        (2, 5, 3),
        (3, 4, 4),
    ]);
    let number_of_nodes = 5;
    assert_eq!(Some(6), dijkstra(&graph, &weight, number_of_nodes, 1, 5));

    // example3
    let (graph, weight) = build_directed_graph_with_weight(&vec![(1, 2, 7), (1, 3, 5), (2, 3, 2)]);
    let number_of_nodes = 3;
    assert_eq!(None, dijkstra(&graph, &weight, number_of_nodes, 3, 2));
}
