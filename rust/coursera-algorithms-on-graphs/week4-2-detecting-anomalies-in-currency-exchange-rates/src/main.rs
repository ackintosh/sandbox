use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::process::exit;

fn main() {
    let (number_of_nodes, number_of_edges) = {
        let nums = read_nums(2);
        (usize::try_from(nums[0]).unwrap(), nums[1])
    };

    let edges = read_edges(number_of_edges);

    let (graph, weight) = build_directed_graph_with_weight(&edges);

    if detect_negative_cycle(&graph, &weight, number_of_nodes) {
        println!("1");
    } else {
        println!("0");
    }
}

fn read_edges(number_of_edges: u64) -> Vec<(usize, usize, isize)> {
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
            let parsed = str.unwrap().parse::<isize>();
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

type Graph = HashMap<usize, Vec<usize>>;
type Weight = HashMap<(usize, usize), isize>;

fn build_directed_graph_with_weight(input: &Vec<(usize, usize, isize)>) -> (Graph, Weight) {
    fn add_edge(graph: &mut Graph, u: usize, v: usize) {
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

    let mut graph: Graph = HashMap::new();
    let mut weight = HashMap::new();

    for i in input {
        add_edge(&mut graph, i.0, i.1);
        weight.insert((i.0, i.1), i.2);
    }

    (graph, weight)
}

// グラフに負閉路が含まれているかどうかを検査する
// 全エッジで Relaxation を行うのを |V| 回実行する
//   -> |V| 回目のループで、まだ Relaxation の影響を受けたノードがある場合、負閉路を含んでいると判定できる
fn detect_negative_cycle(graph: &Graph, weight: &Weight, number_of_nodes: usize) -> bool {
    // 課題の制約で、エッジの重みが最大で 1,000 なので、ここでは 1,001 を初期値に設定している
    let mut distance: Vec<isize> = (0..=number_of_nodes).map(|_| 1001_isize).collect();

    let mut relaxed = false;
    for _ in 0..number_of_nodes {
        relaxed = false;

        for u in graph.keys() {
            for v in graph.get(u).unwrap() {
                let weight = weight.get(&(*u, *v)).unwrap();
                if distance[*v] > distance[*u] + weight {
                    distance[*v] = distance[*u] + weight;
                    relaxed = true;
                }
            }
        }
    }

    relaxed
}

#[test]
fn test() {
    let (graph, weight) =
        build_directed_graph_with_weight(&vec![(1, 2, -5), (4, 1, 2), (2, 3, 2), (3, 1, 1)]);
    // println!("{:?}", graph);
    // println!("{:?}", weight);

    assert!(detect_negative_cycle(&graph, &weight, 4));
}
