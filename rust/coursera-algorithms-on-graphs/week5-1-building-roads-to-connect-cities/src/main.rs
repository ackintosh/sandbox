// https://www.coursera.org/learn/algorithms-on-graphs/programming/DpmDw/programming-assignment-5-minimum-spanning-trees

use std::cmp::Ordering;
use std::process::exit;

fn main() {
    let n = read_nums(1);
    let cities = read_edges(*n.first().unwrap());

    println!("{}", minimum_total_length_of_segments(&cities));
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

fn read_edges(number_of_edges: u64) -> Vec<(i32, i32)> {
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
            let parsed = str.unwrap().parse::<i32>();
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
            let parsed = str.unwrap().parse::<i32>();
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

#[derive(Clone, Debug, PartialEq)]
struct State {
    cost: f64,
    city: usize,
}

impl Eq for State {}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cost
            .partial_cmp(&other.cost)
            .unwrap()
            .then_with(|| self.city.cmp(&other.city))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn minimum_total_length_of_segments(cities: &Vec<(i32, i32)>) -> f64 {
    let mut total_length = 0.0;

    // 初期のコストは最大値にしておく
    let mut cost: MinHeap<State> = MinHeap::new();
    // 開始地点として、最初のcityのコストを 0 にする
    cost.insert(State {
        cost: 0.0,
        city: 0, // 最初のcity
    });
    for i in 1..cities.len() {
        cost.insert(State {
            cost: std::f64::MAX,
            city: i,
        });
    }

    while let Some(c) = cost.extract_min() {
        // println!("extract_min: {:?}", c);
        total_length += c.cost;

        for other in cost.nodes() {
            let addr1 = cities[c.city];
            let addr2 = cities[other.city];
            let new_cost =
                (((addr1.0 - addr2.0).pow(2) + (addr1.1 - addr2.1).pow(2)) as f64).sqrt();
            // change_priority
            if new_cost < other.cost {
                cost.change_priority(
                    &State {
                        cost: other.cost,
                        city: other.city,
                    },
                    State {
                        cost: new_cost,
                        city: other.city,
                    },
                )
                .unwrap();
            }
        }
    }

    total_length
}

// *** algorithms/src/data_structures/heap.rs からコピーして調整した ***
struct MinHeap<T>
where
    T: Ord,
{
    nodes: Vec<T>,
}

impl<T> MinHeap<T>
where
    T: Ord + Clone,
{
    pub fn new() -> Self {
        Self {
            nodes: vec![], // 0-based
        }
    }

    pub fn insert(&mut self, element: T) {
        self.nodes.push(element);
        self.sift_up(self.nodes.len() - 1);
    }

    fn sift_up(&mut self, index: usize) {
        let mut i = index.clone();
        let mut parent_i = Self::parent_index(i);
        while i != 0 {
            // min-heap
            // println!("sift_up: i:{}, parent_i:{}", i, parent_i);
            if self.nodes[i] < self.nodes[parent_i] {
                // println!("sift_up - swap: i:{}, parent_i:{}", i, parent_i);
                self.swap(i, parent_i);
            }
            i = parent_i;
            parent_i = Self::parent_index(i);
        }
    }

    fn sift_down(&mut self, index: usize) {
        match self.smaller_child(index) {
            None => {}
            Some(child_index) => match self.nodes[child_index].cmp(&self.nodes[index]) {
                Ordering::Less => {
                    self.swap(child_index, index);
                    self.sift_down(child_index);
                }
                Ordering::Equal => {
                    panic!("このHeap実装では要素の重複をサポートしていません");
                }
                Ordering::Greater => {}
            },
        }
    }

    fn swap(&mut self, a: usize, b: usize) {
        let tmp_a = self.nodes[a].clone();
        self.nodes[a] = self.nodes[b].clone();
        self.nodes[b] = tmp_a;
    }

    pub fn extract_min(&mut self) -> Option<T> {
        if self.nodes.is_empty() {
            return None;
        } else if self.nodes.len() == 1 {
            return self.nodes.pop();
        }

        let min = self.nodes.first().expect("should have element").clone();
        self.nodes[0] = self.nodes.pop().expect("should have element");
        self.sift_down(0);
        Some(min)
    }

    // 注意: 変更対象のノードを特定するために self.nodes 全体を走査しているので O(N) になっている
    pub fn change_priority(&mut self, node: &T, new_node: T) -> Result<(), String> {
        match self.nodes.iter().position(|n| n == node) {
            None => Err("要素が存在しません".to_owned()),
            Some(index) => {
                self.nodes[index] = new_node.clone();
                if &new_node < node {
                    self.sift_up(index);
                } else {
                    self.sift_down(index);
                }
                Ok(())
            }
        }
    }

    fn parent_index(index: usize) -> usize {
        // root node
        if index == 0 {
            return index;
        }

        (index - 1) / 2
    }

    fn smaller_child(&self, index: usize) -> Option<usize> {
        let left_i = Self::left_child(index);
        let right_i = Self::right_child(index);

        match (self.nodes.get(left_i), self.nodes.get(right_i)) {
            (None, None) => None,
            (Some(_), None) => Some(left_i),
            (None, Some(_)) => Some(right_i),
            (Some(left), Some(right)) => match left.cmp(&right) {
                Ordering::Less => Some(left_i),
                Ordering::Equal => {
                    panic!("このHeap実装では要素の重複をサポートしていません")
                }
                Ordering::Greater => Some(right_i),
            },
        }
    }

    fn left_child(index: usize) -> usize {
        index * 2 + 1
    }

    fn right_child(index: usize) -> usize {
        index * 2 + 2
    }

    pub fn nodes(&self) -> Vec<T> {
        self.nodes.clone()
    }
}

#[test]
fn test() {
    let cities = vec![(0, 0), (0, 1), (1, 0), (1, 1)];
    assert_eq!(3.0, minimum_total_length_of_segments(&cities));

    let cities = vec![(0, 0), (0, 2), (1, 1), (3, 0), (3, 2)];
    assert_eq!(7.06449510224598, minimum_total_length_of_segments(&cities));
}
