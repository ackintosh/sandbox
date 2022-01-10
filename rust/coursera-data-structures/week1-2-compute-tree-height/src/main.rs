use std::collections::hash_map::Entry;
use std::collections::{HashMap, VecDeque};

fn main() {
    let n = read_num();
    let nums = read_nums(n);
    println!("{}", compute_tree_height(&nums));
}

fn read_num() -> u64 {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<u64>().unwrap()
}

fn read_nums(number_of_elements: u64) -> Vec<i64> {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    let mut strs = buff.split_whitespace();

    let mut nums = vec![];
    for _ in 0..number_of_elements {
        nums.push(strs.next().unwrap().parse::<i64>().unwrap());
    }
    nums
}

fn compute_tree_height(nums: &Vec<i64>) -> u64 {
    let nodes = {
        let mut nodes: HashMap<i64, Vec<usize>> = HashMap::new();
        for (pos, parent_pos) in nums.iter().enumerate() {
            match nodes.entry(*parent_pos) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().push(pos);
                }
                Entry::Vacant(entry) => {
                    entry.insert(vec![pos]);
                }
            }
        }
        nodes
    };
    // println!("{:?}", nodes);

    let mut queue: VecDeque<(usize, u64)> = VecDeque::new();
    let root_node_pos = *nodes
        .get(&-1)
        .expect("should have root node")
        .first()
        .expect("should have root node");
    queue.push_back((root_node_pos, 1)); // (pos, height)

    let mut max_height = 0;
    while let Some((pos, height)) = queue.pop_front() {
        max_height = max_height.max(height);

        if let Some(children) = nodes.get(&(pos as i64)) {
            for child_pos in children {
                queue.push_back((*child_pos, height + 1));
            }
        }
    }

    max_height
}

#[test]
fn test_compute_tree_height() {
    assert_eq!(3, compute_tree_height(&vec![4, -1, 4, 1, 1]));
    assert_eq!(4, compute_tree_height(&vec![-1, 0, 4, 0, 3]));
}
