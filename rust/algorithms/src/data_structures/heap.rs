use std::cmp::Ordering;

// *** 要素の重複はサポートしていない ***
//  -> change_priority を実装する際、プライオリティを変更する対象の要素を一意に特定するため、要素の重複をサポートできなかった.
// 例:
//     // 下記は extract_min() で panic が発生するか、正しい値を返せない
//     heap.insert(State { cost: 1, position: 1 });
//     heap.insert(State { cost: 1, position: 1 });
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
            println!("sift_up: i:{}, parent_i:{}", i, parent_i);
            if self.nodes[i] < self.nodes[parent_i] {
                println!("sift_up - swap: i:{}, parent_i:{}", i, parent_i);
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

    #[cfg(test)]
    fn nodes(&self) -> Vec<T> {
        self.nodes.clone()
    }
}

#[cfg(test)]
mod test_min_heap {
    use crate::data_structures::heap::MinHeap;
    use std::cmp::Ordering;

    #[derive(Clone, Eq, PartialEq, Debug)]
    struct State {
        cost: u64,
        position: usize,
    }

    impl Ord for State {
        fn cmp(&self, other: &Self) -> Ordering {
            self.cost
                .cmp(&other.cost)
                .then_with(|| self.position.cmp(&other.position))
        }
    }

    impl PartialOrd for State {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    #[test]
    fn insert_extract_min() {
        let mut heap = MinHeap::new();
        heap.insert(State {
            cost: 1,
            position: 0,
        });
        heap.insert(State {
            cost: 1,
            position: 1,
        });
        heap.insert(State {
            cost: 10,
            position: 1,
        });
        heap.insert(State {
            cost: 20,
            position: 1,
        });

        assert_eq!(
            State {
                cost: 1,
                position: 0
            },
            heap.extract_min().unwrap()
        );
        assert_eq!(
            State {
                cost: 1,
                position: 1
            },
            heap.extract_min().unwrap()
        );

        heap.change_priority(
            &State {
                cost: 20,
                position: 1,
            },
            State {
                cost: 2,
                position: 1,
            },
        )
        .unwrap();
        assert_eq!(
            State {
                cost: 2,
                position: 1
            },
            heap.extract_min().unwrap()
        );
    }

    #[test]
    fn parent_index() {
        assert_eq!(0, MinHeap::<State>::parent_index(0));
        assert_eq!(0, MinHeap::<State>::parent_index(1));
        assert_eq!(0, MinHeap::<State>::parent_index(2));
        assert_eq!(1, MinHeap::<State>::parent_index(3));
        assert_eq!(1, MinHeap::<State>::parent_index(4));
    }
}
