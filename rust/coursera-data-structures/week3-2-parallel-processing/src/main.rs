use std::cmp::Ordering;
use std::process::exit;

fn main() {
    let (num_threads, num_jobs) = {
        let nums = read_nums(2);
        (nums[0], nums[1])
    };
    let jobs = read_nums(num_jobs);

    for p in parallel_processing(num_threads, jobs) {
        println!("{} {}", p.0, p.1);
    }
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

fn parallel_processing(num_threads: u64, jobs: Vec<u64>) -> Vec<(u64, u64)> {
    let mut result = vec![];
    let mut heap: MinHeap<Job> = MinHeap::new();

    let mut current_time = 0;
    let mut job_progress: usize = 0;

    for thread_no in 0..num_threads {
        if jobs.len() <= job_progress {
            // スレッド数よりもジョブ数の方が少ないパターン
            break;
        }

        let job = jobs[job_progress];
        job_progress += 1;

        heap.insert(Job {
            thread_no,
            time_started: current_time,
            estimated_time: job,
        });
    }

    while let Some(processed_job) = heap.extract_min() {
        result.push((processed_job.thread_no, processed_job.time_started));
        current_time = processed_job.time_started + processed_job.estimated_time;

        // ジョブが残っていれば処理する
        if jobs.len() > job_progress {
            heap.insert(Job {
                thread_no: processed_job.thread_no,
                time_started: current_time,
                estimated_time: jobs[job_progress],
            });
            job_progress += 1;
        }
    }

    result
}

struct MinHeap<T>
where
    T: Node,
{
    nodes: Vec<T>,
}

impl<T> MinHeap<T>
where
    T: Node + Clone,
{
    fn new() -> Self {
        Self {
            nodes: vec![], // 0-based
        }
    }

    fn insert(&mut self, element: T) {
        self.nodes.push(element);
        self.sift_up(self.nodes.len() - 1);
    }

    fn sift_up(&mut self, index: usize) {
        let mut i = index.clone();
        let mut parent_i = Self::parent_index(i);
        while i != 0 {
            // min-heap
            // println!("sift_up: i:{}, parent_i:{}", i, parent_i);
            if self.nodes[i].value() < self.nodes[parent_i].value() {
                self.swap(i, parent_i);
            }
            i = parent_i;
            parent_i = Self::parent_index(i);
        }
    }

    fn sift_down(&mut self, index: usize) {
        match self.smaller_child(index) {
            None => {}
            Some(child_index) => {
                match self.nodes[child_index]
                    .value()
                    .cmp(&self.nodes[index].value())
                {
                    Ordering::Less => {
                        self.swap(child_index, index);
                        self.sift_down(child_index);
                    }
                    Ordering::Equal => {
                        // スレッド番号が若いノードを優先する
                        if self.nodes[child_index].additional_ordering_value()
                            < self.nodes[index].additional_ordering_value()
                        {
                            self.swap(child_index, index);
                            self.sift_down(child_index);
                        }
                    }
                    Ordering::Greater => {}
                }
            }
        }
    }

    fn swap(&mut self, a: usize, b: usize) {
        let tmp_a = self.nodes[a].clone();
        self.nodes[a] = self.nodes[b].clone();
        self.nodes[b] = tmp_a;
    }

    fn extract_min(&mut self) -> Option<T> {
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
            (Some(left), Some(right)) => {
                match left.value().cmp(&right.value()) {
                    Ordering::Less => Some(left_i),
                    Ordering::Equal => {
                        // スレッド番号が若いノードを優先する
                        if left.additional_ordering_value() < right.additional_ordering_value() {
                            Some(left_i)
                        } else {
                            Some(right_i)
                        }
                    }
                    Ordering::Greater => Some(right_i),
                }
            }
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

trait Node {
    fn value(&self) -> u64;

    fn additional_ordering_value(&self) -> u64;
}

#[derive(Clone, Debug)]
struct Job {
    pub thread_no: u64,
    pub time_started: u64,
    pub estimated_time: u64,
}

impl Node for Job {
    fn value(&self) -> u64 {
        self.time_started + self.estimated_time
    }

    fn additional_ordering_value(&self) -> u64 {
        self.thread_no
    }
}

#[cfg(test)]
mod test_heap {
    use crate::{Job, MinHeap};

    #[test]
    fn insert_extract_min() {
        let mut heap = MinHeap::new();
        heap.insert(Job {
            thread_no: 0,
            time_started: 0,
            estimated_time: 3,
        });
        heap.insert(Job {
            thread_no: 1,
            time_started: 0,
            estimated_time: 2,
        });
        heap.insert(Job {
            thread_no: 2,
            time_started: 0,
            estimated_time: 1,
        });

        {
            let nodes = heap.nodes();
            // println!("{:?}", nodes);
            assert_eq!(3, nodes.len());
            assert_eq!(2, nodes.first().unwrap().thread_no);
        }

        {
            let job = heap.extract_min().expect("should have min element");
            assert_eq!(2, job.thread_no);
            let nodes = heap.nodes();
            // println!("{:?}", nodes);
            assert_eq!(2, nodes.len());
            assert_eq!(1, nodes.first().unwrap().thread_no);
        }
    }

    #[test]
    fn parent_index() {
        assert_eq!(0, MinHeap::<Job>::parent_index(0));
        assert_eq!(0, MinHeap::<Job>::parent_index(1));
        assert_eq!(0, MinHeap::<Job>::parent_index(2));
        assert_eq!(1, MinHeap::<Job>::parent_index(3));
        assert_eq!(1, MinHeap::<Job>::parent_index(4));
    }
}

#[test]
fn test_parallel_processing() {
    assert_eq!(vec![(0, 0)], parallel_processing(2, vec![1]));

    assert_eq!(
        vec![(1, 0), (0, 0), (1, 0)],
        parallel_processing(2, vec![1, 0, 2])
    );

    assert_eq!(
        vec![(0, 0), (0, 1), (0, 3)],
        parallel_processing(1, vec![1, 2, 3])
    );

    assert_eq!(
        vec![(0, 0), (1, 0), (0, 1), (1, 2), (0, 4)],
        parallel_processing(2, vec![1, 2, 3, 4, 5])
    );

    assert_eq!(
        vec![
            (0, 0),
            (1, 0),
            (2, 0),
            (3, 0),
            (0, 1),
            (1, 1),
            (2, 1),
            (3, 1),
            (0, 2),
            (1, 2),
            (2, 2),
            (3, 2),
            (0, 3),
            (1, 3),
            (2, 3),
            (3, 3),
            (0, 4),
            (1, 4),
            (2, 4),
            (3, 4)
        ],
        parallel_processing(
            4,
            vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
        )
    );
}
