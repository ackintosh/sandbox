// https://leetcode.com/problems/spiral-matrix-iv/

// Definition for singly-linked list.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ListNode {
    pub val: i32,
    pub next: Option<Box<ListNode>>,
}

impl ListNode {
    #[inline]
    fn new(val: i32) -> Self {
        ListNode { next: None, val }
    }
}

struct Solution;

impl Solution {
    pub fn spiral_matrix(m: i32, n: i32, mut head: Option<Box<ListNode>>) -> Vec<Vec<i32>> {
        let mut vals = vec![];
        let mut head = &mut head;
        while let Some(node) = head.as_mut() {
            vals.push(node.val);
            head = &mut node.next;
        }
        vals.reverse();
        println!("{vals:?}");
        let mut answer = vec![vec![-99; n as usize]; m as usize];
        println!("{answer:?}");
        let mut w_m = 0;
        let mut w_n = 0;

        loop {
            Self::left_to_right(&mut answer, w_m, &mut w_n, &mut vals);
            // println!("{answer:?}");

            w_m += 1;
            if w_m >= m as usize {
                return answer;
            }
            if answer[w_m][w_n] != -99 {
                return answer;
            }

            Self::top_to_bottom(&mut answer, &mut w_m, w_n, &mut vals);
            // println!("{answer:?}");

            if w_n.checked_sub(1).is_none() {
                return answer;
            }
            w_n -= 1;
            if answer[w_m][w_n] != -99 {
                return answer;
            }

            Self::right_to_left(&mut answer, w_m, &mut w_n, &mut vals);
            // println!("{answer:?}");
            if w_m.checked_sub(1).is_none() {
                return answer;
            }
            w_m -= 1;
            if answer[w_m][w_n] != -99 {
                return answer;
            }

            Self::bottom_to_top(&mut answer, &mut w_m, w_n, &mut vals);
            // println!("{answer:?}");
            if w_n + 1 >= n as usize {
                return answer;
            }
            w_n += 1;
            if answer[w_m][w_n] != -99 {
                return answer;
            }
        }

        // answer
    }

    fn left_to_right(matrix: &mut Vec<Vec<i32>>, m: usize, w_n: &mut usize, vals: &mut Vec<i32>) {
        loop {
            matrix[m][*w_n] = if let Some(v) = vals.pop() { v } else { -1 };

            if let Some(v) = matrix[m].get(*w_n + 1) {
                if *v != -99 {
                    return;
                }
            } else {
                return;
            }

            *w_n += 1;
        }
    }

    fn top_to_bottom(matrix: &mut Vec<Vec<i32>>, w_m: &mut usize, w_n: usize, vals: &mut Vec<i32>) {
        loop {
            matrix[*w_m][w_n] = if let Some(v) = vals.pop() { v } else { -1 };

            if let Some(row) = matrix.get(*w_m + 1) {
                if row[w_n] != -99 {
                    return;
                }
            } else {
                return;
            }

            *w_m += 1;
        }
    }

    fn right_to_left(matrix: &mut Vec<Vec<i32>>, m: usize, w_n: &mut usize, vals: &mut Vec<i32>) {
        loop {
            matrix[m][*w_n] = if let Some(v) = vals.pop() { v } else { -1 };

            if w_n.checked_sub(1).is_none() {
                return;
            }
            if let Some(v) = matrix[m].get(*w_n - 1) {
                if *v != -99 {
                    return;
                }
            } else {
                return;
            }

            *w_n -= 1;
        }
    }

    fn bottom_to_top(matrix: &mut Vec<Vec<i32>>, w_m: &mut usize, w_n: usize, vals: &mut Vec<i32>) {
        loop {
            matrix[*w_m][w_n] = if let Some(v) = vals.pop() { v } else { -1 };

            if w_m.checked_sub(1).is_none() {
                return;
            }
            if let Some(row) = matrix.get(*w_m - 1) {
                if row[w_n] != -99 {
                    return;
                }
            } else {
                return;
            }

            *w_m -= 1;
        }
    }
}

#[test]
fn test() {
    let head = ListNode {
        val: 0,
        next: Some(Box::new(ListNode {
            val: 1,
            next: Some(Box::new(ListNode { val: 2, next: None })),
        })),
    };

    let answer = Solution::spiral_matrix(1, 4, Some(Box::new(head)));
    assert_eq!(vec![vec![0, 1, 2, -1]], answer);
}

#[test]
fn test2() {
    let head = ListNode {
        val: 3,
        next: Some(Box::new(ListNode {
            val: 0,
            next: Some(Box::new(ListNode {
                val: 2,
                next: Some(Box::new(ListNode {
                    val: 6,
                    next: Some(Box::new(ListNode {
                        val: 8,
                        next: Some(Box::new(ListNode {
                            val: 1,
                            next: Some(Box::new(ListNode {
                                val: 7,
                                next: Some(Box::new(ListNode {
                                    val: 9,
                                    next: Some(Box::new(ListNode {
                                        val: 4,
                                        next: Some(Box::new(ListNode {
                                            val: 2,
                                            next: Some(Box::new(ListNode {
                                                val: 5,
                                                next: Some(Box::new(ListNode {
                                                    val: 5,
                                                    next: Some(Box::new(ListNode {
                                                        val: 0,
                                                        next: None,
                                                    })),
                                                })),
                                            })),
                                        })),
                                    })),
                                })),
                            })),
                        })),
                    })),
                })),
            })),
        })),
    };

    let answer = Solution::spiral_matrix(3, 5, Some(Box::new(head)));
    assert_eq!(
        vec![
            vec![3, 0, 2, 6, 8],
            vec![5, 0, -1, -1, 1],
            vec![5, 2, 4, 9, 7]
        ],
        answer
    );
}
