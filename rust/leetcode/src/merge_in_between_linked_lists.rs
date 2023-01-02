// https://leetcode.com/problems/merge-in-between-linked-lists/

use std::mem;

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
    pub fn merge_in_between(
        list1: Option<Box<ListNode>>,
        a: i32,
        b: i32,
        list2: Option<Box<ListNode>>,
    ) -> Option<Box<ListNode>> {
        let mut current_list1_node = list1.as_ref();
        let mut current_index = 0;
        let mut answer_stack: Vec<i32> = vec![];

        while current_list1_node.is_some() {
            if a == current_index {
                let mut current_list2_node = list2.as_ref();
                while current_list2_node.is_some() {
                    answer_stack.push(current_list2_node.unwrap().val);
                    current_list2_node = current_list2_node.unwrap().next.as_ref();
                }
            }

            if current_index < a || b < current_index {
                answer_stack.push(current_list1_node.unwrap().val);
            }

            current_index += 1;
            current_list1_node = current_list1_node.unwrap().next.as_ref();
        }

        let mut answer = None;
        while let Some(val) = answer_stack.pop() {
            answer = Some(Box::new(ListNode { val, next: answer }));
        }

        answer
    }

    // https://leetcode.com/problems/merge-in-between-linked-lists/solutions/989246/rust-linear-time-and-no-extra-space-o-n-m-time-and-o-1-space/
    pub fn merge_in_between2(
        mut list1: Option<Box<ListNode>>,
        a: i32,
        b: i32,
        mut list2: Option<Box<ListNode>>,
    ) -> Option<Box<ListNode>> {
        let mut head = list1.unwrap();
        let mut current = head.as_mut();

        for _ in 0..(a - 1) {
            current = current.next.as_mut().unwrap();
        }

        mem::swap(&mut current.next, &mut list2);

        while current.next.is_some() {
            current = current.next.as_mut().unwrap();
        }

        for _ in 0..(b - a + 1) {
            list2 = list2.unwrap().next;
        }

        mem::swap(&mut current.next, &mut list2);

        Some(head)
    }
}

#[test]
fn test() {
    let list1 = ListNode {
        val: 0,
        next: Some(Box::new(ListNode {
            val: 1,
            next: Some(Box::new(ListNode {
                val: 2,
                next: Some(Box::new(ListNode {
                    val: 3,
                    next: Some(Box::new(ListNode {
                        val: 4,
                        next: Some(Box::new(ListNode { val: 5, next: None })),
                    })),
                })),
            })),
        })),
    };

    let list2 = ListNode {
        val: 1000000,
        next: Some(Box::new(ListNode {
            val: 1000001,
            next: Some(Box::new(ListNode {
                val: 1000002,
                next: None,
            })),
        })),
    };

    let answer = Solution::merge_in_between(
        Some(Box::new(list1.clone())),
        3,
        4,
        Some(Box::new(list2.clone())),
    );
    println!("{:?}", answer);

    let answer = Solution::merge_in_between2(Some(Box::new(list1)), 3, 4, Some(Box::new(list2)));
    println!("{:?}", answer);
}
