// https://leetcode.com/problems/maximum-twin-sum-of-a-linked-list/

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
    pub fn pair_sum(head: Option<Box<ListNode>>) -> i32 {
        let mut stack = vec![];
        let mut cur = &head;

        while let Some(a) = cur.as_ref() {
            stack.push(a.val);
            cur = &a.next;
        }

        let mut max = 0;
        let mut cur = &head;
        for _ in 0..(stack.len() / 2) {
            let a = cur.as_ref().unwrap().val;
            let b = stack.pop().unwrap();
            max = max.max(a + b);

            cur = &cur.as_ref().unwrap().next;
        }

        max
    }
}

#[test]
fn test() {
    let list = {
        let mut list = ListNode::new(5);
        list.next = Some({
            let mut list = ListNode::new(4);
            list.next = Some({
                let mut list = ListNode::new(2);
                list.next = Some(Box::new(ListNode::new(1)));
                Box::new(list)
            });

            Box::new(list)
        });

        list
    };

    assert_eq!(6, Solution::pair_sum(Some(Box::new(list))));
}
