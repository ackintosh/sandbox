// https://leetcode.com/problems/merge-nodes-in-between-zeros/

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
    pub fn merge_nodes(head: Option<Box<ListNode>>) -> Option<Box<ListNode>> {
        let mut result_head = Box::new(ListNode::new(0));
        let mut result_pointer = &mut result_head;
        let mut sum = 0;

        let mut current_node = head.as_ref();

        while let Some(node) = current_node {
            if node.val == 0 && sum > 0 {
                result_pointer.next = Some(Box::new(ListNode::new(sum)));

                if let Some(ref mut next) = result_pointer.next {
                    result_pointer = next;
                }

                sum = 0;
            } else {
                sum += node.val;
            }

            current_node = node.next.as_ref();
        }

        result_head.next
    }
}

#[test]
fn test() {
    let head = {
        let mut n = ListNode::new(0);
        n.next = Some({
            let mut n = ListNode::new(3);
            n.next = Some({
                let mut n = ListNode::new(1);
                n.next = Some({
                    let mut n = ListNode::new(0);
                    n.next = Some({
                        let mut n = ListNode::new(4);
                        n.next = Some({
                            let mut n = ListNode::new(5);
                            n.next = Some({
                                let mut n = ListNode::new(2);
                                n.next = Some(Box::new(ListNode::new(0)));
                                Box::new(n)
                            });
                            Box::new(n)
                        });
                        Box::new(n)
                    });
                    Box::new(n)
                });
                Box::new(n)
            });
            Box::new(n)
        });
        Box::new(n)
    };

    let out = Solution::merge_nodes(Some(head));
    assert_eq!(4, out.clone().unwrap().val);
    assert_eq!(11, out.clone().unwrap().next.unwrap().val);
    assert_eq!(None, out.unwrap().next.unwrap().next);
}
