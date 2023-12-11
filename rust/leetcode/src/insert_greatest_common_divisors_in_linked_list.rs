// https://leetcode.com/problems/insert-greatest-common-divisors-in-linked-list/

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
    // ref: https://leetcode.com/problems/insert-greatest-common-divisors-in-linked-list/solutions/4128719/clean-rust-solution/
    pub fn insert_greatest_common_divisors(
        mut head: Option<Box<ListNode>>,
    ) -> Option<Box<ListNode>> {
        if head.is_none() {
            return head;
        }

        let mut answer = head;
        let mut answer_ref = answer.as_mut();

        while let Some(current) = answer_ref {
            if current.next.is_some() {
                let val = current.val;
                let gcd = gcd(val, current.next.as_ref().unwrap().val);
                let gcd_node = Some(Box::new(ListNode {
                    val: gcd,
                    next: current.next.take(),
                }));
                current.next = gcd_node;

                answer_ref = current.next.as_mut().unwrap().next.as_mut();
            } else {
                break;
            }
        }

        answer
    }
}

fn gcd(mut n: i32, mut m: i32) -> i32 {
    assert!(n != 0 && m != 0);
    while m != 0 {
        if m < n {
            std::mem::swap(&mut m, &mut n);
        }
        m %= n;
    }
    n
}

#[test]
fn test() {
    let head = Some(Box::new(ListNode {
        val: 18,
        next: Some(Box::new(ListNode {
            val: 6,
            next: Some(Box::new(ListNode {
                val: 10,
                next: Some(Box::new(ListNode { val: 3, next: None })),
            })),
        })),
    }));

    let answer = Solution::insert_greatest_common_divisors(head);
    println!("{answer:?}");
}
