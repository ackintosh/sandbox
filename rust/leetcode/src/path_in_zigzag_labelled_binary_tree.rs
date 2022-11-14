// https://leetcode.com/problems/path-in-zigzag-labelled-binary-tree/

// 解説
// https://leetcode.com/problems/path-in-zigzag-labelled-binary-tree/discuss/324011/Python-O(logn)-time-and-space-with-readable-code-and-step-by-step-explanation

struct Solution;

impl Solution {
    pub fn path_in_zig_zag_tree(label: i32) -> Vec<i32> {
        let mut current_label = label;
        let mut answer = vec![];
        let mut node_count = 1;
        let mut level = 1_i32;

        // Determine level of the label
        while current_label > node_count {
            level += 1;
            node_count = 2_i32.checked_pow(level as u32).unwrap() - 1;
        }

        // Iterate from the target level to the root
        while level > 0 {
            answer.push(current_label);
            let level_max = (2_i32.checked_pow(level as u32)).unwrap() - 1;
            let level_min = (2_i32.checked_pow(level as u32 - 1)).unwrap();

            // https://leetcode.com/problems/path-in-zigzag-labelled-binary-tree/discuss/324011/Python-O(logn)-time-and-space-with-readable-code-and-step-by-step-explanation/817218
            current_label =
                (((level_max - level_min) - (current_label - level_min)) + level_min) / 2;

            level -= 1;
        }

        answer.reverse();
        answer
    }
}

#[test]
fn test() {
    assert_eq!(vec![1, 3, 4, 14], Solution::path_in_zig_zag_tree(14));
}
