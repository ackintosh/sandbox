// https://leetcode.com/problems/find-the-prefix-common-array-of-two-arrays/

// use std::collections::HashMap;

struct Solution;

impl Solution {
    // 下記URLを参考にHashMapを使うパターンを実装してみたが、LeetCodeの結果ではこちらの方が速度が遅かった（9ms と 3ms）
    // https://leetcode.com/problems/find-the-prefix-common-array-of-two-arrays/solutions/3466676/frequency-array-solution-explained-o-n-time-and-space-c/
    // pub fn find_the_prefix_common_array(a: Vec<i32>, b: Vec<i32>) -> Vec<i32> {
    //     let mut answer = vec![];
    //     let mut count = 0;
    //     let mut map = HashMap::new();
    //
    //     for i in 0..a.len() {
    //         let e = map.entry(a[i]).or_insert(0);
    //         *e += 1;
    //         if *e == 2 {
    //             count += 1;
    //         }
    //
    //         let e = map.entry(b[i]).or_insert(0);
    //         *e += 1;
    //         if *e == 2 {
    //             count += 1;
    //         }
    //
    //         answer.push(count);
    //     }
    //
    //     answer
    // }

    pub fn find_the_prefix_common_array(a: Vec<i32>, b: Vec<i32>) -> Vec<i32> {
        let mut answer = vec![];
        let mut count = 0;

        for i in 0..a.len() {
            if a[i] == b[i] {
                count += 1;
            } else {
                for bi in 0..i {
                    if a[i] == b[bi] {
                        count += 1;
                        break;
                    }
                }

                for ai in 0..i {
                    if b[i] == a[ai] {
                        count += 1;
                        break;
                    }
                }
            }

            answer.push(count);
        }

        answer
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![0, 2, 3, 4],
        Solution::find_the_prefix_common_array(vec![1, 3, 2, 4], vec![3, 1, 2, 4])
    );
    assert_eq!(
        vec![0, 1, 3],
        Solution::find_the_prefix_common_array(vec![2, 3, 1], vec![3, 1, 2])
    );
}
