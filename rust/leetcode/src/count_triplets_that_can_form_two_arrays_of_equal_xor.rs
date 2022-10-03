// https://leetcode.com/problems/count-triplets-that-can-form-two-arrays-of-equal-xor/

struct Solution;

impl Solution {
    pub fn count_triplets(arr: Vec<i32>) -> i32 {
        let mut answer = 0;

        for i in 0..(arr.len() - 1) {
            for j in (i + 1)..arr.len() {
                let prefix_xor = Self::xor(i, j - 1, &arr);
                // println!("{:?}", prefix_xor);

                for k in j..arr.len() {
                    // println!("loop: {}, {}, {}", i, j, k);

                    let xor = Self::xor(j, k, &arr);
                    // if i == 0 && j == 2 && k == 2 {
                    //     println!("prefix: {}", prefix_xor);
                    //     println!("xor: {}", xor);
                    // }
                    if prefix_xor ^ xor == 0 {
                        // println!("triplet: {}, {}, {}", i, j, k);
                        answer += 1;
                    }
                }
            }
        }

        answer
    }

    fn xor(s: usize, e: usize, arr: &Vec<i32>) -> i32 {
        let mut result = 0;

        for i in s..=e {
            result = result ^ arr.get(i).expect("should have an element");
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(4, Solution::count_triplets(vec![2, 3, 1, 6, 7]));
    assert_eq!(10, Solution::count_triplets(vec![1, 1, 1, 1, 1]));
}
