// https://leetcode.com/problems/count-sorted-vowel-strings/

struct Solution;

impl Solution {
    pub fn count_vowel_strings(n: i32) -> i32 {
        let mut c = 1;

        let mut ar = vec![5];

        while c < n {
            let mut new_ar = vec![];
            for a in ar {
                for aa in 1..=a {
                    new_ar.push(aa);
                }
            }

            ar = new_ar;
            c += 1;
        }

        ar.iter().sum()
    }
}

#[test]
fn test() {
    assert_eq!(5, Solution::count_vowel_strings(1));
    assert_eq!(15, Solution::count_vowel_strings(2));
    assert_eq!(66045, Solution::count_vowel_strings(33));
}
