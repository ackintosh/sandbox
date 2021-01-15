// https://leetcode.com/problems/kids-with-the-greatest-number-of-candies/

struct Solution;

impl Solution {
    pub fn kids_with_candies(candies: Vec<i32>, extra_candies: i32) -> Vec<bool> {
        let greatest = {
            let mut c = candies.clone();
            // プリミティブのソートには sort ではなく sort_unstable を使う
            // https://rust-lang.github.io/rust-clippy/master/index.html#stable_sort_primitive
            c.sort_unstable();
            // `Copy` 型は明示的に clone() を使う代わりに dereferencing を行う
            // https://rust-lang.github.io/rust-clippy/master/index.html#clone_on_copy
            *c.last().unwrap()
        };

        let mut result = vec![];
        for c in candies {
            result.push(c + extra_candies >= greatest);
        }

        result
    }
}

#[test]
fn test() {
    assert_eq!(
        vec![true,true,true,false,true],
        Solution::kids_with_candies(vec![2,3,5,1,3], 3)
    );
}
