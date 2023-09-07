// https://leetcode.com/problems/smallest-number-in-infinite-set/

struct SmallestInfiniteSet {
    // nums in descending order.
    inner: Vec<i32>,
}

/**
 * `&self` means the method takes an immutable reference
 * If you need a mutable reference, change it to `&mut self` instead.
 */
impl SmallestInfiniteSet {
    fn new() -> Self {
        let mut inner = (1..=1000).into_iter().collect::<Vec<i32>>();
        inner.reverse();
        SmallestInfiniteSet { inner }
    }

    fn pop_smallest(&mut self) -> i32 {
        self.inner.pop().unwrap()
    }

    fn add_back(&mut self, num: i32) {
        if self.inner.contains(&num) {
            return;
        }

        let mut index = 0;
        let mut found = false;
        for (i, n) in self.inner.iter().enumerate() {
            if &num > n {
                index = i;
                found = true;
                break;
            }
        }

        if found {
            self.inner.insert(index, num);
        } else {
            self.inner.push(num);
        }
    }
}

/**
 * Your SmallestInfiniteSet object will be instantiated and called as such:
 * let obj = SmallestInfiniteSet::new();
 * let ret_1: i32 = obj.pop_smallest();
 * obj.add_back(num);
 */
#[test]
fn test() {
    let mut set = SmallestInfiniteSet::new();
    set.add_back(2);
    assert_eq!(1, set.pop_smallest());
    assert_eq!(2, set.pop_smallest());
    assert_eq!(3, set.pop_smallest());
    set.add_back(1);
    assert_eq!(1, set.pop_smallest());
    assert_eq!(4, set.pop_smallest());
    assert_eq!(5, set.pop_smallest());
}
