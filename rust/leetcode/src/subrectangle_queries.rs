// https://leetcode.com/problems/subrectangle-queries/

use std::convert::TryFrom;

struct SubrectangleQueries {
    rectangle: Vec<Vec<i32>>,
}

/**
 * `&self` means the method takes an immutable reference.
 * If you need a mutable reference, change it to `&mut self` instead.
 */
impl SubrectangleQueries {
    fn new(rectangle: Vec<Vec<i32>>) -> Self {
        Self { rectangle }
    }

    fn update_subrectangle(&mut self, row1: i32, col1: i32, row2: i32, col2: i32, new_value: i32) {
        for row in row1..=row2 {
            for col in col1..=col2 {
                self.rectangle[usize::try_from(row).unwrap()][usize::try_from(col).unwrap()] =
                    new_value;
            }
        }
    }

    fn get_value(&self, row: i32, col: i32) -> i32 {
        self.rectangle[usize::try_from(row).unwrap()][usize::try_from(col).unwrap()]
    }
}

/**
 * Your SubrectangleQueries object will be instantiated and called as such:
 * let obj = SubrectangleQueries::new(rectangle);
 * obj.update_subrectangle(row1, col1, row2, col2, newValue);
 * let ret_2: i32 = obj.get_value(row, col);
 */
#[test]
fn test() {
    let mut subrectangle = SubrectangleQueries::new(vec![
        vec![1, 2, 1],
        vec![4, 3, 4],
        vec![3, 2, 1],
        vec![1, 1, 1],
    ]);
    assert_eq!(subrectangle.get_value(0, 2), 1);

    subrectangle.update_subrectangle(0, 0, 3, 2, 5);
    assert_eq!(subrectangle.get_value(0, 2), 5);
    assert_eq!(subrectangle.get_value(3, 1), 5);

    subrectangle.update_subrectangle(3, 0, 3, 2, 10);
    assert_eq!(subrectangle.get_value(3, 1), 10);
    assert_eq!(subrectangle.get_value(0, 2), 5);
}
