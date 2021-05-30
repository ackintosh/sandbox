// https://doc.rust-lang.org/core/ops/index.html

use std::ops::{Add, AddAssign};

const MAX_POSITION: usize = 100;

#[derive(Debug, PartialEq)]
pub struct Position(usize);

impl Add for Position {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        assert!(self.0 + other.0 <= MAX_POSITION);
        Self(self.0 + other.0)
    }
}

impl AddAssign for Position {
    fn add_assign(&mut self, other: Self) {
        assert!(self.0 + other.0 <= MAX_POSITION);
        self.0 += other.0;
    }
}

mod test {
    use crate::ops::Position;

    #[test]
    fn add() {
        let pos = Position(1) + Position(99);
        assert_eq!(Position(100), pos);
    }

    #[test]
    fn add_assign() {
        let mut pos = Position(1);
        pos += Position(99);
        assert_eq!(Position(100), pos);

        // 100を超える場合はpanic
        // pos += Position(1)
        // assertion failed: self.0 + other.0 <= MAX_POSITION
    }
}
