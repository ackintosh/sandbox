// https://leetcode.com/problems/design-parking-system/

struct ParkingSystem {
    big: i32,
    medium: i32,
    small: i32,
}

/**
 * `&self` means the method takes an immutable reference.
 * If you need a mutable reference, change it to `&mut self` instead.
 */
impl ParkingSystem {
    fn new(big: i32, medium: i32, small: i32) -> Self {
        Self { big, medium, small }
    }

    fn add_car(&mut self, car_type: i32) -> bool {
        match car_type {
            1 => {
                if self.big > 0 {
                    self.big -= 1;
                    true
                } else {
                    false
                }
            }
            2 => {
                if self.medium > 0 {
                    self.medium -= 1;
                    true
                } else {
                    false
                }
            }
            3 => {
                if self.small > 0 {
                    self.small -= 1;
                    true
                } else {
                    false
                }
            }
            _ => unreachable!(),
        }
    }
}

/**
 * Your ParkingSystem object will be instantiated and called as such:
 * let obj = ParkingSystem::new(big, medium, small);
 * let ret_1: bool = obj.add_car(carType);
 */

#[test]
fn test() {
    let mut parking_system = ParkingSystem::new(1, 1, 0);
    assert!(parking_system.add_car(1));
    assert!(parking_system.add_car(2));
    assert!(!parking_system.add_car(3));
    assert!(!parking_system.add_car(1));
}
