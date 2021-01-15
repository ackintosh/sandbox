#[test]
fn test() {
    assert_eq!(tower_of_hanoi(0), 0);
    assert_eq!(tower_of_hanoi(1), 1);
    assert_eq!(tower_of_hanoi(2), 3);
    assert_eq!(tower_of_hanoi(3), 7);
    assert_eq!(tower_of_hanoi(4), 15);
    assert_eq!(tower_of_hanoi(5), 31);
    assert_eq!(tower_of_hanoi(6), 63);
}

#[allow(dead_code)]
fn tower_of_hanoi(n: u32) -> u32 {
    match n {
        0 => 0,
        other => {
            tower_of_hanoi(other - 1) + 1 + tower_of_hanoi(other - 1)
        }
    }
}
