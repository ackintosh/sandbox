#[test]
fn and() {
    println!("{}", 1 & 5); // 1
    println!("{}", 5 & 12); // 4
}

#[test]
fn or() {
    let a = 1;
    let b = 2;
    println!("{}", a | b); // 3
}

#[test]
fn xor() {
    // How do I print an integer in binary with leading zeros?
    // https://stackoverflow.com/questions/44690439/how-do-i-print-an-integer-in-binary-with-leading-zeros
    //
    //                          Width  0       8      16      24      32
    //                                 |       |       |       |       |
    // println!("{:#010b}", 1i8);  // 0b00000001
    // println!("{:#018b}", 1i16); // 0b0000000000000001
    // println!("{:#034b}", 1i32); // 0b00000000000000000000000000000001
    println!("{:#010b}", 1 ^ 2);
    println!("{:#010b}", 4 ^ 3);
}
