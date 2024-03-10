// types - Converting number primitives (i32, f64, etc) to byte representations - Stack Overflow
// https://stackoverflow.com/questions/29445026/converting-number-primitives-i32-f64-etc-to-byte-representations)
#[test]
fn convert_number_to_bytes() {
    // from i32 to bytes (Big Endian)
    let b = 10_i32.to_be_bytes();
    println!("{:?}", 10_i32.to_be_bytes()); // [0, 0, 0, 10]
    println!("{:?}", 256_i32.to_be_bytes()); // [0, 0, 1, 0]

    // from i32 to bytes (Little Endian)
    println!("{:?}", 10_i32.to_le_bytes()); // [10, 0, 0, 0]
    println!("{:?}", 256_i32.to_le_bytes()); // [0, 1, 0, 0]
}

#[test]
fn copy_bytes() {
    let four_bytes = [1_u8; 4];
    // [1, 1, 1, 1]
    println!("{:?}", four_bytes);

    let mut thirty_two_bytes = [0; 32];
    // [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    println!("{:?}", thirty_two_bytes);

    thirty_two_bytes[0..=3].copy_from_slice(&four_bytes);
    // [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    println!("{:?}", thirty_two_bytes);
}
