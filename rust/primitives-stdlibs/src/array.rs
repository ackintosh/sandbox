#[test]
fn array() {
    {
        let array = [99_i32]; // [i32; 1]
        println!("{:?}", array);
    }

    // 宣言時に初期値をセットする
    {
        let array = [3; 3]; // [i32; 3]
        println!("{:?}", array);
        println!("{:?}", [99; 3]);
    }
}

#[test]
fn multidimensional_array() {
    {
        let array = [[1; 3]; 5]; // [[i32; 3]; 5] という型の配列
        println!("{:?}", array);
    }
}
