// 任意の型TとSを引数にとって、それらをタプルにまとめて戻り値にする
fn make_tuple<T, S>(t: T, s: S) -> (T, S) {
    (t, s)
}

// 数値、文字列、ベクタ型をそれぞれ引数にしている
// このときコンパイラは、要求される型の組み合わせの分だけ make_tuple() を用意して、呼出が高速に行われるようにしている
//   ->  単相化 (monomorphization) (ゼロコスト抽象化)
#[test]
fn test() {
    let t1 = make_tuple(1, 2);
    println!("{:?}", t1);

    let t2 = make_tuple("Hello", "World");
    println!("{:?}", t2);

    let t3 = make_tuple(vec![1, 2, 3], vec![4, 5]);
    println!("{:?}", t3);

    let t4 = make_tuple(3, "years old");
    println!("{:?}", t4);
}
