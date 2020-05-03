fn str() {
    let str = "1 2 + 3 4 - *";

    // Split構造体が返る
    // https://doc.rust-lang.org/std/str/struct.Split.html
    let split = str.split(" ");
    println!("{:?}", split);

    // Split構造体がIteratorトレイトを実装している
    let strs: Vec<&str> = str.split(" ").collect();
    println!("{:?}", strs);

    for s in str.split(" ").collect::<Vec<&str>>() {
        print!("{} ", s)
    }
    print!("\n");
}

#[test]
fn test() {
    str();
}