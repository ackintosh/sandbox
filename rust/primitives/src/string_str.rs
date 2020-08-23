/////////////////////////////////////////////////////////
// str
/////////////////////////////////////////////////////////
#[test]
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

/////////////////////////////////////////////////////////
// String
/////////////////////////////////////////////////////////
#[test]
fn remove_all_whitespace() {
    // 文字列からスペースを削除する
    let mut s = "a b c".to_owned();
    s.retain(|c| !c.is_whitespace());

    assert_eq!(s, "abc".to_owned());
}

#[test]
fn string_pos() {
    let mut s = "aaabbbccc".to_owned();

    // bbb以降を切り落とす
    if let Some(pos) = s.find("bbb") {
        s.replace_range(pos.., "");
    }

    assert_eq!(s, "aaa".to_owned());
}
