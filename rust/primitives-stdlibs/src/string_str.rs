/////////////////////////////////////////////////////////
// str
/////////////////////////////////////////////////////////
mod str {
    #[cfg(test)]
    use regex::Regex;

    #[test]
    fn str() {
        let str = "1 2 + 3 4 - *";

        // Split構造体が返る
        // https://doc.rust-lang.org/std/str/struct.Split.html
        let split = str.split(' ');
        println!("{:?}", split);

        // Split構造体がIteratorトレイトを実装している
        let strs: Vec<&str> = str.split(' ').collect();
        println!("{:?}", strs);

        for s in str.split(' ').collect::<Vec<&str>>() {
            print!("{} ", s)
        }
        println!();
    }

    /////////////////////////////////////////////////////////
    // 分割
    /////////////////////////////////////////////////////////
    #[test]
    fn split() {
        let str = "abc";
        for s in str.split("") {
            println!("split: {}", s);
            // ※空文字で分割した場合、前後に空文字が入る
            // split:
            // split: a
            // split: b
            // split: c
            // split:
        }

        for s in str.split("").skip_while(|&s| s.is_empty()) {
            println!("Str::split() & Iterator::skip_while(): {}", s);
            // ※skip_whileだと最後の空文字が残ってしまう
            // Str::split() & Iterator::skip_while(): a
            // Str::split() & Iterator::skip_while(): b
            // Str::split() & Iterator::skip_while(): c
            // Str::split() & Iterator::skip_while():
        }

        for s in str.split("").filter(|&s| !s.is_empty()) {
            println!("Str::split() & Iterator::filter(): {}", s);
            // ※前後の空文字が除かれて、3文字だけが出力される
            // Str::split() & Iterator::filter(): a
            // Str::split() & Iterator::filter(): b
            // Str::split() & Iterator::filter(): c
        }
    }

    // How can I split a string (String or &str) on more than one delimiter? - Stack Overflow
    // https://stackoverflow.com/questions/29240157/how-can-i-split-a-string-string-or-str-on-more-than-one-delimiter
    #[test]
    fn split_with_regex() {
        // r"" はraw string literal
        // Rust: Raw string literals - rahul thakoor
        // https://rahul-thakoor.github.io/rust-raw-string-literals/
        let regex = Regex::new(r",|\.").unwrap();
        let str = "aaa,bbb.ccc";

        for s in regex.split(str) {
            println!("{}", s);
        }
        // aaa
        // bbb
        // ccc

        //////////////////////////////////
        // 配列から正規表現を作るパターン
        //////////////////////////////////
        let keywords: [&str; 3] = [",", ".", "|"];
        let reg_str = keywords
            .iter()
            .map(|&k| {
                if [".", "|"].contains(&k) {
                    // エスケープが必要な文字
                    format!("\\{}", k)
                } else {
                    String::from(k)
                }
            })
            .collect::<Vec<_>>()
            .join("|");
        let regex = Regex::new(&reg_str).unwrap();
        for s in regex.split("aaa,bbb.ccc|ddd") {
            println!("{}", s);
        }
        // aaa
        // bbb
        // ccc
        // ddd
    }

    #[test]
    fn iter() {
        let str = "abc";
        for char in str.chars() {
            println!("char: {}", char);
        }
    }

    #[test]
    fn index() {
        let str = "abc";

        // println!("{:?}", str[0]);
        // string indices are ranges of `usize`

        let i = 0;
        assert_eq!(&str[i..=i], "a");
    }
}

/////////////////////////////////////////////////////////
// String
/////////////////////////////////////////////////////////
mod string {
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

    #[test]
    fn index() {
        let string = "abc".to_owned();

        // 新しくCharsが作られる
        let mut chars = string.chars();
        // nth() は要素を消費する
        assert_eq!(chars.nth(0), Some('a'));
        assert_eq!(chars.nth(0), Some('b'));
        assert_eq!(chars.nth(0), Some('c'));
        assert_eq!(chars.nth(0), None);

        // stringは変化しない
        assert_eq!(string, "abc".to_owned());

        // &Stringにレンジでアクセスできる
        assert_eq!(&string[0..=0], "a");
        assert_eq!(&string[1..=1], "b");
        assert_eq!(&string[2..=2], "c");
        // 範囲外にアクセスするとpanic
        // assert_eq!(&string[3..=3], "c");
        // byte index 4 is out of bounds of `abc`
    }

    #[test]
    fn iter() {
        let string = "abc".to_owned();
        for char in string.chars() {
            println!("char: {}", char);
        }

        let mut chars = string.chars();
        assert_eq!(chars.next(), Some('a'));
        assert_eq!(chars.next(), Some('b'));
        assert_eq!(chars.next(), Some('c'));
        assert_eq!(chars.next(), None);
    }
}
