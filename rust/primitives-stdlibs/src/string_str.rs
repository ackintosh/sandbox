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

    // unstable
    // #[test]
    // fn rsplit_once() {
    //     let str = "abc";
    //     let s = str.rsplit_once("c").unwrap();
    // }

    #[test]
    fn rsplitn() {
        let str = "abc";

        // 通常の分割
        assert_eq!(str.rsplitn(2, 'b').collect::<Vec<&str>>(), vec!["c", "a"]);
        assert_eq!(str.rsplitn(2, 'a').collect::<Vec<&str>>(), vec!["bc", ""]);

        // 該当する文字列が無い場合
        assert_eq!(str.rsplitn(2, 'x').collect::<Vec<&str>>(), vec!["abc"]);

        // 完全一致している場合
        assert_eq!(str.rsplitn(2, "abc").collect::<Vec<&str>>(), vec!["", ""]);
        assert_eq!(str.rsplitn(4, "abc").collect::<Vec<&str>>(), vec!["", ""]);
    }

    // How can I split a string (String or &str) on more than one delimiter? - Stack Overflow
    // https://stackoverflow.com/questions/29240157/how-can-i-split-a-string-string-or-str-on-more-than-one-delimiter
    #[test]
    fn split_with_regex() {
        // r";" はraw string literal
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

    // 文字列から、インデックスを指定して文字を取る
    #[test]
    fn index() {
        let str = "abc";

        // println!("{:?}", str[0]);
        // string indices are ranges of `usize`

        let i = 0;
        assert_eq!(&str[i..=i], "a");
    }

    // 文字列から、ユニークな文字のvectorを作る
    // 参考
    // https://qiita.com/yagince/items/73184237964e9dbb8b3d#comment-24b9ff48e7aba10e736b
    #[test]
    fn uniq() {
        let str = "abcdabcdefg";

        // 1文字ごとのvectorを作る
        let mut strs: Vec<&str> = str.split("").filter(|&s| !s.is_empty()).collect();
        assert_eq!(
            strs,
            ["a", "b", "c", "d", "a", "b", "c", "d", "e", "f", "g"]
        );

        // 重複を取り除く(dedupを実行する)前にソートしておく
        //   -> 最悪ケースで O(n log n)を保証
        strs.sort_unstable();
        assert_eq!(
            strs,
            ["a", "a", "b", "b", "c", "c", "d", "d", "e", "f", "g"]
        );

        // vectorから重複を取り除く
        strs.dedup();
        assert_eq!(strs, ["a", "b", "c", "d", "e", "f", "g"]);
    }

    // 文字列から、特定の文字が存在する "最後のインデックス" を返す
    #[test]
    fn last_index_using_rfind() {
        let str = "abcabc";

        // strの最初の文字 "a" の "最後のインデックス" を返す
        let target = str.chars().next().unwrap();
        assert_eq!(str.rfind(target), Some(3));
    }

    #[test]
    fn reverse() {
        let str = "abc";
        let rev_string = str.chars().rev().collect::<String>();

        assert_eq!(rev_string, "cba".to_owned());
    }

    #[test]
    fn ascii() {
        let str = "abc";
        // as i8
        for c in str.chars() {
            println!("{}", c as i8);
            // 97
            // 98
            // 99
        }

        // as u32
        for c in str.chars() {
            println!("{}", c as u32);
            // 97
            // 98
            // 99
        }
    }

    #[test]
    fn comparing() {
        assert!("a" < "b");
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

    // 特定の文字列以降を切り落とす
    #[test]
    fn string_pos() {
        let mut s = "aaabbbccc".to_owned();

        // bbb以降を切り落とす
        if let Some(pos) = s.find("bbb") {
            s.replace_range(pos.., "");
        }

        assert_eq!(s, "aaa".to_owned());
    }

    // 任意の位置の文字にアクセスする
    #[test]
    #[allow(clippy::iter_nth_zero)]
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

    #[test]
    fn replace() {
        let string = "http://example.com/foo".to_owned();
        let replaced = string.replace("http://example.com/", "");
        assert_eq!(replaced, "foo".to_owned());
    }

    #[test]
    fn reverse() {
        let string = "abcd".to_owned();
        let reverse = string.chars().rev().collect::<String>();

        assert_eq!(reverse, "dcba".to_owned());
    }

    #[test]
    fn comparing() {
        assert!("a".to_string() < "b".to_string());
    }
}

mod char {
    #[test]
    fn comparing() {
        assert!('a' < 'b');
    }
}
