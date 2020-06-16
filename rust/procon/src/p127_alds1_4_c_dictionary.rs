// プロコンのためのアルゴリズムとデータ構造
// 5.4 ハッシュ

// insert str: 辞書に文字列 str を追加する
// find str: その時点で辞書に str が含まれるかどうかを bool 値で返す

// 制約: 与えられる文字列は 'A', 'C', 'G', 'T' の4種類の文字から構成される

use std::collections::HashMap;

struct Dictionary {
    size: u32, // ハッシュテーブルのサイズ
    table: HashMap<u32, String>,
}

impl Dictionary {
    fn new() -> Self {
        Self {
            size: 1024,
            table: HashMap::new()
        }
    }

    fn insert(&mut self, str: String) {
        let key = Self::str_to_key(&str);

        for i in 0..self.size {
            let hash = self.hash(key, i);
            if !self.table.contains_key(&hash) {
                self.table.insert(hash, str);
                return
            }
        }
    }

    fn find(&self, str: &str) -> bool {
        let str = String::from(str);
        let key = Self::str_to_key(&str);
        let hash = self.hash(key, 0);

        for i in 0..self.size {
            let hash = self.hash(key, i);
            match self.table.get(&hash) {
                Some(s) => {
                    if str == *s {
                        return true;
                    }
                },
                None => return false
            }
        }

        false
    }

    fn hash(&self, key: u32, i: u32) -> u32 {
        (self.hash1(&key) + (i * self.hash2(&key))) % self.size
    }

    fn hash1(&self, key: &u32) -> u32 {
        key % self.size
    }

    fn hash2(&self, key: &u32) -> u32 {
        1 + (key % (self.size - 1))
    }

    fn str_to_key(str: &String) -> u32 {
        str.chars().into_iter().fold(0, |sum, n| sum + Self::char_to_num(&n))
    }

    fn char_to_num(c: &char) -> u32 {
        match c {
            'A' => 1,
            'C' => 2,
            'G' => 3,
            'T' => 4,
            _ => panic!()
        }
    }
}

#[test]
fn test() {
    let mut dictionary = Dictionary::new();
    dictionary.insert("AAA".to_owned());
    dictionary.insert("AAC".to_owned());
    assert!(dictionary.find("AAA"));
    assert!(!dictionary.find("CCC"));
    dictionary.insert("CCC".to_owned());
    assert!(dictionary.find("CCC"));
}
