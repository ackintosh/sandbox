// https://leetcode.com/problems/encode-and-decode-tinyurl/

use std::ops::Index;

struct Codec {
    url: Vec<String>,
}

/**
 * `&self` means the method takes an immutable reference.
 * If you need a mutable reference, change it to `&mut self` instead.
 */
impl Codec {
    fn new() -> Self {
        Self { url: vec![] }
    }

    // Encodes a URL to a shortened URL.
    fn encode(&mut self, longURL: String) -> String {
        let index = self.url.len();
        self.url.push(longURL);

        format!("http://tinyurl.com/{}", index)
    }

    // Decodes a shortened URL to its original URL.
    fn decode(&self, shortURL: String) -> String {
        let index_string = shortURL.replace("http://tinyurl.com/", "");
        let index: usize = index_string.parse().unwrap();
        self.url.index(index).clone()
    }
}

/**
 * Your Codec object will be instantiated and called as such:
 * let obj = Codec::new();
 * let s: String = obj.encode(strs);
 * let ans: VecVec<String> = obj.decode(s);
 */

#[test]
fn test() {
    let mut codec = Codec::new();
    let url = "https://leetcode.com/problems/design-tinyurl".to_owned();
    let s = codec.encode(url.clone());

    assert_eq!(s, "http://tinyurl.com/0".to_owned());
    assert_eq!(codec.decode(s), url);
}
