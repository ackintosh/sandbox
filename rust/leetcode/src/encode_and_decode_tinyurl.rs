// https://leetcode.com/problems/encode-and-decode-tinyurl/

use std::cell::RefCell;
use std::ops::Index;

struct Codec {
    urls: RefCell<Vec<String>>,
}

/**
 * `&self` means the method takes an immutable reference.
 * If you need a mutable reference, change it to `&mut self` instead.
 */
#[allow(non_snake_case)]
impl Codec {
    fn new() -> Self {
        Self {
            urls: RefCell::new(vec![]),
        }
    }

    // Encodes a URL to a shortened URL.
    fn encode(&self, longURL: String) -> String {
        let mut urls = self.urls.borrow_mut();
        let index = urls.len();
        urls.push(longURL);

        format!("http://tinyurl.com/{}", index)
    }

    // Decodes a shortened URL to its original URL.
    fn decode(&self, shortURL: String) -> String {
        let index_string = shortURL.replace("http://tinyurl.com/", "");
        let index: usize = index_string.parse().unwrap();
        self.urls.borrow().index(index).clone()
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
    let codec = Codec::new();
    let url = "https://leetcode.com/problems/design-tinyurl".to_owned();
    let s = codec.encode(url.clone());

    assert_eq!(s, "http://tinyurl.com/0".to_owned());
    assert_eq!(codec.decode(s), url);
}
