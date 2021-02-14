// https://leetcode.com/problems/check-if-two-string-arrays-are-equivalent/

use dhat::{Dhat, DhatAlloc};
use std::ops::Index;

#[global_allocator]
static ALLOCATOR: DhatAlloc = DhatAlloc;

struct Solution;

impl Solution {
    pub fn array_strings_are_equal(word1: Vec<String>, word2: Vec<String>) -> bool {
        let mut w2_index = 0;
        let mut ww2_index = 0;

        for w1 in word1.iter() {
            for i in 0..w1.len() {
                let ww1 = &w1[i..=i];

                if word2.len() <= w2_index {
                    return false;
                }

                let w2 = word2.index(w2_index);
                let ww2 = &w2[ww2_index..=ww2_index];
                if ww1 != ww2 {
                    return false;
                }

                if w2.len() <= (ww2_index + 1) {
                    w2_index += 1;
                    ww2_index = 0;
                } else {
                    ww2_index += 1;
                }
            }
        }

        if word2.len() >= (w2_index + 1) {
            let w2 = &word2[w2_index];
            if w2.len() >= (ww2_index + 1) {
                return false;
            }
        }

        true
    }

    pub fn array_strings_are_equal_easy(word1: Vec<String>, word2: Vec<String>) -> bool {
        word1.concat() == word2.concat()
    }
}

#[test]
fn example1() {
    let _dhat = Dhat::start_heap_profiling();

    assert!(Solution::array_strings_are_equal(
        vec!["a".into(), "c".into()],
        vec!["a".into(), "c".into()]
    ));

    assert!(!Solution::array_strings_are_equal(
        vec!["ab".into(), "c".into()],
        vec!["a".into(), "bc".into(), "d".into()]
    ));

    assert!(!Solution::array_strings_are_equal(
        vec!["ab".into(), "c".into(), "d".into()],
        vec!["a".into(), "bc".into()]
    ));
}

#[test]
fn heap_test1() {
    let _dhat = Dhat::start_heap_profiling();

    assert!(Solution::array_strings_are_equal(
        vec!["12".into(), "34567890".into(), "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890".into()],
        vec!["12".into(), "345678901234567890123456789012345678901234567890".into(), "12345678901234567890123456789012345678901234567890".into()],
    ));
}

#[test]
fn heap_test2() {
    let _dhat = Dhat::start_heap_profiling();

    assert!(Solution::array_strings_are_equal_easy(
        vec!["12".into(), "34567890".into(), "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890".into()],
        vec!["12".into(), "345678901234567890123456789012345678901234567890".into(), "12345678901234567890123456789012345678901234567890".into()],
    ));
}
