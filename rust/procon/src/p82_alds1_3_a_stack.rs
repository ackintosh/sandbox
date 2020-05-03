// プロコンのためのアルゴリズムとデータ構造
// 4.2 スタック

use std::fmt::Debug;
use std::str::FromStr;

// *出力*
// 計算結果
type Output = i32;

// *入力*
// 逆ポーランド記法の数式
// *制約*
// 2 <= 式に含まれるオペランドの数 <= 100
// 1 <= 式に含まれる演算子の数 <= 99
fn stack(sequence: &str) -> Output {
    let mut stack: Stack<i32> = Stack::new();

    for term in sequence.split(" ").collect::<Vec<&str>>().iter() {
        println!("term: {:?}", term);

        match i32::from_str(term) {
            Ok(num) => {
                stack.push(num);
            }
            Err(e) => {
                println!("from_str: {:?}", term);

                match term {
                    &"+" => {
                        let right = stack.pop().expect("should have nums");
                        let left = stack.pop().expect("should have nums");
                        stack.push(left + right);
                    }
                    &"-" => {
                        let right = stack.pop().expect("should have nums");
                        let left = stack.pop().expect("should have nums");
                        stack.push(left - right);
                    }
                    &"*" => {
                        let right = stack.pop().expect("should have nums");
                        let left = stack.pop().expect("should have nums");
                        stack.push(left * right);
                    }
                    others => panic!("不明な演算子: {}", others)
                }
            }
        }
    }

    let result = stack.pop().expect("should have a result");
    if !stack.is_empty() {
        panic!("スタックに項が残っています. stack: {:?}", stack);
    }

    result
}

// 練習のために、vectorは使わずに配列で実装する
#[derive(Debug)]
struct Stack<T: Default + Copy + Debug> {
    // 制約条件から、オペランドの数が100以下なので配列サイズは100にしたいけど、
    // 現状、Debugトレイトが、長さ32までの配列しかサポートしていないので、32にしておく
    // https://doc.rust-lang.org/std/primitive.array.html
    haystack: [T; 32],
    top: Option<usize>,
}

impl<T: Default + Copy + Debug> Stack<T> {
    fn new() -> Self {
        Self {
            haystack: Default::default(),
            top: None,
        }
    }

    fn is_empty(&self) -> bool {
        self.top.is_none()
    }

    fn is_full(&self) -> bool {
        if self.top.is_none() {
            return false;
        }

        self.top.unwrap() == 31
    }

    fn push(&mut self, v: T) {
        println!("push({:?}) -->", v);
        print!("    elements: {:?} \n    top: {:?} \n", self.haystack, self.top);

        if self.is_full() {
            panic!("スタックがいっぱいです");
        }

        if self.top.is_none() {
            self.top = Some(0);
        } else {
            self.top = Some(self.top.unwrap() + 1);
        }
        self.haystack[self.top.unwrap()] = v;

        print!("    elements: {:?} \n    top: {:?} \n", self.haystack, self.top);
        println!("<-- push({:?})", v);
    }

    fn pop(&mut self) -> Result<T, ()> {
        println!("pop() -->");
        print!("    elements: {:?} \n    top: {:?} \n", self.haystack, self.top);

        if self.top.is_none() {
            return Err(());
        }

        let top = self.top.unwrap();
        let v = self.haystack[top];
        self.haystack[top] = Default::default();

        if top == 0 {
            self.top = None;
        } else {
            self.top = Some(top - 1);
        }

        print!("    elements: {:?} \n    top: {:?} \n", self.haystack, self.top);
        println!("<-- pop()");

        Ok(v)
    }
}

#[test]
fn test() {
    assert_eq!(
        stack("1 2 + 3 4 - *"),
        -3
    )
}

#[test]
fn test_stack() {
    let mut stack: Stack<i32> = Stack::new();
    assert!(stack.is_empty());
    assert!(!stack.is_full());

    stack.push(10);
    assert!(!stack.is_empty());
    assert!(!stack.is_full());

    assert_eq!(stack.pop(), Ok(10));
    assert!(stack.is_empty());
    assert!(!stack.is_full());

    for i in 0..32 {
        stack.push(i);
    }
    assert!(!stack.is_empty());
    assert!(stack.is_full());
}
