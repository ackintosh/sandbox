// https://leetcode.com/problems/design-a-stack-with-increment-operation/

struct CustomStack {
    inner: Vec<i32>,
    max_size: usize,
}

/**
 * `&self` means the method takes an immutable reference.
 * If you need a mutable reference, change it to `&mut self` instead.
 */
#[allow(non_snake_case)]
impl CustomStack {
    fn new(maxSize: i32) -> Self {
        CustomStack {
            inner: Vec::with_capacity(maxSize as usize),
            max_size: maxSize as usize,
        }
    }

    fn push(&mut self, x: i32) {
        if self.inner.len() < self.max_size {
            self.inner.push(x);
        }
    }

    fn pop(&mut self) -> i32 {
        if let Some(x) = self.inner.pop() {
            return x;
        }

        -1
    }

    fn increment(&mut self, k: i32, val: i32) {
        for i in 0..k as usize {
            if let Some(x) = self.inner.get_mut(i) {
                *x += val;
            } else {
                return;
            }
        }
    }
}

#[test]
fn test() {
    let mut stack = CustomStack::new(3);
    stack.push(1);
    stack.push(2);
    assert_eq!(2, stack.pop());
    stack.push(2);
    stack.push(3);
    stack.push(4);
    stack.increment(5, 100);
    stack.increment(2, 100);
    assert_eq!(103, stack.pop());
    assert_eq!(202, stack.pop());
    assert_eq!(201, stack.pop());
    assert_eq!(-1, stack.pop());
}
