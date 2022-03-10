use std::collections::BinaryHeap;

// 標準ライブラリの BinaryHeap ではプライオリティの変更はサポートされていない
// https://stackoverflow.com/questions/53111721/can-i-modify-a-value-inside-a-binaryheap-that-isnt-the-top-value

#[test]
fn test() {
    let mut heap = BinaryHeap::new();
    heap.push(1);
    heap.push(2);
    heap.push(3);
    heap.push(3);

    assert_eq!(Some(3), heap.pop());
    assert_eq!(Some(3), heap.pop());
    assert_eq!(Some(2), heap.pop());
}
