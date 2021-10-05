struct Node<T> {
    value: T,
    prev: Option<Node<T>>,
    next: Option<Node<T>>,
}

struct LinkedList<T> {
    length: u64,
    start: Option<Node<T>>,
}

impl<T> LinkedList<T> {
    fn new() -> Self<T> {
        Self {
            length: 0,
            start: None,
        }
    }

    fn add(mut self, value: T) {
        let n = Node {
            value,
            prev: None,
            next: None,
        };
        self.length += 1;
    }
}

#[test]
fn test() {
    let linked_list: LinkedList<u64> = LinkedList::new();
}
