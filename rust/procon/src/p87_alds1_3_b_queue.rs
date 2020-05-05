// プロコンのためのアルゴリズムとデータ構造
// 4.3 キュー

// ラウンドロビンスケジューリングをシミュレートする

// *入力*
// n: プロセス数を表す整数
// q: クオンタムを表す整数 (ms)
// processes: プロセス情報のベクター

// *出力*
// プロセスが完了した順に、

// *制約*
// 1 <= n <= 100,000
// 1 <= q <= 1,000
// 1 <= time_i <= 50,000
// 1 <= 文字列name_iの長さ <= 10
// 1 <= time_iの合計 <= 1,000,000

type Input = (
    String, // プロセス名
    u32, // 必要な処理時間 (ms)
);

type Output = (
    String, // プロセス名
    u32, // 終了時刻
);

fn round_robin_scheduling(n: u32, q: u32, processes: Vec<Input>) -> Vec<Output> {

    vec![("xx".to_owned(), 1)]
}

#[derive(Debug)]
struct Queue<T: Default + Copy> {
    size: usize,
    head: usize,
    tail: usize,
    haystack: [Option<T>; 32],
}

impl<T: Default + Copy> Queue<T> {
    fn new(size: usize) -> Self {
        if size > 32 {
            panic!("いったんhaysetackの上限を32にしている")
        }

        Self {
            size,
            head: 0,
            tail: 0,
            haystack: Default::default(),
        }
    }

    fn is_empty(&self) -> bool {
        self.head == self.tail
            && self.haystack[self.tail].is_none()
    }

    fn is_full(&self) -> bool {
        self.haystack[self.tail].is_some()
    }

    fn enqueue(&mut self, v: T) {
        // オーバーフロー
        if self.is_full() {
            panic!("キューがいっぱい");
        }

        self.haystack[self.tail] = Some(v);
        self.tail = self.next_index(self.tail);
    }

    fn dequeue(&mut self) -> Result<T, String> {
        // アンダーフロー
        if self.is_empty() {
            return Err("キューが空".to_owned());
        }

        let v = self.haystack[self.head];
        self.haystack[self.head] = None;
        self.head = self.next_index(self.head);
        Ok(v.expect("should have a value"))
    }

    fn next_index(&self, i: usize) -> usize {
        (i + 1) % self.size
    }
}

#[test]
fn test() {
    assert_eq!(
        round_robin_scheduling(
            5,
            100,
            vec![
                ("p1".to_owned(), 150),
                ("p2".to_owned(), 80),
                ("p3".to_owned(), 200),
                ("p4".to_owned(), 350),
                ("p5".to_owned(), 20),
            ]
        ),
        vec![
            ("p2".to_owned(), 180),
            ("p5".to_owned(), 400),
            ("p1".to_owned(), 450),
            ("p3".to_owned(), 550),
            ("p4".to_owned(), 800),
        ]
    );
}

#[test]
fn test_queue() {
    let mut q: Queue<u32> = Queue::new(5);
    assert!(q.is_empty());

    q.enqueue(10);
    assert!(!q.is_empty());

    assert_eq!(
        q.dequeue(),
        Ok(10),
    );
    assert!(q.is_empty());

    for i in 0..5 {
        q.enqueue(i);
    }
    assert!(!q.is_empty());
    assert!(q.is_full());

}
