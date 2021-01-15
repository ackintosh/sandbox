// プロコンのためのアルゴリズムとデータ構造
// 4.3 キュー

// ラウンドロビンスケジューリングをシミュレートする

// *入力*
// n: プロセス数を表す整数
// quantum: クオンタムを表す整数 (ms)
// processes: プロセス情報のベクター

// *出力*
// プロセスが完了した順に、各プロセスの名前と終了時刻のタプルを格納したベクター

// *制約*
// 1 <= n <= 100,000
// 1 <= q <= 1,000
// 1 <= time_i <= 50,000
// 1 <= 文字列name_iの長さ <= 10
// 1 <= time_iの合計 <= 1,000,000

#[derive(Clone, Default, Debug)]
struct Input {
    name: String,         // プロセス名
    processing_time: u32, // 必要な処理時間 (ms)
}

impl Input {
    fn copy(self, processing_time: u32) -> Self {
        Self {
            processing_time,
            ..self
        }
    }
}

type Output = (
    String, // プロセス名
    u32,    // 終了時刻
);

fn round_robin_scheduling(n: usize, quantum: u32, processes: Vec<Input>) -> Vec<Output> {
    let mut queue: Queue<Input> = Queue::new(n);
    for p in processes.iter() {
        queue.enqueue(p.clone());
    }

    // 経過時間
    let mut time_elapsed = 0u32;
    // 出力
    let mut result = vec![];

    while !queue.is_empty() {
        let p = queue.dequeue().expect("should have processes");
        if p.processing_time <= quantum {
            time_elapsed += p.processing_time;
            result.push((p.name, time_elapsed));
        } else {
            time_elapsed += quantum;
            let remaining_processing_time = p.processing_time - quantum;
            queue.enqueue(p.copy(remaining_processing_time));
        }
    }

    println!("queue: {:?}", queue);
    println!("result: {:?}", result);

    result
}

#[derive(Debug)]
struct Queue<T: Default + Clone> {
    size: usize,
    head: usize,
    tail: usize,
    haystack: [Option<T>; 32],
}

impl<T: Default + Clone> Queue<T> {
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
        self.head == self.tail && self.haystack[self.tail].is_none()
    }

    fn is_full(&self) -> bool {
        self.head == self.tail && self.haystack[self.tail].is_some()
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

        let v = self.haystack[self.head].clone();
        self.haystack[self.head] = None;
        self.head = self.next_index(self.head);
        Ok(v.expect("should have a value"))
    }

    // 配列をリングバッファとみなして管理することで、
    // enqueue, dequeueの操作を O(1) で実装できる
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
                Input {
                    name: "p1".to_owned(),
                    processing_time: 150
                },
                Input {
                    name: "p2".to_owned(),
                    processing_time: 80
                },
                Input {
                    name: "p3".to_owned(),
                    processing_time: 200
                },
                Input {
                    name: "p4".to_owned(),
                    processing_time: 350
                },
                Input {
                    name: "p5".to_owned(),
                    processing_time: 20
                },
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

    assert_eq!(q.dequeue(), Ok(10),);
    assert!(q.is_empty());

    for i in 0..5 {
        q.enqueue(i);
    }
    assert!(!q.is_empty());
    assert!(q.is_full());
}
