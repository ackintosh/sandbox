use parking_lot::RwLock;

#[test]
fn scope() {
    let lock = RwLock::new(vec![]);

    {
        let reader = lock.read();
        println!("{:?}", *reader);
    }

    let len = lock.read().len();

    let mut writer = lock.write();
    writer.push(1);

    println!("len: {}", len);
}

#[test]
fn read() {
    let lock = RwLock::new(vec![1, 2, 3]);

    let read = lock.read();
    assert_eq!(3, read.len());

    // 変更しようとするとコンパイルエラー
    //
    // let mut read = lock.read();
    // read.push(1);
    //
    // 27 |     read.push(1);
    //    |     ^^^^ cannot borrow as mutable
    //    |
    //    = help: trait `DerefMut` is required to modify through a dereference, but it is not implemented for `parking_lot::lock_api::RwLockReadGuard<'_, parking_lot::RawRwLock, Vec<i32>>`
}

#[test]
fn write() {
    let lock = RwLock::new(vec![1]);

    let mut write = lock.write();
    assert_eq!(1, write.len());

    write.push(1);
    assert_eq!(2, write.len());
}

mod local_network {
    use parking_lot::RwLock;
    use std::sync::Arc;
    use tokio::time::Duration;

    struct LocalNetwork {
        elements: RwLock<Vec<i32>>,
    }

    impl LocalNetwork {
        fn new() -> Self {
            Self {
                elements: RwLock::new(vec![]),
            }
        }

        async fn add(&self, task_index: i32) {
            {
                let reader = self.elements.read();
                println!("[task: {}] len: {}", task_index, reader.len());
            }

            let len = self.elements.read().len();
            println!("[task: {}] len2: {}", task_index, len);

            // task_index: 0 だけsleepする
            //   -> task 1 が処理される
            if task_index == 0 {
                tokio::time::sleep(Duration::from_millis(100)).await;
            }

            let len = self.elements.read().len();
            println!("[task: {}] len3: {}", task_index, len);

            self.elements.write().push(1);

            let len = self.elements.read().len();
            println!("[task: {}] len4: {}", task_index, len);
        }
    }

    #[test]
    fn local_network() {
        let nw = Arc::new(LocalNetwork::new());

        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        rt.block_on(async move {
            let mut handles = vec![];
            for i in 0..2 {
                let nw_cloned = nw.clone();
                let h = tokio::task::spawn(async move {
                    nw_cloned.add(i).await;
                });
                handles.push(h);
            }

            for h in handles {
                h.await.unwrap();
            }
        });
    }
}
