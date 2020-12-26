use std::sync::{Arc, Mutex};

#[test]
fn test() {
    let mut handles = vec![];

    // 所有権を共有するために Rc を使う
    // スレッド間で共有するために Rc ではなく Arc を使う
    // 排他制御のために Mutex を使う
    let data = Arc::new(Mutex::new(vec![1; 10]));

    for i in 0..10 {
        let data_ref = data.clone();
        handles.push(std::thread::spawn(move || {
            let mut data = data_ref.lock().unwrap();
            data[i] += 1;
        }));
    }

    for h in handles {
        let _ = h.join();
    }

    dbg!(data);
}
