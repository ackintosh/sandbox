struct Droppable;

impl Drop for Droppable {
    fn drop(&mut self) {
        println!("Resource will be released!");
    }
}

#[test]
fn test() {
    {
        let _ = Droppable {};
    }

    println!("スコープを外れた時点で変数はドロップされている");
}
