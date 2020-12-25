struct Dropable;

impl Drop for Dropable {
    fn drop(&mut self) {
        println!("Resource will be released!");
    }
}

#[test]
fn test() {
    {
        let _ = Dropable {};
    }

    println!("スコープを外れた時点で変数はドロップされている");
}
