use primitives_proc_macro::Builder;

#[derive(Builder)]
pub struct Command {
    executable: String,
    args: Vec<String>,
    env: Vec<String>,
    current_dir: String,
}

#[test]
fn main() {
    let builder = Command::builder();

    let _ = builder;
}
