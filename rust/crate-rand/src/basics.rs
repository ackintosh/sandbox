use rand::Rng;

#[test]
fn range() {
    let mut rng = rand::thread_rng();
    let uniform = rand::distributions::Uniform::new(1, 500);

    println!("rng.sample(): {}", rng.sample(uniform));
    println!("rng.sample(): {}", rng.sample(uniform));
    println!("rng.sample(): {}", rng.sample(uniform));
}
