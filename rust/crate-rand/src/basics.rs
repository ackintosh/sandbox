use rand::{Rng, RngCore, SeedableRng};

#[test]
fn basic() {
    let i: i32 = rand::thread_rng().gen();
    println!("{:?}", i);
}

#[test]
fn range() {
    let mut rng = rand::thread_rng();
    let uniform = rand::distributions::Uniform::new(1, 500);

    println!("rng.sample(): {}", rng.sample(uniform));
    println!("rng.sample(): {}", rng.sample(uniform));
    println!("rng.sample(): {}", rng.sample(uniform));
}

// Basic pseudo-random number generators (PRNGs)
// non-cryptographic PRNGs
// https://rust-random.github.io/book/guide-rngs.html#basic-pseudo-random-number-generators-prngs
// generatorごとの速度やクオリティの比較など
#[test]
fn basic_prng() {
    // SmallRng
    // https://rust-random.github.io/rand/rand/rngs/struct.SmallRng.html
    let mut rng = rand::rngs::SmallRng::from_entropy();
    let mut data = [0u8; 8];
    rng.fill_bytes(&mut data);
    println!("{data:?}")
}
