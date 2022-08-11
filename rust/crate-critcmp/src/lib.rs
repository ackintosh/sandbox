// critcmp
// https://github.com/BurntSushi/critcmp

// Quickstartのコード例そのまま
// https://github.com/bheisler/criterion.rs#quickstart
pub fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}