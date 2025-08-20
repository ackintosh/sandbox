use tracing::{info, instrument};

#[instrument]
pub fn add(left: u64, right: u64) -> u64 {
    info!("Adding {} + {}", left, right);
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;
    use tracing_subscriber;

    #[test]
    fn it_works() {
        tracing_subscriber::fmt::init();
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
