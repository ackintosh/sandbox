// https://serde.rs/
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct Person {
    name: String,
    age: u8,
    phones: Vec<String>,
}

#[cfg(test)]
mod tests {
    use crate::Person;

    #[test]
    fn json() {
        let person = Person {
            name: "AAA".to_owned(),
            age: 20,
            phones: vec!["+44 1234567".into(), "+44 2345678".into()],
        };

        let serialized = serde_json::to_string(&person);

        assert!(serialized.is_ok());
        println!("{}", serialized.unwrap()); // {"name":"AAA","age":20,"phones":["+44 1234567","+44 2345678"]}
    }
}
