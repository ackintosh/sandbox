// https://serde.rs/
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct Person {
    name: String,
    age: u8,
    phones: Vec<String>,
}

#[cfg(test)]
mod tests {
    use crate::Person;

    // //////////////////
    // serde_json
    // //////////////////
    #[test]
    fn json() {
        let person = Person {
            name: "AAA".to_owned(),
            age: 20,
            phones: vec!["+44 1234567".into(), "+44 2345678".into()],
        };

        // //////////////////////
        // serialize
        // https://docs.rs/serde_json/1.0.79/serde_json/#creating-json-by-serializing-data-structures
        // //////////////////////
        let json = serde_json::to_string(&person).unwrap();
        println!("{}", json); // {"name":"AAA","age":20,"phones":["+44 1234567","+44 2345678"]}

        // //////////////////////
        // deserialize
        // https://docs.rs/serde_json/1.0.79/serde_json/#parsing-json-as-strongly-typed-data-structures
        // //////////////////////
        let p: Person = serde_json::from_str(&json).unwrap();
        println!("{:?}", p);
    }
}
