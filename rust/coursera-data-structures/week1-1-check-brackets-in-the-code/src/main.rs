use std::collections::HashMap;

// Output:
//   - If the code in S uses brackets correctly, output “Success" (without the quotes).
//   -  Otherwise, output the 1-based index of the first unmatched closing bracket, and if there are no unmatched closing brackets, output the 1-based index of the first unmatched opening bracket.
fn main() {
    let string = read_string();
    match check_brackets(string) {
        None => println!("Success"),
        Some(index) => println!("{}", index),
    }
}

fn read_string() -> String {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().to_string()
}

fn check_brackets(code: String) -> Option<usize> {
    let mut stack = vec![];

    // Compile error on the grading system
    // let brackets_mapping = HashMap::from([
    //     (']', '['),
    //     ('}', '{'),
    //     (')', '('),
    // ]);

    // closing brackets to opening brackets
    let brackets_mapping = {
        let mut map = HashMap::new();
        map.insert(']', '[');
        map.insert('}', '{');
        map.insert(')', '(');
        map
    };

    for (index, c) in code.char_indices() {
        match c {
            '[' | '{' | '(' => {
                stack.push((index, c));
            }
            ']' | '}' | ')' => match stack.pop() {
                None => return Some(index + 1),
                Some((_, extracted_char)) => {
                    if extracted_char != *brackets_mapping.get(&c).unwrap() {
                        return Some(index + 1);
                    }
                }
            },
            _ => {}
        }
    }

    match stack.pop() {
        None => None,
        Some((index, _)) => Some(index + 1),
    }
}

#[test]
fn test_check_brackets() {
    assert_eq!(None, check_brackets("[]".to_owned()));
    assert_eq!(None, check_brackets("{}[]".to_owned()));
    assert_eq!(None, check_brackets("[()]".to_owned()));
    assert_eq!(None, check_brackets("(())".to_owned()));
    assert_eq!(None, check_brackets("{[]}()".to_owned()));
    assert_eq!(Some(1), check_brackets("{".to_owned()));
    assert_eq!(Some(3), check_brackets("{[}".to_owned()));
    assert_eq!(None, check_brackets("foo(bar);".to_owned()));
    assert_eq!(Some(10), check_brackets("foo(bar[i);".to_owned()));
}
