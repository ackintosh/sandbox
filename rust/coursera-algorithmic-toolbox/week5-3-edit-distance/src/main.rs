// https://www.coursera.org/learn/algorithmic-toolbox/programming/ekN4T/programming-assignment-5-dynamic-programming-1/instructions
fn main() {
    let a = read_string();
    let b = read_string();

    println!("{}", edit_distance(a, b));
}

fn read_string() -> String {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().to_string()
}

fn edit_distance(a: String, b: String) -> u32 {
    let mut matrix = vec![vec![0; b.len() + 1]; a.len() + 1];

    for i in 0..=a.len() {
        matrix[i][0] = i as u32;
    }

    for j in 0..=b.len() {
        matrix[0][j] = j as u32;
    }
    // println!("{:?}", matrix);

    for i in 1..=a.len() {
        for j in 1..=b.len() {
            let insertion = matrix[i][j - 1] + 1;
            let deletion = matrix[i - 1][j] + 1;
            let matched = matrix[i - 1][j - 1];
            let mismatched = matrix[i - 1][j - 1] + 1;

            // 文字列の index を指定するときはゼロオリジンなので i - 1/j - 1 にしている
            if a.chars().nth(i - 1).unwrap() == b.chars().nth(j - 1).unwrap() {
                matrix[i][j] = matched.min(insertion.min(deletion));
            } else {
                matrix[i][j] = mismatched.min(insertion.min(deletion));
            }
        }
    }

    matrix[a.len()][b.len()]
}

#[test]
fn test_edit_distance() {
    assert_eq!(0, edit_distance("ab".to_owned(), "ab".to_owned()));
    assert_eq!(3, edit_distance("short".to_owned(), "ports".to_owned()));
}
