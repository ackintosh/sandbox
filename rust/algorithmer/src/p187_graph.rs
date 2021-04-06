// 会社の組織と給与

// メモ化再帰での解法
fn solution(relations: Vec<Vec<&str>>) -> i32 {
    let mut result = 0;
    let mut memo = vec![0; relations.len()];

    for i in 0..relations.len() {
        result += if memo[i] != 0 {
            memo[i]
        } else {
            salary(i, &relations, &mut memo)
        };
    }

    return result;

    fn salary(i: usize, relations: &Vec<Vec<&str>>, memo: &mut Vec<i32>) -> i32 {
        if memo[i] != 0 {
            return memo[i];
        }

        let r = &relations[i];

        let mut result = 0;

        for ii in 0..r.len() {
            if i == ii {
                // 自分自身
                continue;
            }

            if r[ii] == "Y" {
                result += salary(ii, relations, memo);
            }
        }

        let salary = if result == 0 {
            // 部下がいないので1
            1
        } else {
            result
        };

        memo[i] = salary;
        salary
    }
}

#[test]
fn example0() {
    let relations = vec![
        vec!["N"],
    ];

    assert_eq!(1, solution(relations));
}

#[test]
fn example0_1() {
    let relations = vec![
        vec!["N", "Y"],
        vec!["N", "N"],
    ];

    assert_eq!(2, solution(relations));
}

#[test]
fn example1() {
    let relations = vec![
        vec!["N", "N", "Y", "N"],
        vec!["N", "N", "Y", "N"],
        vec!["N", "N", "N", "N"],
        vec!["N", "Y", "Y", "N"],
    ];

    assert_eq!(5, solution(relations));
}

#[test]
fn example2() {
    let relations = vec![
        vec!["N", "N", "N", "N", "N", "N"],
        vec!["Y", "N", "Y", "N", "N", "Y"],
        vec!["Y", "N", "N", "N", "N", "Y"],
        vec!["N", "N", "N", "N", "N", "N"],
        vec!["Y", "N", "Y", "N", "N", "N"],
        vec!["Y", "N", "N", "Y", "N", "N"],
    ];

    assert_eq!(17, solution(relations));
}
