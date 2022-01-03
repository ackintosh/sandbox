// ////////////////////////////////////////////////////////////
// 2つに分割するパターン
// 参考:
// * https://www.geeksforgeeks.org/partition-problem-dp-18/
// ////////////////////////////////////////////////////////////

// *DPで実装するパターン*
// -> https://www.geeksforgeeks.org/partition-problem-dp-18/ の `Dynamic Programming Solution`
// input: 要素
// output: 2分割可能(= 合計値の半分と等しいサブセットが存在する)ならばtrue
fn two_partition_problem_dp(input: Vec<u8>) -> bool {
    let sum: u8 = input.iter().sum();
    // inputの合計値が偶数出ない場合、2分割が不可能なのでfalse
    if sum % 2 != 0 {
        return false;
    }

    // 合計値の半分
    // これと等しいサブセットが存在するならば、2分割可能と判断できる
    let half_of_sum = sum / 2;

    // 0から始まるマトリックスを作るために下記になる
    // * x軸: 0から `half_of_sum + 1` まで
    // * y軸: 0から `input.len() + 1` まで
    let mut matrix = vec![vec![false; input.len() + 1]; (half_of_sum + 1) as usize];

    // 値がゼロならば、アイテムに関わらず分割可能なので true を入れておく
    // ただし、アイテム無し(j = 0)は除くので、ループは 1 から始めている
    for j in 1..=input.len() {
        matrix[0][j] = true;
    }

    for i in 1..=half_of_sum as usize {
        for j in 1..=input.len() {
            // ////////////////////////////////////////////
            // 下記いずれかの条件を満たすならば、2分割可能と判断する
            // * 現在のアイテム抜きで、サブセットが存在する
            //     -> 同一の合計値(i)で、アイテムを1つ引いた(j - 1)、マトリックス上の要素がtrueかどうか
            // * 現在のアイテムを考慮したときに、サブセットが存在する
            //     -> 合計値(i)からアイテムの値を引き、アイテムを1つ引いた(j - 1)、マトリックス上の要素がtrueかどうか
            //        (上記がtrueならば、現在のアイテムを考慮した場合でもtrueになる)
            // ////////////////////////////////////////////

            // 現在のアイテム抜きで、サブセットが存在するか否か
            let without_current_item = matrix[i][j - 1];

            // 現在のアイテムを考慮したときに、サブセットが存在するか否か
            let consider_current_item = if i as u8 >= input[j - 1] {
                matrix[i - (input[j - 1] as usize)][j - 1]
            } else {
                false
            };

            // いずれかの条件を満たすならば、2分割可能と判断する
            matrix[i][j] = without_current_item || consider_current_item;
        }
    }

    // println!("{:?}", matrix);

    matrix[half_of_sum as usize][input.len()]
}

#[test]
fn test_two_partition_problem_dp() {
    // The array can be partitioned as {1, 5, 5} and {11}
    assert!(two_partition_problem_dp(vec![1, 5, 11, 5]));

    // The array cannot be partitioned into equal sum sets.
    assert!(!two_partition_problem_dp(vec![1, 5, 3]));
}

// *DPで実装するパターン*
// 2次元のマトリックスではなく、配列を作るパターン
// -> https://www.geeksforgeeks.org/partition-problem-dp-18/ の `Dynamic Programming Solution (Space Complexity Optimized)`
fn two_partition_problem_dp_array(input: Vec<u8>) -> bool {
    let sum: u8 = input.iter().sum();
    if sum % 2 != 0 {
        return false;
    }

    let half_of_sum = sum / 2;
    let mut table = vec![false; half_of_sum as usize + 1];

    table[0] = true;

    for i in 0..input.len() {
        for j in (1..=half_of_sum as usize).rev() {
            if (j as u8) < input[i] {
                break;
            }

            if j == input[i] as usize || table[j - (input[i] as usize)] {
                table[j] = true;
            }
        }
    }

    return table[half_of_sum as usize];
}

#[test]
fn test_two_partition_problem_dp_array() {
    // The array can be partitioned as {1, 5, 5} and {11}
    assert!(two_partition_problem_dp_array(vec![1, 5, 11, 5]));

    // The array cannot be partitioned into equal sum sets.
    assert!(!two_partition_problem_dp_array(vec![1, 5, 3]));
}

// ////////////////////////////////////////////////////////////
// 3つに分割するパターン
// 参考:
// * https://stackoverflow.com/questions/4803668/3-partition-problem
// * https://thisthread.blogspot.com/2018/02/partitioning-souvenirs.html
// ////////////////////////////////////////////////////////////
// 下記を参照
// https://github.com/ackintosh/sandbox/blob/master/rust/coursera-algorithmic-toolbox/week6-2-partition-souvenirs/src/main.rs
