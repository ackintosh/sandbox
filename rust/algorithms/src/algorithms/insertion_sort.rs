// 参考:
// * アルゴリズム イントロダクション 1章 P.14
//   メモ: P.14の擬似コードを Rust で実装しようとすると、(擬似コードの7行目で) `j` が subtraction overflow を起こしてしまう
//         -> `j`(usize) に -1 を代入しようとしてしまう
//        なので、代わりに、下記の実装では2つの隣り合う要素をスワップするかたちにしている
// * TheAlgorithms https://github.com/TheAlgorithms/Rust/blob/master/src/sorting/insertion_sort.rs

// in-place方式で実装するので引数を &mut にしている
//   -> in-placeにすることで空間効率が O(1) になる
fn insertion_sort_asc(input: &mut Vec<u8>) {
    for i in 1..(input.len()) {
        let mut j = i - 1;
        while input[j] > input[j + 1] {
            // `j` と `j + 1` が指す要素をスワップする
            let elm = input[j + 1];
            input[j + 1] = input[j];
            input[j] = elm;
            if j == 0 {
                break;
            }
            j -= 1;
        }
    }
}

fn insertion_sort_desc(input: &mut Vec<u8>) {
    for i in 1..(input.len()) {
        let mut j = i - 1;
        while input[j] < input[j + 1] {
            let elm = input[j + 1];
            input[j + 1] = input[j];
            input[j] = elm;
            if j == 0 {
                break;
            }
            j -= 1;
        }
    }
}

// insertion_sort_ascを再帰的手続きで実装する
fn insertion_sort_recursive(input: &mut Vec<u8>) {
    _insertion_sort_recursive(input, input.len() - 1);
}

fn _insertion_sort_recursive(input: &mut Vec<u8>, right: usize) {
    if right == 0 {
        return;
    }
    _insertion_sort_recursive(input, right - 1);
    for i in (0..right).rev() {
        if input[i + 1] < input[i] {
            let elm = input[i + 1];
            input[i + 1] = input[i];
            input[i] = elm;
        } else {
            break;
        }
    }
}

mod test {
    use crate::algorithms::insertion_sort::{
        insertion_sort_asc, insertion_sort_desc, insertion_sort_recursive,
    };

    #[test]
    fn test_asc() {
        let mut input = vec![5, 2, 4, 6, 1, 3];
        insertion_sort_asc(&mut input);
        assert_eq!(vec![1, 2, 3, 4, 5, 6], input);
    }

    #[test]
    fn test_desc() {
        let mut input = vec![5, 2, 4, 6, 1, 3];
        insertion_sort_desc(&mut input);
        assert_eq!(vec![6, 5, 4, 3, 2, 1], input);
    }

    #[test]
    fn test_recursive() {
        let mut input = vec![5, 2, 4, 6, 1, 3];
        insertion_sort_recursive(&mut input);
        assert_eq!(vec![1, 2, 3, 4, 5, 6], input);
    }
}
