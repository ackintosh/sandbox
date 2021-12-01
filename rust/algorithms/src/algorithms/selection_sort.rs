// 見本: https://github.com/TheAlgorithms/Rust/blob/master/src/sorting/selection_sort.rs

// in-place方式で実装するので引数を &mut にしている
//   -> in-placeにすることで空間効率が O(1) になる
fn selection_sort(input: &mut Vec<u8>) {
    for i in 0..(input.len() - 1) {
        // 最後に残る1要素は必ず最大値なので(`input.len()`ではなく)`input.len() - 1` で良い
        let mut min_index = i;
        for j in (i + 1)..(input.len()) {
            if input[j] < input[min_index] {
                min_index = j;
            }
        }
        let minimum_num = input[min_index];
        input[min_index] = input[i];
        input[i] = minimum_num;
    }
}

mod test {
    use crate::algorithms::selection_sort::selection_sort;

    #[test]
    fn test() {
        {
            let mut input = vec![5, 2, 4, 6, 1, 3];
            selection_sort(&mut input);
            assert_eq!(vec![1, 2, 3, 4, 5, 6], input);
        }
        {
            let mut input = vec![6, 5, 4, 3, 2, 1];
            selection_sort(&mut input);
            assert_eq!(vec![1, 2, 3, 4, 5, 6], input);
        }
    }
}
