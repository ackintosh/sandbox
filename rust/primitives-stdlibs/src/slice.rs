mod split {
    #[test]
    fn split_at() {
        let vec = vec![1, 2, 3, 4, 5];
        let boxed_slice = vec.into_boxed_slice();

        // インデックス 3 で分割
        let (left, right) = boxed_slice.split_at(3);
        // [0, mid)
        assert_eq!(left, &[1, 2, 3]);
        // [mid, len)
        assert_eq!(right, &[4, 5]);
    }

    #[test]
    fn view() {
        let array = [1, 2, 3];
        let slice = &array;

        assert_eq!(slice[1..], [2, 3]);
    }
}
