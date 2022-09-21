#[test]
fn max() {
    assert_eq!(2_147_483_647, i32::MAX);
}

#[test]
fn size_of_usize_isize() {
    // std::mem::size_of()
    // https://doc.rust-lang.org/std/mem/fn.size_of.html
    // 型のサイズ(byte)を返す

    // https://doc.rust-jp.rs/book/second-edition/ch03-02-data-types.html#a%E6%95%B4%E6%95%B0%E5%9E%8B
    // usize, isizeのサイズは、64bitアーキテクチャの場合は 8 (8byte) を返す
    assert_eq!(8, std::mem::size_of::<usize>());
    assert_eq!(8, std::mem::size_of::<isize>());
}

#[test]
fn cmp() {
    let n = 10;
    let m = 20;

    match n.cmp(&m) {
        std::cmp::Ordering::Equal => println!("n = m"),
        std::cmp::Ordering::Greater => println!("n > m"),
        std::cmp::Ordering::Less => println!("n < m"),
    }

    // n < m が出力される
}

mod convert {
    use std::convert::TryFrom;

    #[test]
    fn to_string() {
        let num = 6699;
        assert_eq!("6699".to_owned(), num.to_string());
    }

    #[test]
    fn string_to_number() {
        let s = "10";
        assert_eq!(10_u8, s.parse::<u8>().unwrap());
    }

    #[test]
    fn uint_to_float() {
        let i = 1_u64;
        println!("{}", i as f64)
    }

    #[test]
    fn positive_to_negative() {
        let positive = 10;
        assert_eq!(-10, -positive);
    }

    #[test]
    fn usize_to_isize() {
        let u = 1_usize;
        let i = isize::try_from(u).unwrap();
        assert_eq!(1_isize, i);
    }

    mod usize_to_i32 {
        use std::convert::TryFrom;

        #[test]
        fn usize_to_i32() {
            let num_usize = 1_usize;
            let num_i32 = i32::try_from(num_usize).unwrap();

            assert_eq!(num_i32, 1_i32);
        }
    }
}
