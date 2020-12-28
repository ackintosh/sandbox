mod test {
    #[test]
    fn test() {
        let byte_array = vec![b'h', b'e', b'l', b'l', b'o'];

        // Vec<u8> から Box<u8> に変換する
        print(byte_array.into_boxed_slice());
        // let byte_array = [b'h', b'e', b'l', b'l', b'o', b'!'];
        // print(Box::new(byte_array));
    }

    fn print(s: Box<[u8]>) {
    // fn print(s: [u8]) {
        println!("{:?}", s);
    }
}
