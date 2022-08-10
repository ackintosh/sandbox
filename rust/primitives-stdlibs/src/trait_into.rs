use std::convert::TryInto;

#[test]
fn test() {
    let foo = Foo { i: 10_u64 };
    foo.print();
}

struct Foo<T> {
    i: T,
}

// trait bound に TryInto を指定する
impl<T> Foo<T>
where
    T: TryInto<i64> + Copy,
{
    fn print(&self) {
        let x = self.i.try_into().unwrap_or(0);
        println!("{:?}", x);
    }
}
