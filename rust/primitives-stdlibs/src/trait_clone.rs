// https://doc.rust-lang.org/std/clone/trait.Clone.html

// ある型が Clone を実装するかどうかの目安
// https://github.com/prometheus/client_rust/issues/53#issuecomment-1073702865
// > I think a good rule of thumb whether a type should implement Clone is whether it fits into a single CPU cache line.

// *** derive ***
// すべてのフィールドが Clone を満たしていれば、`#[derive]` が可能
#[derive(Clone)]
#[allow(dead_code)]
struct Item<P> {
    price: P,
    // もし Category が Clone を満たしていれば下記のコンパイルエラーが発生する
    // 12 |     category: Category,
    //    |     ^^^^^^^^^^^^^^^^^^ the trait `Clone` is not implemented for `Category`
    category: Category,
}

#[derive(Clone)]
#[allow(dead_code)]
struct Category {
    id: u64,
}

#[test]
fn test() {
    let item = Item {
        price: 10,
        category: Category { id: 1 },
    };
    let item_cloned = item.clone();

    assert_eq!(10, item_cloned.price);

    // 別のオブジェクトなのでアドレスが異なる
    // 参考: https://stackoverflow.com/a/30157393
    assert_ne!(format!("{:p}", &item), format!("{:p}", &item_cloned));
    // println!("{:p}", &item);
    // println!("{:p}", &item_cloned);
}
