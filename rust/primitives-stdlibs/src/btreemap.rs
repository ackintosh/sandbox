////////////////////////////////////////
//
// std::collections::BTreeMap
//
////////////////////////////////////////

// * キーの昇順でデータが格納される
// * いろいろ操作したあとに最小値がほしいとか、ある区間の中にある値たちがほしい、みたいな場面で役立つ

// # 参考
// Rust の BTreeSet / BTreeMap で最大値を素早く取得する方法
// https://maguro.dev/btree-maximum-value/

#[cfg(test)]
use std::collections::btree_map::Entry;
#[cfg(test)]
use std::collections::BTreeMap;

#[test]
fn test() {
    let mut map = BTreeMap::new();
    map.insert(1, "foo");
    map.insert(2, "bar");

    println!("{:?}", map);
    // {1: "foo", 2: "bar"}

    // 存在するエントリ
    match map.entry(1) {
        Entry::Vacant(_) => unreachable!(),
        Entry::Occupied(occupied_entry) => {
            println!("{:?}", occupied_entry)
            // OccupiedEntry { key: 1, value: "foo" }
        }
    }

    // 存在しないエントリ
    match map.entry(999) {
        Entry::Vacant(vacant_entry) => {
            println!("{:?}", vacant_entry);
            // VacantEntry(999)
        }
        Entry::Occupied(_) => unreachable!(),
    }
}

#[test]
fn iter() {
    let mut map = BTreeMap::new();
    map.insert(2, "foo");
    map.insert(8, "bar");
    map.insert(3, "baz");
    map.insert(0, "zzz");

    // キーの昇順で出力される
    for (i, s) in map.iter() {
        println!("{i}, {s}");
        // 0, zzz
        // 2, foo
        // 3, baz
        // 8, bar
    }
}
