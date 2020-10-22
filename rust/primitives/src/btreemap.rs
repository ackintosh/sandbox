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

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

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
        Entry::Occupied(_) => unreachable!()
    }
}
