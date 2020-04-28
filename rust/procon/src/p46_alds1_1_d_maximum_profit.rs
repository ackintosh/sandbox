// プロコンのためのアルゴリズムとデータ構造
// 2.5 導入問題
use std::convert::TryFrom;

////////////////////
// O(n^2)
////////////////////
fn main(n: u64, r: Vec<u64>) -> i64 {
    let ii = n.clone();
    let jj = n.clone();

    let mut max_profit: Option<i64> = None;

    for i in 0..ii {
        for j in (i+1..jj).rev() {
            println!("i : {}", i);
            println!("j : {}", j);

            let rj = i64::try_from(
                r[usize::try_from(j).unwrap()]
            ).unwrap();
            let ri = i64::try_from(
                r[usize::try_from(i).unwrap()]
            ).unwrap();
            println!("rj : {}", rj);
            println!("ri : {}", ri);

            let profit = rj - ri;
            println!("profit : {}", profit);

            if max_profit.is_none() {
                max_profit = Some(profit);
            } else {
                if profit > max_profit.unwrap() {
                    max_profit = Some(profit);
                }
            }
            println!("max_profit : {}", max_profit.unwrap());
        }
    }

    max_profit.unwrap()
}

////////////////////
// O(n)
////////////////////
fn main2(n: u64, r: Vec<u64>) -> i64 {
    let mut minv = r.first().unwrap().clone();
    let mut max_profit: Option<i64> = None;

    for j in 1..n {
        let rj = r[usize::try_from(j).unwrap()];

        // Update `max_profit`
        let v = i64::try_from(rj.clone()).unwrap();
        let v_min = i64::try_from(minv.clone()).unwrap();
        let result: i64 = v - v_min;

        if max_profit.is_none() {
            max_profit = Some(result);
        } else {
            if result > max_profit.unwrap() {
                max_profit = Some(result);
            }
        }

        // Update `minv`
        if rj < minv {
            minv = rj;
        }
    }

    max_profit.unwrap()
}

#[test]
fn test() {
    assert_eq!(main(6, vec![5, 3, 1, 3, 4, 3]), 3);
    assert_eq!(main(3, vec![4, 3, 2]), -1);

    assert_eq!(main2(6, vec![5, 3, 1, 3, 4, 3]), 3);
    assert_eq!(main2(3, vec![4, 3, 2]), -1);
}