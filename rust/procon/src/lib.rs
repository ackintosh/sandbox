mod p46_alds1_1_d_maximum_profit;
mod p54_alds1_1_a_insertion_sort;
mod p60_alds1_2_a_bubble_sort;
mod p65_alds1_2_b_selection_sort;

use std::convert::TryFrom;

fn u8_to_usize(n: u8) -> usize {
    usize::try_from(n).expect("should be converted to usize")
}

fn i8_to_usize(n: i8) -> usize {
    usize::try_from(n).expect("should be converted to usize")
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
