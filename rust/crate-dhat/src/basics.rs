// https://docs.rs/dhat/0.2.2/dhat/

use dhat::{Dhat, DhatAlloc};

#[global_allocator]
static ALLOCATOR: DhatAlloc = DhatAlloc;

// https://github.com/unicode-org/icu4x/issues/107#issuecomment-754259472
// - The total bytes is the total amount of allocations over the entire run of the program.
// - The t-gmax refers to the maximum amount of allocated memory at a single time.
// - The t-end represents the amount of bytes left over after the dhat reference is dropped.

// dhatをCIで利用する例
// https://github.com/unicode-org/icu4x/pull/446/files

#[test]
fn test1() {
    let _dhat = Dhat::start_heap_profiling();

    let a = [0; 100000];
    println!("{:?}", a);
    // dhat: Total:     1,048,568 bytes in 17 blocks
    // dhat: At t-gmax: 524,288 bytes in 1 blocks
    // dhat: At t-end:  524,288 bytes in 1 blocks
    // dhat: The data in dhat-heap.json is viewable with dhat/dh_view.html
}

#[test]
fn test2() {
    let _dhat = Dhat::start_heap_profiling();

    let a = [0; 10];
    println!("{:?}", a);
    // dhat: Total:     88 bytes in 4 blocks
    // dhat: At t-gmax: 64 bytes in 2 blocks
    // dhat: At t-end:  64 bytes in 2 blocks
    // dhat: The data in dhat-heap.json is viewable with dhat/dh_view.html
}
