// https://docs.rs/dhat/0.2.2/dhat/

// CIでコケることがあるのでコメントアウト
// https://github.com/ackintosh/sandbox/runs/1910682875?check_suite_focus=true
// use dhat::{Dhat, DhatAlloc};

// #[global_allocator]
// static ALLOCATOR: DhatAlloc = DhatAlloc;

// https://github.com/unicode-org/icu4x/issues/107#issuecomment-754259472
// - The total bytes is the total amount of allocations over the entire run of the program.
// - The t-gmax refers to the maximum amount of allocated memory at a single time.
// - The t-end represents the amount of bytes left over after the dhat reference is dropped.

// https://www.valgrind.org/docs/manual/dh-manual.html
// The first line shows how many heap blocks and bytes were allocated over the entire execution.
// The second line shows how many heap blocks and bytes were alive at t-gmax, i.e. the time when the heap size reached its global maximum (as measured in bytes).
// The third line shows how many heap blocks and bytes were alive at t-end, i.e. the end of execution. In other words, how many blocks and bytes were not explicitly freed.

// dhatをCIで利用する例
// https://github.com/unicode-org/icu4x/pull/446/files

#[test]
fn test1() {
    // CIでコケることがあるのでコメントアウト
    // https://github.com/ackintosh/sandbox/runs/1910682875?check_suite_focus=true
    // let _dhat = Dhat::start_heap_profiling();

    let a = [0; 100000];
    println!("{:?}", a);
    // dhat: Total:     1,048,568 bytes in 17 blocks
    // dhat: At t-gmax: 524,288 bytes in 1 blocks
    // dhat: At t-end:  524,288 bytes in 1 blocks
    // dhat: The data in dhat-heap.json is viewable with dhat/dh_view.html
}

#[test]
fn test2() {
    // CIでコケることがあるのでコメントアウト
    // https://github.com/ackintosh/sandbox/runs/1910682875?check_suite_focus=true
    // let _dhat = Dhat::start_heap_profiling();

    let a = [0; 10];
    println!("{:?}", a);
    // dhat: Total:     88 bytes in 4 blocks
    // dhat: At t-gmax: 64 bytes in 2 blocks
    // dhat: At t-end:  64 bytes in 2 blocks
    // dhat: The data in dhat-heap.json is viewable with dhat/dh_view.html
}
