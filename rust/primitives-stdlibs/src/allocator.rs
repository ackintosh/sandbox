// メモリアロケーションが発生した回数を数える
// https://kanejaku.org/posts/2021/01/2021-01-27/

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::SeqCst;

struct CheckAlloc;

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CheckAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATED.fetch_add(1, SeqCst);
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
    }
}

#[global_allocator]
static A: CheckAlloc = CheckAlloc;

#[test]
fn count_allocations() {
    println!("before ret_vec: {}", ALLOCATED.load(SeqCst));
    let _r = ret_vec();
    // println!("{:?}", r);
    println!("after ret_vec {}", ALLOCATED.load(SeqCst));

    println!("before ret_iter: {}", ALLOCATED.load(SeqCst));
    let _r2 = ret_iter().collect::<Vec<_>>();
    // println!("{:?}", r2);
    println!("after ret_iter: {}", ALLOCATED.load(SeqCst));
}

fn ret_vec() -> Vec<u8> {
    println!("  ret_vec start: {}", ALLOCATED.load(SeqCst));
    let mut ret = vec![];

    println!("  ret_vec before loop: {}", ALLOCATED.load(SeqCst));
    for i in 0..9 {
        ret.push(i);
    }
    println!("  ret_vec after loop: {}", ALLOCATED.load(SeqCst));

    ret
}

fn ret_iter() -> impl Iterator<Item = u8> {
    println!("  ret_iter start: {}", ALLOCATED.load(SeqCst));
    let mut ret = vec![];

    println!("  ret_iter before loop: {}", ALLOCATED.load(SeqCst));
    for i in 0..9 {
        ret.push(i);
    }

    println!("  ret_iter after loop: {}", ALLOCATED.load(SeqCst));

    ret.into_iter()
}
