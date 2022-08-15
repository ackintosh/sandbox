// ///////////////////////////////////////////////////////////////
// How to switch between `vec` version and `iter` version.
// * There are some mark: `before(vec)`, `after(iter)`.
//   * Cargo.toml
//     * `prometheus-client` dependency
//   * src/lib.rs
//     * `use` declaration
//     * Instantiating `Registry`
// * Enable the one you want to test.
// ///////////////////////////////////////////////////////////////

// ///////////////////////////////////////////////////////////////
// * before (vec)
// use prometheus_client::encoding::proto::EncodeProtobuf as Encode;
// * after (iter)
use prometheus_client::encoding::proto::Encode;
// ///////////////////////////////////////////////////////////////

use prometheus_client::encoding::proto::{encode, EncodeMetric};
use prometheus_client::metrics::counter::Counter;
use prometheus_client::metrics::family::Family;
use prometheus_client::metrics::histogram::{exponential_buckets, Histogram};
use prometheus_client::registry::Registry;
use std::fmt::{Display, Formatter};
use std::vec::IntoIter;

#[derive(Clone, Hash, PartialEq, Eq, Encode)]
struct Labels {
    path: String,
    method: Method,
    some_number: u64,
}

#[derive(Clone, Hash, PartialEq, Eq)]
enum Method {
    Get,
    #[allow(dead_code)]
    Put,
}

impl Display for Method {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Method::Get => write!(f, "Get"),
            Method::Put => write!(f, "Put"),
        }
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Encode)]
enum Region {
    Africa,
    #[allow(dead_code)]
    Asia,
}

pub fn run_encode() -> prometheus_client::encoding::proto::MetricSet {
    // ///////////////////////////////////////////////////////////////
    // * before (vec)
    // let mut registry = Registry::<Box<dyn EncodeMetric>>::default();
    // * after (iter)
    let mut registry = Registry::<
        Box<dyn EncodeMetric<Iterator = IntoIter<prometheus_client::encoding::proto::Metric>>>,
    >::default();
    // ///////////////////////////////////////////////////////////////

    for i in 0..100 {
        let counter_family = Family::<Labels, Counter>::default();
        let histogram_family = Family::<Region, Histogram>::new_with_constructor(|| {
            Histogram::new(exponential_buckets(1.0, 2.0, 10))
        });

        registry.register(
            format!("my_counter{}", i),
            "My counter",
            Box::new(counter_family.clone()),
        );
        registry.register(
            format!("my_histogram{}", i),
            "My histogram",
            Box::new(histogram_family.clone()),
        );

        for j in 0_u32..100 {
            counter_family
                .get_or_create(&Labels {
                    path: format!("/path/{}", i),
                    method: Method::Get,
                    some_number: j.into(),
                })
                .inc();

            histogram_family
                .get_or_create(&Region::Africa)
                .observe(j.into());
        }
    }

    encode(&registry)
}

#[cfg(test)]
mod allocation_count {
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering::SeqCst;
    use crate::run_encode;

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
    fn allocation_count() {
        let before = ALLOCATED.load(SeqCst);

        let _metric_set = run_encode();

        // *** Allocation count ***
        // before (vec): allocation count: 124114
        // after (iter): allocation count: 124214
        println!("allocation count: {}", ALLOCATED.load(SeqCst) - before);
    }
}
