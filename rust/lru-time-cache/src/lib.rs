use hashlink::LinkedHashMap;
use std::hash::Hash;
use std::time::{Duration, Instant};

pub struct LruCache<K, V> {
    map: LinkedHashMap<K, (V, Instant)>,
    capacity: usize,
    ttl: Duration,
}

impl<K: Eq + Hash, V: Copy> LruCache<K, V> {
    pub fn new(capacity: usize, ttl: Duration) -> Self {
        LruCache {
            map: LinkedHashMap::new(),
            capacity,
            ttl,
        }
    }

    pub fn contains(&mut self, k: &K) -> bool {
        let now = Instant::now();
        match self.map.raw_entry_mut().from_key(k) {
            hashlink::linked_hash_map::RawEntryMut::Occupied(mut occupied) => {
                let (v, t) = {
                    let v = occupied.get();
                    (v.0, v.1)
                };

                if t + self.ttl < now {
                    occupied.remove_entry();
                    return false;
                }

                occupied.replace_value((v, now));
                occupied.to_back();
                true
            }
            hashlink::linked_hash_map::RawEntryMut::Vacant(_) => false,
        }
    }

    pub fn insert(&mut self, k: K, v: V) {
        let now = Instant::now();
        self.map.insert(k, (v, now));

        if self.map.len() > self.capacity {
            self.map.pop_front();
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::LruCache;
    use std::time::Duration;

    #[test]
    fn it_works() {
        let mut lru_cache = LruCache::new(2, Duration::new(10, 0));

        lru_cache.insert(1, 10);
        lru_cache.insert(2, 20);
        lru_cache.insert(3, 30);
        assert!(!lru_cache.contains(&1));
        assert!(lru_cache.contains(&2));
        assert!(lru_cache.contains(&3));

        lru_cache.contains(&2);
        lru_cache.insert(4, 40);
        assert!(lru_cache.contains(&2));
        assert!(!lru_cache.contains(&3));
        assert!(lru_cache.contains(&4));
    }
}
