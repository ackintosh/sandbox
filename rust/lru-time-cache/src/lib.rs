use hashlink::LinkedHashMap;
use std::hash::Hash;
use std::time::{Duration, Instant};

pub struct LruCache<K, V> {
    map: LinkedHashMap<K, (V, Instant)>,
    ttl: Duration,
    capacity: Option<usize>,
}

impl<K: Clone + Eq + Hash, V: Copy> LruCache<K, V> {
    pub fn new(ttl: Duration, capacity: Option<usize>) -> Self {
        LruCache {
            map: LinkedHashMap::new(),
            ttl,
            capacity,
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        let now = Instant::now();
        self.map.insert(key, (value, now));

        if let Some(capacity) = self.capacity {
            if self.map.len() > capacity {
                self.map.pop_front();
            }
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        self.get_mut(key).map(|value| &*value)
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let now = Instant::now();
        self.remove_expired_values(now);

        match self.map.raw_entry_mut().from_key(key) {
            hashlink::linked_hash_map::RawEntryMut::Occupied(mut occupied) => {
                occupied.replace_value((occupied.get().0, now));
                occupied.to_back();
                Some(&mut occupied.into_mut().0)
            }
            hashlink::linked_hash_map::RawEntryMut::Vacant(_) => None,
        }
    }

    /// Returns a reference to the value with the given `key`, if present and not expired, without
    /// updating the timestamp.
    pub fn peek(&self, key: &K) -> Option<&V> {
        if let Some((value, time)) = self.map.get(key) {
            return if *time + self.ttl >= Instant::now() {
                Some(value)
            } else {
                None
            }
        }

        None
    }

    pub fn len(&mut self) -> usize {
        self.remove_expired_values(Instant::now());
        self.map.len()
    }

    pub fn remove(&mut self, key: &K) {
        self.map.remove(key);
    }

    fn remove_expired_values(&mut self, now: Instant) {
        let mut expired_keys = vec![];

        for (key, (_, time)) in self.map.iter_mut() {
            if *time + self.ttl >= now {
                break;
            }
            expired_keys.push(key.clone());
        }

        for k in expired_keys {
            self.map.remove(&k);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::LruCache;
    use std::time::Duration;

    #[test]
    fn insert() {
        let mut lru_cache = LruCache::new(Duration::from_secs(10), None);

        lru_cache.insert(1, 10);
        lru_cache.insert(2, 20);
        lru_cache.insert(3, 30);

        assert_eq!(Some(&10), lru_cache.get(&1));
        assert_eq!(Some(&20), lru_cache.get(&2));
        assert_eq!(Some(&30), lru_cache.get(&3));
    }

    #[test]
    fn capacity() {
        let mut lru_cache = LruCache::new(Duration::from_secs(10), Some(2));

        lru_cache.insert(1, 10);
        lru_cache.insert(2, 20);
        assert_eq!(2, lru_cache.len());

        lru_cache.insert(3, 30);
        assert_eq!(2, lru_cache.len());
        assert_eq!(Some(&20), lru_cache.get(&2));
        assert_eq!(Some(&30), lru_cache.get(&3));
    }

    #[test]
    fn get() {
        let mut lru_cache = LruCache::new(Duration::from_secs(10), Some(2));

        lru_cache.insert(1, 10);
        lru_cache.insert(2, 20);
        assert_eq!(Some(&10), lru_cache.get(&1));

        lru_cache.insert(3, 30);
        // `1` is alive as `get()` updates the timestamp.
        assert_eq!(Some(&10), lru_cache.get(&1));
        // `2` is removed as `2` is oldest at the time `3` was inserted.
        assert_eq!(None, lru_cache.get(&2));
    }

    #[test]
    fn get_mut() {
        let mut lru_cache = LruCache::new(Duration::from_secs(10), None);

        lru_cache.insert(1, 10);
        let v = lru_cache.get_mut(&1).expect("should have value");
        *v = 100;

        assert_eq!(Some(&100), lru_cache.get(&1));
    }

    #[test]
    fn peek() {
        let mut lru_cache = LruCache::new(Duration::from_secs(10), Some(2));

        lru_cache.insert(1, 10);
        lru_cache.insert(2, 20);
        assert_eq!(Some(&10), lru_cache.peek(&1));

        lru_cache.insert(3, 30);
        // `1` is removed as `peek()` does not update the timestamp.
        assert_eq!(None, lru_cache.peek(&1));
        assert_eq!(Some(&20), lru_cache.get(&2));
    }

    #[test]
    fn len() {
        let mut lru_cache = LruCache::new(Duration::from_secs(10), None);

        assert_eq!(0, lru_cache.len());

        lru_cache.insert(1, 10);
        lru_cache.insert(2, 20);
        lru_cache.insert(3, 30);
        assert_eq!(3, lru_cache.len());
    }

    #[test]
    fn remove() {
        let mut lru_cache = LruCache::new(Duration::from_secs(10), None);

        lru_cache.insert(1, 10);
        assert_eq!(Some(&10), lru_cache.get(&1));
        lru_cache.remove(&1);
        assert_eq!(None, lru_cache.get(&1));
    }

    mod ttl {
        use crate::LruCache;
        use std::thread::sleep;
        use std::time::Duration;

        const TTL: Duration = Duration::from_millis(1);

        #[test]
        fn get() {
            let mut lru_cache = LruCache::new(TTL, None);
            lru_cache.insert(1, 10);
            assert_eq!(Some(&10), lru_cache.get(&1));

            sleep(TTL);
            assert_eq!(None, lru_cache.get(&1));
        }

        #[test]
        fn peek() {
            let mut lru_cache = LruCache::new(TTL, None);
            lru_cache.insert(1, 10);
            assert_eq!(Some(&10), lru_cache.peek(&1));

            sleep(TTL);
            assert_eq!(None, lru_cache.peek(&1));
        }

        #[test]
        fn len() {
            let mut lru_cache = LruCache::new(TTL, None);
            lru_cache.insert(1, 10);
            assert_eq!(1, lru_cache.len());

            sleep(TTL);
            assert_eq!(0, lru_cache.len());
        }
    }
}
