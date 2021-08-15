use hashlink::LinkedHashMap;
use std::hash::Hash;
use std::time::{Duration, Instant};

pub struct LruCache<K, V> {
    map: LinkedHashMap<K, (V, Instant)>,
    capacity: usize,
    ttl: Duration,
}

impl<K: Clone + Eq + Hash, V: Copy> LruCache<K, V> {
    pub fn new(capacity: usize, ttl: Duration) -> Self {
        LruCache {
            map: LinkedHashMap::new(),
            capacity,
            ttl,
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        let now = Instant::now();
        self.map.insert(key, (value, now));

        if self.map.len() > self.capacity {
            self.map.pop_front();
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
                None
            } else {
                Some(value)
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
        let mut lru_cache = LruCache::new(2, Duration::new(10, 0));

        lru_cache.insert(1, 10);
        lru_cache.insert(2, 20);
        lru_cache.insert(3, 30);

        assert_eq!(None, lru_cache.get(&1));
        assert_eq!(Some(&20), lru_cache.get(&2));
        assert_eq!(Some(&30), lru_cache.get(&3));

        lru_cache.get(&2);
        lru_cache.insert(4, 40);
        assert_eq!(Some(&20), lru_cache.get(&2));
        assert_eq!(None, lru_cache.get(&3));
        assert_eq!(Some(&40), lru_cache.get(&4));
    }

    #[test]
    fn len() {
        let mut lru_cache = LruCache::new(10, Duration::new(10, 0));

        assert_eq!(0, lru_cache.len());

        lru_cache.insert(1, 10);
        lru_cache.insert(2, 20);
        lru_cache.insert(3, 30);
        assert_eq!(3, lru_cache.len());
    }

    #[test]
    fn remove() {
        let mut lru_cache = LruCache::new(2, Duration::new(10, 0));

        lru_cache.insert(1, 10);
        assert_eq!(Some(&10), lru_cache.get(&1));
        lru_cache.remove(&1);
        assert_eq!(None, lru_cache.get(&1));
    }
}
