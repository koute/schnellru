use arbitrary::Arbitrary;
use honggfuzz::fuzz;

type Key = u16;

#[derive(Arbitrary, Debug)]
pub enum Action {
    Insert { key: Key, value: u8 },
    Remove { key: Key },
    PopOldest,
    PopNewest,
    Clear,
}

#[derive(Arbitrary, Debug)]
pub struct Testcase {
    hasher_seed: usize,
    memory_usage: u16,
    actions: Vec<Action>,
}

// This is copied almost verbatim from the main crate.
#[derive(Copy, Clone, Debug)]
pub struct ByMemoryUsage {
    max_bytes: usize,
    hit_memory_limit: bool,
}

impl ByMemoryUsage {
    pub const fn new(max_bytes: usize) -> Self {
        ByMemoryUsage {
            max_bytes,
            hit_memory_limit: false,
        }
    }
}

impl<K, V> schnellru::Limiter<K, V> for ByMemoryUsage {
    type KeyToInsert<'a> = K;
    type LinkType = u32;

    #[inline]
    fn is_over_the_limit(&self, _: usize) -> bool {
        false
    }

    #[inline]
    fn on_insert(&mut self, _length: usize, key: Self::KeyToInsert<'_>, value: V) -> Option<(K, V)> {
        Some((key, value))
    }

    #[inline]
    fn on_replace(
        &mut self,
        _length: usize,
        _old_key: &mut K,
        _new_key: K,
        _old_value: &mut V,
        _new_value: &mut V,
    ) -> bool {
        true
    }

    #[inline]
    fn on_removed(&mut self, _key: &mut K, _value: &mut V) {}

    #[inline]
    fn on_cleared(&mut self) {}

    #[inline]
    fn on_grow(&mut self, new_memory_usage: usize) -> bool {
        if new_memory_usage <= self.max_bytes {
            true
        } else {
            self.hit_memory_limit = true;
            false
        }
    }
}

fn main() {
    loop {
        fuzz!(|testcase: Testcase| {
            let hasher = ahash::RandomState::with_seed(testcase.hasher_seed);
            let limiter = ByMemoryUsage::new(testcase.memory_usage as usize);
            let mut lru = schnellru::LruMap::with_hasher(limiter, hasher);
            let mut last_pointer = std::ptr::null();

            for action in testcase.actions {
                match action {
                    Action::Insert { key, value } => {
                        lru.insert(key, value);
                    }
                    Action::Remove { key } => {
                        lru.remove(&key);
                    }
                    Action::PopOldest => {
                        lru.pop_oldest();
                    }
                    Action::PopNewest => {
                        lru.pop_newest();
                    }
                    Action::Clear => {
                        lru.clear();
                    }
                }

                assert!(lru.memory_usage() <= testcase.memory_usage as usize);

                let pointer = lru.allocation_pointer();
                if lru.limiter().hit_memory_limit {
                    assert_eq!(pointer, last_pointer);
                }
                last_pointer = pointer;
            }
        });
    }
}
