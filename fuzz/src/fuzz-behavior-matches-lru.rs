use arbitrary::Arbitrary;
use honggfuzz::fuzz;
use std::num::NonZeroUsize;

type Key = u16;

#[derive(Arbitrary)]
pub enum Action {
    Insert { key: Key, value: u8 },
    GetOrInsert { key: Key, value: u8 },
    Get { key: Key },
    Peek { key: Key },
    Remove { key: Key },
    PopOldest,
    Clear,
}

#[derive(Arbitrary)]
pub struct Testcase {
    hasher_seed: usize,
    length: u16,
    actions: Vec<Action>,
}

fn main() {
    loop {
        fuzz!(|testcase: Testcase| {
            let hasher = ahash::RandomState::with_seed(testcase.hasher_seed);
            let length = std::cmp::max(1, testcase.length) as usize;
            let mut lru = schnellru::LruMap::with_hasher(schnellru::ByLength::new(length as u32), hasher.clone());
            let mut lru_sanity = lru::LruCache::with_hasher(NonZeroUsize::new(length).unwrap(), hasher);

            for action in testcase.actions {
                match action {
                    Action::Insert { key, value } => {
                        lru.insert(key, value);
                        lru_sanity.push(key, value);
                        assert_eq!(lru.len(), lru_sanity.len());
                    }
                    Action::GetOrInsert { key, value } => {
                        let value_lru = lru.get_or_insert(key, || value).unwrap();
                        let value_lru_sanity = lru_sanity.get_or_insert(key, || value);
                        assert_eq!(value_lru, value_lru_sanity);
                    }
                    Action::Get { key } => {
                        assert_eq!(lru.get(&key).copied(), lru_sanity.get(&key).copied());
                    }
                    Action::Remove { key } => {
                        assert_eq!(lru.remove(&key), lru_sanity.pop(&key));
                    }
                    Action::Peek { key } => {
                        assert_eq!(lru.peek(&key), lru_sanity.peek(&key));
                    }
                    Action::PopOldest => {
                        assert_eq!(lru.pop_oldest(), lru_sanity.pop_lru());
                    }
                    Action::Clear => {
                        lru.clear();
                        lru_sanity.clear();
                    }
                }
            }
        });
    }
}
