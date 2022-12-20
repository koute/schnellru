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

fn main() {
    loop {
        fuzz!(|testcase: Testcase| {
            let hasher = ahash::RandomState::with_seed(testcase.hasher_seed);
            let limiter = schnellru::ByMemoryUsage::new(testcase.memory_usage as usize);
            let mut lru = schnellru::LruMap::with_hasher(limiter, hasher);

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
            }
        });
    }
}
