use arbitrary::Arbitrary;
use honggfuzz::fuzz;

type Key = u16;

#[derive(Arbitrary, Debug)]
pub enum Action {
    Insert { key: Key, value: u8 },
    GetOrInsert { key: Key, value: u8 },
    Get { key: Key },
    Remove { key: Key },
    PopOldest,
    PopNewest,
    Clear,
}

#[derive(Arbitrary)]
pub struct Testcase {
    hasher_seed: usize,
    length: u16,
    actions: Vec<Action>,
}

#[derive(Copy, Clone, Debug)]
pub struct LimitedLength {
    limit: usize,
    cost: usize,
}

impl LimitedLength {
    pub const fn new(limit: usize) -> Self {
        LimitedLength { limit, cost: 0 }
    }
}

impl<K, V> schnellru::Limiter<K, V> for LimitedLength {
    type KeyToInsert<'a> = K;
    type LinkType = u16;

    #[inline]
    fn is_over_the_limit(&self, current_length: usize) -> bool {
        assert_eq!(self.cost, current_length);
        current_length > self.limit
    }

    #[inline]
    fn on_insert<'a>(&mut self, current_length: usize, key: Self::KeyToInsert<'a>, value: V) -> Option<(K, V)> {
        assert_eq!(self.cost, current_length);
        if self.limit > 0 {
            self.cost += 1;
            Some((key, value))
        } else {
            None
        }
    }

    #[inline]
    fn on_replace(&mut self, current_length: usize, _: &mut K, _: K, _: &mut V, _: &mut V) -> bool {
        assert_eq!(self.cost, current_length);
        self.limit > 0
    }

    #[inline]
    fn on_removed(&mut self, _: &mut K, _: &mut V) {
        assert_ne!(self.cost, 0);
        self.cost -= 1;
    }

    #[inline]
    fn on_cleared(&mut self) {
        self.cost = 0;
    }

    #[inline]
    fn on_grow(&mut self, _new_memory_usage: usize) -> bool {
        true
    }
}

fn main() {
    loop {
        fuzz!(|testcase: Testcase| {
            let hasher = ahash::RandomState::with_seed(testcase.hasher_seed);
            let mut lru = schnellru::LruMap::with_hasher(LimitedLength::new(testcase.length as usize), hasher);
            for action in &testcase.actions {
                match action {
                    Action::Insert { key, value } => {
                        lru.insert(key, value);
                    }
                    Action::GetOrInsert { key, value } => {
                        let value = lru.get_or_insert(key, || value);
                        if testcase.length == 0 {
                            assert!(value.is_none());
                        } else {
                            assert!(value.is_some());
                        }
                    }
                    Action::Get { key } => {
                        lru.get(&key);
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

                lru.assert_check_internal_state();
            }
        });
    }
}
