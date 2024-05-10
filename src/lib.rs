#![doc = include_str!("../README.md")]
#![no_std]
#![deny(missing_docs)]
#![deny(unused_must_use)]
#![allow(clippy::while_let_on_iterator)]

use core::hash::{BuildHasher, Hash, Hasher};
use hashbrown::raw::{Bucket, RawTable};

extern crate alloc;

mod limiters;
pub use limiters::*;

// Mostly copied from `hashbrown`.
cfg_if::cfg_if! {
        if #[cfg(all(
            target_feature = "sse2",
            any(target_arch = "x86", target_arch = "x86_64"),
            not(miri)
        ))] {
            const GROUP_WIDTH: usize = 16;
        } else if
               #[cfg(any(
                target_pointer_width = "64",
                target_arch = "aarch64",
                target_arch = "x86_64",
                target_arch = "wasm32",
            ))] {
            const GROUP_WIDTH: usize = 8;
        } else {
            const GROUP_WIDTH: usize = 4;
        }
}

/// Returns the number of buckets for a given `capacity`.
///
/// Mostly copied from `hashbrown` with minor modifications.
const fn buckets_for_capacity(capacity: usize, max: usize) -> Option<usize> {
    if capacity == 0 {
        Some(0)
    } else if capacity < 4 {
        Some(4)
    } else if capacity < 8 {
        Some(8)
    } else {
        // Use a match since `?` is not yet const-stable.
        let capacity_times_8 = match capacity.checked_mul(8) {
            Some(value) => value,
            None => return None,
        };

        let buckets = (capacity_times_8 / 7).next_power_of_two();
        if buckets >= max {
            None
        } else {
            Some(buckets)
        }
    }
}

/// Returns the full capacity of the map for a given number of `buckets`.
const fn full_capacity_for_buckets(buckets: usize) -> usize {
    if buckets == 0 {
        0
    } else if buckets <= 8 {
        buckets - 1
    } else {
        buckets / 8 * 7
    }
}

mod private {
    /// This trait's used as the type of the links between the nodes in the LRU map.
    ///
    /// # Safety
    ///
    /// - None of the methods can panic.
    /// - The `MAX` must be the maximum value.
    #[doc(hidden)]
    pub unsafe trait LinkType: Copy + PartialEq + Eq + core::fmt::Debug {
        /// Used as a sentinel value for an empty link.
        const MAX: Self;

        fn from_usize(value: usize) -> Self;
        fn into_usize(self) -> usize;
    }

    unsafe impl LinkType for usize {
        const MAX: Self = usize::MAX;

        #[inline]
        fn from_usize(value: usize) -> Self {
            value
        }

        #[inline]
        fn into_usize(self) -> usize {
            self
        }
    }

    unsafe impl LinkType for u32 {
        const MAX: Self = u32::MAX;

        #[inline]
        fn from_usize(value: usize) -> Self {
            value as u32
        }

        #[inline]
        fn into_usize(self) -> usize {
            self as usize
        }
    }

    unsafe impl LinkType for u16 {
        const MAX: Self = u16::MAX;

        #[inline]
        fn from_usize(value: usize) -> Self {
            value as u16
        }

        #[inline]
        fn into_usize(self) -> usize {
            self as usize
        }
    }

    unsafe impl LinkType for u8 {
        const MAX: Self = u8::MAX;

        #[inline]
        fn from_usize(value: usize) -> Self {
            value as u8
        }

        #[inline]
        fn into_usize(self) -> usize {
            self as usize
        }
    }
}

use private::LinkType;

/// A trait used to customize the behavior and the limits of the LRU map.
pub trait Limiter<K, V> {
    /// The type of the key to be inserted into the map.
    ///
    /// This is the type which is passed into `insert`.
    ///
    /// This usually should be the same as `K`, but can be set to a different type
    /// if creating an instance of `K` is not zero-cost and we want to achieve
    /// zero-cost replacement of existing values through `insert`.
    type KeyToInsert<'a>;

    /// The type used to hold the links between the nodes inside of the LRU map.
    ///
    /// In practice this type determines the maximum number of elements that can be in the map,
    /// regardless of any other limits imposed on it.
    ///
    /// The exact limit is implementation defined.
    ///
    /// The narrower the type the less memory each element in the map
    /// will use, and the map should also get slightly faster as long
    /// as this limit will not be hit.
    ///
    /// Can be one of: `usize`, `u32`, `u16`, `u8`.
    ///
    /// You probably want to use either `usize` or `u32` here.
    type LinkType: LinkType;

    /// Checks whether any of the elements must be popped.
    ///
    /// This is called before an element is inserted, and after it was inserted.
    ///
    /// The `length` specifies how many elements will be in the map or how many are currently
    /// in the map, depending on whether this was called before or after an insert.
    fn is_over_the_limit(&self, length: usize) -> bool;

    /// Called *before* a node is inserted into the map.
    ///
    /// Should return `None` if it would be impossible to insert a given element into an empty map.
    /// Otherwise should always return `Some` and, if applicable, update its internal cost estimate.
    ///
    /// Changing the key here in a way that hashes or compares differently is a logic error.
    ///
    /// The `length` specifies how many elements are currently in the map.
    /// The `key` and `value` is the key and value of the element we're about to insert.
    fn on_insert(&mut self, length: usize, key: Self::KeyToInsert<'_>, value: V) -> Option<(K, V)>;

    /// Called *before* a value is replaced inside of the map.
    ///
    /// Should return `false` if it would be impossible to insert a given element into an empty map.
    /// Otherwise should always return `true` and, if applicable, update its internal cost estimate.
    ///
    /// Returning `false` will remove the element from the map.
    ///
    /// The `length` specifies how many elements are currently in the map.
    /// The `old_key` and `old_value` is the key and value that are already inside of the map.
    /// The `new_key` and `new_value` is the key and value of the element we're about to insert.
    ///
    /// Changing the `old_key` here in a way that hashes or compares differently is a logic error.
    ///
    /// This is only called when the keys are equal! The `old_key` will be kept in the map while
    /// the `new_key` is moved into this callback, so you're free to do with it as you see fit.
    // TODO: Rename to `on_replace_value`.
    fn on_replace(
        &mut self,
        length: usize,
        old_key: &mut K,
        new_key: Self::KeyToInsert<'_>,
        old_value: &mut V,
        new_value: &mut V,
    ) -> bool;

    /// Called *after* an element is removed from the map.
    ///
    /// If applicable the internal cost estimate should be updated to account for the removed node.
    fn on_removed(&mut self, key: &mut K, value: &mut V);

    /// Called *after* the map is cleared.
    ///
    /// If applicable the internal cost estimate should be set to zero here.
    fn on_cleared(&mut self);

    /// Called *before* the map is resized.
    ///
    /// Returns whether the map should be allowed to grow.
    ///
    /// Returning `false` here will ensure that no memory will be allocated.
    ///
    /// The `new_memory_usage` specifies how much memory the map will consume *after* the resize.
    fn on_grow(&mut self, new_memory_usage: usize) -> bool;
}

#[derive(Clone)]
struct Entry<K, V, E> {
    key: K,
    value: V,
    older: E,
    newer: E,
}

/// The default hasher used by the LRU map.
// Create a newtype to isolate the public API.
pub struct DefaultHasher(ahash::AHasher);

impl Hasher for DefaultHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0.finish()
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        self.0.write(bytes)
    }

    #[inline]
    fn write_u8(&mut self, value: u8) {
        self.0.write_u8(value)
    }

    #[inline]
    fn write_u16(&mut self, value: u16) {
        self.0.write_u16(value)
    }

    #[inline]
    fn write_u32(&mut self, value: u32) {
        self.0.write_u32(value)
    }

    #[inline]
    fn write_u128(&mut self, value: u128) {
        self.0.write_u128(value)
    }

    #[inline]
    fn write_usize(&mut self, value: usize) {
        self.0.write_usize(value)
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        self.0.write_u64(value)
    }
}

/// The default hash builder used by the LRU map.
// Create a newtype to isolate the public API.
#[derive(Debug)]
#[cfg_attr(feature = "runtime-rng", derive(Default))]
pub struct RandomState(ahash::RandomState);

impl BuildHasher for RandomState {
    type Hasher = DefaultHasher;

    #[inline]
    fn build_hasher(&self) -> Self::Hasher {
        DefaultHasher(self.0.build_hasher())
    }
}

/// An LRU hash map.
#[derive(Clone)]
pub struct LruMap<K, V, L = ByLength, S = RandomState>
where
    L: Limiter<K, V>,
{
    // Internally this is just a normal hash map with its buckets added to a linked list.
    hasher: S,
    map: RawTable<Entry<K, V, L::LinkType>>,
    newest: <L as Limiter<K, V>>::LinkType,
    oldest: <L as Limiter<K, V>>::LinkType,
    limiter: L,
}

impl<K, V, L, S> core::fmt::Debug for LruMap<K, V, L, S>
where
    L: Limiter<K, V>,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LruMap")
            .field("len", &self.map.len())
            .field("key_type", &core::any::type_name::<K>())
            .field("value_type", &core::any::type_name::<V>())
            .finish_non_exhaustive()
    }
}

impl<K, V, L, S> Default for LruMap<K, V, L, S>
where
    K: Hash + PartialEq,
    S: BuildHasher + Default,
    L: Limiter<K, V> + Default,
{
    fn default() -> Self {
        Self::with_hasher(L::default(), S::default())
    }
}

impl<K, V, L> LruMap<K, V, L, RandomState>
where
    K: Hash + PartialEq,
    L: Limiter<K, V>,
{
    /// Creates a new empty map with a given `limiter`.
    #[cfg(feature = "runtime-rng")]
    pub fn new(limiter: L) -> Self {
        Self::with_hasher(limiter, RandomState::default())
    }

    /// Creates a new empty map with a given `limiter` and a non-randomized hasher.
    pub const fn with_seed(limiter: L, seed: [u64; 4]) -> Self {
        let hasher = ahash::RandomState::with_seeds(seed[0], seed[1], seed[2], seed[3]);
        Self::with_hasher(limiter, RandomState(hasher))
    }
}

impl<K, V, S> LruMap<K, V, ByMemoryUsage, S>
where
    K: Hash + PartialEq,
    S: BuildHasher,
{
    /// Creates a new empty map with a given `memory_budget` and `hasher`.
    ///
    /// This will configure the limiter so that the map can use at most `memory_budget`
    /// bytes of memory.
    ///
    /// This does not preallocate any memory.
    pub const fn with_memory_budget_and_hasher(memory_budget: usize, hasher: S) -> Self {
        let limiter = ByMemoryUsage::new(memory_budget);
        Self::with_hasher(limiter, hasher)
    }
}

impl<K, V> LruMap<K, V, ByMemoryUsage, RandomState>
where
    K: Hash + PartialEq,
{
    /// Creates a new empty map with a given `memory_budget`.
    ///
    /// This will configure the limiter so that the map can use at most `memory_budget`
    /// bytes of memory.
    ///
    /// This does not preallocate any memory.
    #[cfg(feature = "runtime-rng")]
    pub fn with_memory_budget(memory_budget: usize) -> Self {
        Self::with_memory_budget_and_hasher(memory_budget, RandomState::default())
    }
}

impl<K, V, L, S> LruMap<K, V, L, S>
where
    K: Hash + PartialEq,
    S: BuildHasher,
    L: Limiter<K, V>,
{
    fn assert_not_empty(&self) {
        debug_assert_ne!(self.newest, L::LinkType::MAX);
        debug_assert_ne!(self.oldest, L::LinkType::MAX);
        debug_assert!(!self.map.is_empty());
    }

    fn assert_empty(&self) {
        debug_assert_eq!(self.newest, L::LinkType::MAX);
        debug_assert_eq!(self.oldest, L::LinkType::MAX);
        debug_assert!(self.map.is_empty());
    }

    /// This checks that the map's internal state is consistent.
    ///
    /// Not a public API; exported as public to use for testing.
    #[doc(hidden)]
    pub fn assert_check_internal_state(&self) {
        if self.map.is_empty() {
            assert_eq!(self.newest, L::LinkType::MAX);
            assert_eq!(self.oldest, L::LinkType::MAX);
            return;
        }

        assert_ne!(self.newest, L::LinkType::MAX);
        assert_ne!(self.oldest, L::LinkType::MAX);

        if self.map.len() == 1 {
            assert_eq!(self.newest, self.oldest);

            {
                let node = unsafe { self.map.bucket(self.newest.into_usize()).as_ref() };
                assert_eq!(node.newer, L::LinkType::MAX);
                assert_eq!(node.older, L::LinkType::MAX);
            }
        } else {
            assert_ne!(self.newest, self.oldest);

            {
                let newest = unsafe { self.map.bucket(self.newest.into_usize()).as_ref() };
                assert_eq!(newest.newer, L::LinkType::MAX);
                assert_ne!(newest.older, L::LinkType::MAX);
            }

            {
                let oldest = unsafe { self.map.bucket(self.oldest.into_usize()).as_ref() };
                assert_ne!(oldest.newer, L::LinkType::MAX);
                assert_eq!(oldest.older, L::LinkType::MAX);
            }
        }

        let mut seen = hashbrown::HashSet::with_capacity_and_hasher(
            self.len(),
            ahash::random_state::RandomState::with_seeds(12, 34, 56, 78),
        );
        let mut previous_index = L::LinkType::MAX;
        let mut index = self.newest;
        loop {
            assert!(seen.insert(index.into_usize()));
            let node = unsafe { self.map.bucket(index.into_usize()).as_ref() };
            assert_eq!(node.newer, previous_index);

            previous_index = index;
            index = node.older;

            if index == L::LinkType::MAX {
                break;
            }
        }

        assert_eq!(seen.len(), self.map.len());
        assert_eq!(
            Self::memory_usage_for_memory_budget(self.memory_usage()),
            self.memory_usage()
        );
    }

    /// Creates a new map with a given `limiter` and `hasher`.
    pub const fn with_hasher(limiter: L, hasher: S) -> Self {
        LruMap {
            hasher,
            map: RawTable::new(),
            newest: L::LinkType::MAX,
            oldest: L::LinkType::MAX,
            limiter,
        }
    }

    /// Ensures that at least `additional` items can be inserted into the table without
    /// reallocation.
    ///
    /// # Panics
    ///
    /// Will panic if the total number of elements is too big or the memory couldn't be allocated.
    pub fn reserve_or_panic(&mut self, additional: usize) {
        let capacity = self.len() + additional;
        if self.guaranteed_capacity() >= capacity {
            return;
        }

        if !self.try_grow(capacity) {
            // TODO: A more descriptive error message.
            panic!("failed to reserve space for extra elements");
        }
    }

    /// Returns the current guaranteed capacity of the map.
    ///
    /// This specifies how many elements the map is guaranteed to be able to hold without allocating
    /// any memory. This is a lower bound; it's possible that the map can hold more elements than
    /// this.
    ///
    /// This value will change as elements are added and removed. In particular, in might go *down*
    /// when an element is removed from the map.
    ///
    /// This is independent of the cap imposed by the limiter.
    pub fn guaranteed_capacity(&self) -> usize {
        self.map.capacity()
    }

    /// A convenience helper to call [`crate::buckets_for_capacity`].
    fn buckets_for_capacity(capacity: usize) -> Option<usize> {
        buckets_for_capacity(capacity, L::LinkType::MAX.into_usize())
    }

    /// Returns how much memory will be used by a map that contains a given number of `buckets`.
    ///
    /// Will return `None` if such map cannot be created.
    //
    // Mostly copied from `hashbrown` with minor modifications.
    // TODO: Have `hashbrown` export this?
    fn memory_usage_for_buckets(buckets: usize) -> Option<usize> {
        if buckets == 0 {
            return Some(0);
        }

        let entry_layout = core::alloc::Layout::new::<Entry<K, V, L::LinkType>>();
        let size = entry_layout.size();
        let ctrl_align = if entry_layout.align() > GROUP_WIDTH {
            entry_layout.align()
        } else {
            GROUP_WIDTH
        };

        let ctrl_offset = size.checked_mul(buckets)?.checked_add(ctrl_align - 1)? & !(ctrl_align - 1);

        let len = ctrl_offset.checked_add(buckets + GROUP_WIDTH)?;
        if len > isize::MAX as usize - (ctrl_align - 1) {
            return None;
        }

        Some(len)
    }

    /// Returns an estimated memory usage this map will have with a given `memory_budget`.
    pub fn memory_usage_for_memory_budget(memory_budget: usize) -> usize {
        let mut memory_usage = 0;
        let mut capacity = 1;
        while let Some(buckets) = Self::buckets_for_capacity(capacity) {
            match Self::memory_usage_for_buckets(buckets) {
                Some(usage) if usage <= memory_budget => memory_usage = usage,
                _ => break,
            }
            capacity = buckets + 1;
        }

        memory_usage
    }

    /// Returns the current memory usage of the map, in bytes.
    pub fn memory_usage(&self) -> usize {
        self.map.allocation_info().1.size()
    }

    /// Returns a pointer to the underlying memory allocation.
    #[doc(hidden)]
    pub fn allocation_pointer(&self) -> *const u8 {
        let (ptr, layout) = self.map.allocation_info();
        if layout.size() == 0 {
            core::ptr::null()
        } else {
            ptr.as_ptr() as *const u8
        }
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns whether the map is empty or not.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// A convenience method to calculate the hash for a given `key`.
    #[inline]
    fn hash_key<T>(&self, key: &T) -> u64
    where
        T: Hash + ?Sized,
    {
        let mut hasher = self.hasher.build_hasher();
        key.hash(&mut hasher);
        hasher.finish()
    }

    /// Returns a reference to the value for a given key and promotes that element to be the most
    /// recently used.
    #[inline]
    pub fn get(&mut self, key: &(impl Hash + PartialEq<K> + ?Sized)) -> Option<&mut V> {
        let hash = self.hash_key(key);
        self.get_by_hash(hash, |existing_key, _| *key == *existing_key)
    }

    /// Returns a reference to the value for a given `hash` and for which `is_eq` returns `true`.
    /// Promotes that element to be the most recently used.
    #[inline]
    pub fn get_by_hash(&mut self, hash: u64, mut is_eq: impl FnMut(&K, &V) -> bool) -> Option<&mut V> {
        let bucket = self.map.find(hash, |entry| is_eq(&entry.key, &entry.value))?;

        // SAFETY: Promoting an existing bucket is always safe.
        unsafe {
            self.promote_existing_bucket(&bucket);
        }

        // SAFETY: Bucket always exists.
        let entry = unsafe { bucket.as_mut() };
        Some(&mut entry.value)
    }

    /// Tries to get the value for a given `key` or insert a new value if there's no element
    /// in the map which matches that `key`.
    ///
    /// If present the element will be promoted to be the most recently used.
    #[inline]
    pub fn get_or_insert<'a>(
        &mut self,
        key: (impl Into<L::KeyToInsert<'a>> + Hash + PartialEq<K> + ?Sized),
        get: impl FnOnce() -> V,
    ) -> Option<&mut V>
    where
        L::KeyToInsert<'a>: Hash + PartialEq<K>,
    {
        match self.get_or_insert_fallible(key, || Ok(get())) {
            Ok(value) => value,
            Err(()) => unreachable!(),
        }
    }

    /// Same as [`Self::get_or_insert`], just with a fallible callback.
    #[inline]
    pub fn get_or_insert_fallible<'a, E>(
        &mut self,
        key: (impl Into<L::KeyToInsert<'a>> + Hash + PartialEq<K> + ?Sized),
        get: impl FnOnce() -> Result<V, E>,
    ) -> Result<Option<&mut V>, E>
    where
        L::KeyToInsert<'a>: Hash + PartialEq<K>,
    {
        #[allow(clippy::needless_lifetimes)]
        #[inline(always)]
        unsafe fn cast_lifetime<'a, 'b, T>(x: &'a mut T) -> &'b mut T {
            core::mem::transmute(x)
        }

        let hash = self.hash_key(&key);
        if let Some(value) = self.get_by_hash(hash, |existing_key, _| key == *existing_key) {
            // SAFETY: This is safe and is only necessary because of borrow checker's limitations.
            // (With RUSTFLAGS="-Z polonius=y" this line can be removed and the code will compile.)
            let value = unsafe { cast_lifetime(value) };
            return Ok(Some(value));
        }

        let value = get()?;
        if self.insert(key.into(), value) {
            debug_assert_ne!(self.newest, L::LinkType::MAX);

            // SAFETY: After inserting a new element the `newest` is always a valid index.
            unsafe {
                let bucket = self.map.bucket(self.newest.into_usize());
                Ok(Some(&mut bucket.as_mut().value))
            }
        } else {
            Ok(None)
        }
    }

    /// Returns a reference to the value for a given key. Does not change the order of the elements.
    #[inline]
    pub fn peek<'a>(&'a self, key: &(impl Hash + PartialEq<K> + ?Sized)) -> Option<&'a V> {
        let hash = self.hash_key(&key);
        self.peek_by_hash(hash, |existing_key, _| *key == *existing_key)
    }

    /// Returns a mutable reference to the value for a given key. Does not change the order of the elements.
    #[inline]
    pub fn peek_mut<'a>(&'a mut self, key: &(impl Hash + PartialEq<K> + ?Sized)) -> Option<&'a mut V> {
        let hash = self.hash_key(&key);
        self.peek_by_hash_mut(hash, |existing_key, _| *key == *existing_key)
    }

    /// Returns a reference to the value for a given `hash` and for which `is_eq` returns `true`.
    /// Does not change the order of the elements.
    #[inline]
    pub fn peek_by_hash(&self, hash: u64, mut is_eq: impl FnMut(&K, &V) -> bool) -> Option<&V> {
        let bucket = self.map.find(hash, |entry| is_eq(&entry.key, &entry.value))?;

        // SAFETY: Bucket always exists.
        let entry = unsafe { bucket.as_ref() };
        Some(&entry.value)
    }

    /// Returns a mutable reference to the value for a given `hash` and for which `is_eq` returns `true`.
    /// Does not change the order of the elements.
    #[inline]
    pub fn peek_by_hash_mut(&mut self, hash: u64, mut is_eq: impl FnMut(&K, &V) -> bool) -> Option<&mut V> {
        let bucket = self.map.find(hash, |entry| is_eq(&entry.key, &entry.value))?;

        // SAFETY: Bucket always exists.
        let entry = unsafe { bucket.as_mut() };
        Some(&mut entry.value)
    }

    /// Removes an element from the map.
    pub fn remove(&mut self, key: &(impl Hash + PartialEq<K> + ?Sized)) -> Option<V> {
        let hash = self.hash_key(&key);
        let bucket = self.map.find(hash, |entry| *key == entry.key)?;

        // SAFETY: Bucket always exists.
        let entry = unsafe { self.remove_bucket(bucket) };

        Some(entry.value)
    }

    /// Inserts a new element into the map.
    ///
    /// Can fail if the element is rejected by the limiter or if we fail to grow an empty map.
    ///
    /// Returns `true` if the element was inserted; `false` otherwise.
    #[inline]
    pub fn insert<'a>(&mut self, key: L::KeyToInsert<'a>, mut value: V) -> bool
    where
        L::KeyToInsert<'a>: Hash + PartialEq<K>,
    {
        let hash = self.hash_key(&key);
        if let Some(bucket) = self.map.find(hash, |entry| key == entry.key) {
            // This key already exists in the map; try to replace it.
            let can_replace = {
                // SAFETY: Bucket exists since we just found it.
                let entry = unsafe { bucket.as_mut() };
                self.limiter
                    .on_replace(self.map.len(), &mut entry.key, key, &mut entry.value, &mut value)
            };

            if !can_replace {
                // Even if we remove the old item we still can't afford to add the new one;
                // just remove the old item and bail out.

                // SAFETY: Bucket exists since we just found it.
                unsafe { self.remove_bucket_noinline(bucket) };
                return false;
            } else {
                // SAFETY: Bucket exists since we just found it.
                unsafe {
                    let old_value = core::mem::replace(&mut bucket.as_mut().value, value);
                    self.promote_existing_bucket(&bucket);
                    core::mem::drop(old_value);
                }
            }
        } else {
            let (key, value) = match self.limiter.on_insert(self.map.len(), key, value) {
                Some(key_value) => key_value,
                None => {
                    // The new item wouldn't fit even if the map's empty.
                    return false;
                }
            };

            if !self.map.is_empty() && self.limiter.is_over_the_limit(self.map.len() + 1) {
                // We'll be over the limit after inserting this new element,
                // so we know we will have to pop at least one old element.

                self.pop_oldest();
            }

            let was_inserted = if self.map.is_empty() {
                // SAFETY: Map is empty so it's safe to call this.
                unsafe { self.insert_into_empty_map(hash, key, value) }
            } else {
                // SAFETY: Map is not empty so it's safe to call this.
                unsafe { self.insert_into_new_bucket(hash, key, value) }
            };

            if !was_inserted {
                return false;
            }
        }

        if self.limiter.is_over_the_limit(self.map.len()) {
            // If the map's limited not by the raw length then we can end up here.
            self.pop_until_under_the_limit();
        }

        !self.is_empty()
    }

    /// Clears the map.
    pub fn clear(&mut self) {
        self.oldest = L::LinkType::MAX;
        self.newest = L::LinkType::MAX;
        self.map.clear();
        self.limiter.on_cleared();
    }

    /// Removes the least recently accessed element and returns it.
    #[inline]
    pub fn pop_oldest(&mut self) -> Option<(K, V)> {
        if self.is_empty() {
            return None;
        }

        // SAFETY: Map is not empty so at least one bucket must exist.
        let mut oldest_entry = unsafe {
            let oldest_bucket = self.map.bucket(self.oldest.into_usize());
            self.map.remove(oldest_bucket)
        };
        debug_assert_eq!(oldest_entry.older, L::LinkType::MAX);

        self.oldest = oldest_entry.newer;
        if self.map.is_empty() {
            debug_assert_eq!(self.oldest, L::LinkType::MAX);
            self.newest = L::LinkType::MAX;
        } else {
            // SAFETY: Map is still not empty so the oldest bucket must have had a link to a newer
            // bucket.
            unsafe {
                self.map.bucket(oldest_entry.newer.into_usize()).as_mut().older = L::LinkType::MAX;
            }
        }

        self.limiter.on_removed(&mut oldest_entry.key, &mut oldest_entry.value);
        Some((oldest_entry.key, oldest_entry.value))
    }

    /// Pops elements from the map until we're not over the limit anymore.
    #[inline(never)]
    fn pop_until_under_the_limit(&mut self) {
        loop {
            if self.pop_oldest().is_none() {
                // We're empty and yet we're still over the limit?
                //
                // Technically this shouldn't happen, but it is possible to trigger
                // using a custom limiter, so we handle it.
                break;
            }

            if !self.limiter.is_over_the_limit(self.map.len()) {
                break;
            }
        }
    }

    /// Removes the most recently accessed element and returns it.
    pub fn pop_newest(&mut self) -> Option<(K, V)> {
        if self.is_empty() {
            return None;
        }

        // SAFETY: Map is not empty so at least one bucket must exist.
        let mut newest_entry = unsafe {
            let newest_bucket = self.map.bucket(self.newest.into_usize());
            self.map.remove(newest_bucket)
        };
        debug_assert_eq!(newest_entry.newer, L::LinkType::MAX);

        self.newest = newest_entry.older;
        if self.map.is_empty() {
            debug_assert_eq!(self.newest, L::LinkType::MAX);
            self.oldest = L::LinkType::MAX;
        } else {
            // SAFETY: Map is still not empty so the newest bucket must have had a link to an older
            // bucket.
            unsafe {
                self.map.bucket(newest_entry.older.into_usize()).as_mut().newer = L::LinkType::MAX;
            }
        }

        self.limiter.on_removed(&mut newest_entry.key, &mut newest_entry.value);
        Some((newest_entry.key, newest_entry.value))
    }

    /// Returns the most recently used (inserted or accessed) element of the map. Does not change
    /// the order of the elements.
    pub fn peek_newest(&self) -> Option<(&K, &V)> {
        if self.newest == L::LinkType::MAX {
            return None;
        }

        // SAFETY: The index to the newest element is always valid.
        unsafe {
            let entry = self.map.bucket(self.newest.into_usize()).as_ref();
            Some((&entry.key, &entry.value))
        }
    }

    /// Returns the least recently used (inserted or accessed) element of the map. Does not change
    /// the order of the elements.
    pub fn peek_oldest(&self) -> Option<(&K, &V)> {
        if self.oldest == L::LinkType::MAX {
            return None;
        }

        // SAFETY: The index to the oldest element is always valid.
        unsafe {
            let entry = self.map.bucket(self.oldest.into_usize()).as_ref();
            Some((&entry.key, &entry.value))
        }
    }

    /// Promotes an existing bucket as the most recent.
    ///
    /// # Safety
    ///
    /// - The bucket must exist within the map; no dangling links are allowed.
    #[inline]
    unsafe fn promote_existing_bucket(&mut self, bucket: &Bucket<Entry<K, V, L::LinkType>>) {
        self.assert_not_empty();

        let index = L::LinkType::from_usize(self.map.bucket_index(bucket));
        if self.newest == index {
            // Already the newest element; no action necessary.
            return;
        }

        // It's not the newest element already, so the links need to be adjusted.

        if self.oldest != index {
            // Break the link to this element's older neighbor.
            self.map.bucket(bucket.as_ref().older.into_usize()).as_mut().newer = bucket.as_ref().newer;
        } else {
            // This element's the oldest.
            self.oldest = bucket.as_ref().newer;
        }

        // Break the link to this element's newer neighbor.
        self.map.bucket(bucket.as_ref().newer.into_usize()).as_mut().older = bucket.as_ref().older;
        bucket.as_mut().newer = L::LinkType::MAX;

        // Add a link between the previous newest element and this element.
        self.map.bucket(self.newest.into_usize()).as_mut().newer = index;
        bucket.as_mut().older = self.newest;

        // Finally set this element as the newest element.
        self.newest = index;
    }

    /// Updates the links for a newly inserted element.
    ///
    /// # Safety
    ///
    /// - Must be called right after inserting a new element into the map.
    /// - The map must have at least two elements.
    /// - The entry must already point to the previous newest element in the map.
    #[inline]
    unsafe fn finish_inserting_bucket(&mut self, bucket: Bucket<Entry<K, V, L::LinkType>>) {
        debug_assert_ne!(bucket.as_ref().older, L::LinkType::MAX);
        debug_assert_eq!(bucket.as_ref().newer, L::LinkType::MAX);
        debug_assert!(self.map.len() >= 2);

        let index = L::LinkType::from_usize(self.map.bucket_index(&bucket));
        self.map.bucket(self.newest.into_usize()).as_mut().newer = index;
        bucket.as_mut().older = self.newest;
        self.newest = index;
    }

    /// Same as `remove_bucket`.
    #[inline(never)]
    unsafe fn remove_bucket_noinline(&mut self, bucket: Bucket<Entry<K, V, L::LinkType>>) {
        self.remove_bucket(bucket);
    }

    /// Removes an existing bucket from the map.
    ///
    /// # Safety
    ///
    /// The bucket must exist within the map.
    #[inline]
    unsafe fn remove_bucket(&mut self, bucket: Bucket<Entry<K, V, L::LinkType>>) -> Entry<K, V, L::LinkType> {
        self.assert_not_empty();
        let index = L::LinkType::from_usize(self.map.bucket_index(&bucket));
        let mut entry = self.map.remove(bucket);

        if self.newest == index {
            self.newest = entry.older;
        } else {
            self.map.bucket(entry.newer.into_usize()).as_mut().older = entry.older;
        }

        if self.oldest == index {
            self.oldest = entry.newer;
        } else {
            self.map.bucket(entry.older.into_usize()).as_mut().newer = entry.newer;
        }

        self.limiter.on_removed(&mut entry.key, &mut entry.value);
        entry
    }

    /// Inserts a new element into the map.
    ///
    /// # Safety
    ///
    /// The map must be empty.
    #[inline(never)]
    #[cold]
    #[must_use]
    unsafe fn insert_into_empty_map(&mut self, hash: u64, key: K, value: V) -> bool {
        self.assert_empty();

        if self.map.capacity() == 0 && !self.try_grow(1) {
            return false;
        }

        assert!(self.map.buckets() < L::LinkType::MAX.into_usize());

        let entry = Entry {
            key,
            value,
            older: L::LinkType::MAX,
            newer: L::LinkType::MAX,
        };
        let bucket = self.map.insert_no_grow(hash, entry);
        let index = L::LinkType::from_usize(self.map.bucket_index(&bucket));

        self.oldest = index;
        self.newest = index;

        true
    }

    /// Inserts a new element into a new bucket.
    ///
    /// # Safety
    ///
    /// - The map must not be empty.
    #[inline]
    #[must_use]
    unsafe fn insert_into_new_bucket(&mut self, hash: u64, key: K, value: V) -> bool {
        self.assert_not_empty();

        let entry = Entry {
            key,
            value,
            older: self.newest,
            newer: L::LinkType::MAX,
        };
        match self.map.try_insert_no_grow(hash, entry) {
            Ok(bucket) => {
                // SAFETY: We've just inserted this bucket, so it's safe to call this.
                unsafe {
                    self.finish_inserting_bucket(bucket);
                }

                true
            }
            Err(entry) => {
                // SAFETY: The map's not empty so it's safe to call this.
                unsafe {
                    // Not enough space; grow the map and *then* insert.
                    self.try_grow_and_insert(hash, entry.key, entry.value)
                }
            }
        }
    }

    /// Grows the map and inserts a given item.
    ///
    /// # Safety
    ///
    /// - The map must not be empty.
    #[inline(never)]
    #[cold]
    unsafe fn try_grow_and_insert(&mut self, hash: u64, mut key: K, mut value: V) -> bool {
        self.assert_not_empty();

        let new_capacity = self.len() + 1;
        if self.try_grow(new_capacity) {
            let entry = Entry {
                key,
                value,
                older: self.newest,
                newer: L::LinkType::MAX,
            };

            // SAFETY: `try_grow` was successful so it is possible to insert at least one element.
            unsafe {
                let bucket = self.map.insert_no_grow(hash, entry);
                self.finish_inserting_bucket(bucket);
            }

            true
        } else {
            // Growing the map has failed. We must insert the new element without growing the map.
            loop {
                // This might take a few tries depending on which exact bucket
                // the new entry will land on. In the worst case we might have
                // to remove more than one existing element.
                self.pop_oldest();

                if self.is_empty() {
                    return self.insert_into_empty_map(hash, key, value);
                }

                let entry = Entry {
                    key,
                    value,
                    older: self.newest,
                    newer: L::LinkType::MAX,
                };

                let full_capacity = full_capacity_for_buckets(self.map.buckets());
                if self.len() < full_capacity / 2 {
                    // We're at a threshold when it's worth it to just rehash the map.
                    if !self.rehash_in_place() {
                        // This can only fail if we failed to allocate memory.
                        //
                        // We're screwed; just give up.
                        return false;
                    }

                    assert!(self.map.capacity() > self.map.len());

                    // SAFETY: We've just checked that there is still free capacity.
                    unsafe {
                        let bucket = self.map.insert_no_grow(hash, entry);
                        self.finish_inserting_bucket(bucket);
                    }

                    return true;
                }

                match self.map.try_insert_no_grow(hash, entry) {
                    Ok(bucket) => {
                        // SAFETY: We've just inserted this bucket, so it's safe to call this.
                        unsafe {
                            self.finish_inserting_bucket(bucket);
                        }

                        return true;
                    }
                    Err(entry) => {
                        key = entry.key;
                        value = entry.value;

                        continue;
                    }
                }
            }
        }
    }

    /// Rehashes the map in place.
    ///
    /// Mostly used to free up any excess capacity that's being hogged by deleted entries.
    #[inline(never)]
    #[cold]
    fn rehash_in_place(&mut self) -> bool {
        if self.is_empty() {
            // The map's empty so we don't have to update any links.
            // Just trigger a rehash if necessary.
            self.map.reserve(1, |_| unreachable!());
            return true;
        }

        let bucket_count = self.map.buckets();
        let mut buffer = alloc::vec::Vec::<core::mem::MaybeUninit<L::LinkType>>::new();
        if buffer.try_reserve_exact(bucket_count * 2).is_err() {
            return false;
        }

        // SAFETY: The inner type is `MaybeUninit`, so this is safe.
        unsafe {
            buffer.set_len(bucket_count * 2);
        }

        let (older_to_old_index_map, index_map) = buffer.split_at_mut(bucket_count);

        let old_oldest = core::mem::replace(&mut self.oldest, L::LinkType::MAX);
        let old_newest = core::mem::replace(&mut self.newest, L::LinkType::MAX);

        // SAFETY: We drop the iterator before the lifetime of the map ends,
        //         and we only fetch values it returns.
        unsafe {
            let mut iter = self.map.iter();
            while let Some(old_bucket) = iter.next() {
                let old_index = self.map.bucket_index(&old_bucket);
                let entry = old_bucket.as_ref();
                if entry.older != L::LinkType::MAX {
                    // Since the index of each entry is stored implicitly by hashbrown
                    // as an offset from the start of the table we won't have access to
                    // it after the map is rehashed, so save those indexes now.
                    //
                    // We use the link to the older entry as a key here since it's going
                    // to be unique anyway.
                    older_to_old_index_map[entry.older.into_usize()] =
                        core::mem::MaybeUninit::new(L::LinkType::from_usize(old_index));
                }
            }
        }

        // Trigger a rehash.
        {
            // Protect against a panic in the hash function.
            struct Guard<'a, K, V, L>
            where
                L: Limiter<K, V>,
            {
                map: &'a mut RawTable<Entry<K, V, L::LinkType>>,
                limiter: &'a mut L,
            }

            impl<'a, K, V, L> Drop for Guard<'a, K, V, L>
            where
                L: Limiter<K, V>,
            {
                fn drop(&mut self) {
                    // Clear the whole map if this is suddenly dropped.
                    //
                    // If we panic during a rehash some of the elements might have been dropped.
                    // This will mess up our links, so just clear the whole map to make sure
                    // that we can't trigger any unsoundness.
                    self.map.clear();
                    self.limiter.on_cleared();
                }
            }

            let guard = Guard {
                map: &mut self.map,
                limiter: &mut self.limiter,
            };

            // Unfortunately hashbrown doesn't expose the ability to directly trigger a rehash,
            // but we can force it to do it through 'reserve'. It's a hack, but it works.
            let extra_capacity = full_capacity_for_buckets(bucket_count) / 2 - guard.map.len();
            let hasher = &self.hasher;
            guard.map.reserve(extra_capacity, |entry| {
                let mut hasher = hasher.build_hasher();
                entry.key.hash(&mut hasher);
                hasher.finish()
            });

            core::mem::forget(guard);
        }

        debug_assert_eq!(self.map.buckets(), bucket_count); // Make sure it was actually a rehash.

        // SAFETY: We drop the iterator before the lifetime of the map ends,
        //         we only fetch values it returns, and we only access elements
        //         in the `older_to_old_index_map` which were initialized in the previous loop.
        unsafe {
            // Now go through the rehashed map and build a map of old indexes to new indexes.
            let mut iter = self.map.iter();
            while let Some(new_bucket) = iter.next() {
                let new_index = self.map.bucket_index(&new_bucket);
                let entry = new_bucket.as_ref();
                let old_index = if entry.older == L::LinkType::MAX {
                    old_oldest
                } else {
                    older_to_old_index_map[entry.older.into_usize()].assume_init()
                }
                .into_usize();

                index_map[old_index] = core::mem::MaybeUninit::new(L::LinkType::from_usize(new_index));
            }
        }

        // SAFETY: We drop the iterator before the lifetime of the map ends,
        //         we only fetch values it returns, and we only access elements
        //         in the `index_map` which were initialized in the previous loop.
        unsafe {
            // Adjust all of the links in the new map.
            let mut iter = self.map.iter();
            while let Some(new_bucket) = iter.next() {
                let entry = new_bucket.as_mut();

                if entry.older != L::LinkType::MAX {
                    entry.older = index_map[entry.older.into_usize()].assume_init();
                }

                if entry.newer != L::LinkType::MAX {
                    entry.newer = index_map[entry.newer.into_usize()].assume_init()
                }
            }

            debug_assert_ne!(old_oldest, L::LinkType::MAX);
            debug_assert_ne!(old_newest, L::LinkType::MAX);

            self.oldest = index_map[old_oldest.into_usize()].assume_init();
            self.newest = index_map[old_newest.into_usize()].assume_init();
        }

        true
    }

    /// Tries to grow the map in size.
    ///
    /// This rehashes and reindexes the map, updating all of the links between nodes.
    fn try_grow(&mut self, mut required_length: usize) -> bool {
        let mut new_bucket_count = match Self::buckets_for_capacity(required_length) {
            Some(new_bucket_count) => new_bucket_count,
            None => {
                // The capacity's too big; bail.
                return false;
            }
        };

        let old_bucket_count = self.map.buckets();
        debug_assert!(old_bucket_count < L::LinkType::MAX.into_usize());

        if new_bucket_count <= old_bucket_count {
            // The bucket count's less or unchanged.
            let full_capacity = full_capacity_for_buckets(old_bucket_count);
            if required_length <= full_capacity / 2 {
                // Still plenty of space; it's just taken by all of the deleted entries.
                return self.rehash_in_place();
            }

            // Force the map to grow.
            required_length = full_capacity_for_buckets(old_bucket_count * 2);
            new_bucket_count = match Self::buckets_for_capacity(required_length) {
                Some(new_bucket_count) => new_bucket_count,
                None => {
                    // The capacity's too big; bail.
                    return false;
                }
            };
        }

        debug_assert!(new_bucket_count > old_bucket_count);

        let new_memory_usage = match Self::memory_usage_for_buckets(new_bucket_count) {
            Some(new_memory_usage) => new_memory_usage,
            None => {
                // This should never trigger.
                return false;
            }
        };

        if !self.limiter.on_grow(new_memory_usage) {
            // We're not allowed to grow anymore.
            return false;
        }

        let new_map = match RawTable::try_with_capacity(required_length) {
            Ok(new_map) => new_map,
            Err(_) => return false,
        };

        debug_assert_eq!(new_map.buckets(), new_bucket_count);
        if new_map.buckets() >= L::LinkType::MAX.into_usize() {
            // This should never happen since we already checked it through `buckets_for_capacity`.
            debug_assert!(false, "unreachable");
            return false;
        }

        if self.is_empty() {
            // The map's empty so no links need to be adjusted.
            self.map = new_map;
            return true;
        }

        let mut index_map = alloc::vec::Vec::<core::mem::MaybeUninit<L::LinkType>>::new();
        if index_map.try_reserve_exact(old_bucket_count).is_err() {
            return false;
        }

        let mut old_map = core::mem::replace(&mut self.map, new_map);
        let old_oldest = core::mem::replace(&mut self.oldest, L::LinkType::MAX);
        let old_newest = core::mem::replace(&mut self.newest, L::LinkType::MAX);

        unsafe {
            index_map.set_len(old_bucket_count);

            // Move all of the items into the new map and build a mapping of indexes.
            let mut iter = old_map.iter();
            while let Some(old_bucket) = iter.next() {
                let old_index = old_map.bucket_index(&old_bucket);
                let entry = old_map.remove(old_bucket);
                let hash = self.hash_key(&entry.key);

                let new_bucket = self.map.insert_no_grow(hash, entry);
                let new_index = self.map.bucket_index(&new_bucket);

                index_map[old_index] = core::mem::MaybeUninit::new(L::LinkType::from_usize(new_index));
            }
        }

        unsafe {
            // Adjust all of the links in the new map.
            let mut iter = self.map.iter();
            while let Some(new_bucket) = iter.next() {
                let entry = new_bucket.as_mut();

                if entry.older != L::LinkType::MAX {
                    entry.older = index_map[entry.older.into_usize()].assume_init();
                }

                if entry.newer != L::LinkType::MAX {
                    entry.newer = index_map[entry.newer.into_usize()].assume_init()
                }
            }

            debug_assert_ne!(old_oldest, L::LinkType::MAX);
            debug_assert_ne!(old_newest, L::LinkType::MAX);

            self.oldest = index_map[old_oldest.into_usize()].assume_init();
            self.newest = index_map[old_newest.into_usize()].assume_init();
        }

        true
    }

    /// An iterator over all of the elements in the most recently used order.
    pub fn iter(&self) -> Iter<K, V, L> {
        Iter {
            map: &self.map,
            newest: self.newest,
            oldest: self.oldest,
            remaining: self.len(),
        }
    }

    /// A mutable iterator over all of the elements in the most recently used order.
    pub fn iter_mut(&mut self) -> IterMut<K, V, L> {
        let newest = self.newest;
        let oldest = self.oldest;
        let remaining = self.len();
        IterMut {
            map: &mut self.map,
            newest,
            oldest,
            remaining,
        }
    }

    /// Drains the map of all of its elements in the most recently used order.
    ///
    /// When the iterator is dropped the map will be automatically cleared.
    pub fn drain(&mut self) -> Drain<K, V, L, S> {
        Drain { map: self }
    }

    /// Returns a reference to the map's limiter.
    pub fn limiter(&self) -> &L {
        &self.limiter
    }

    /// Returns a mutable reference to the map's limiter.
    pub fn limiter_mut(&mut self) -> &mut L {
        &mut self.limiter
    }
}

/// An iterator for the LRU map.
pub struct Iter<'a, K, V, L>
where
    L: Limiter<K, V>,
{
    map: &'a RawTable<Entry<K, V, L::LinkType>>,
    newest: L::LinkType,
    oldest: L::LinkType,
    remaining: usize,
}

impl<'a, K, V, L> Iterator for Iter<'a, K, V, L>
where
    L: Limiter<K, V>,
{
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        self.remaining -= 1;

        unsafe {
            let bucket = self.map.bucket(self.newest.into_usize());
            let entry = bucket.as_ref();
            self.newest = entry.older;

            Some((&entry.key, &entry.value))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V, L> DoubleEndedIterator for Iter<'a, K, V, L>
where
    L: Limiter<K, V>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        self.remaining -= 1;

        unsafe {
            let bucket = self.map.bucket(self.oldest.into_usize());
            let entry = bucket.as_ref();
            self.oldest = entry.newer;

            Some((&entry.key, &entry.value))
        }
    }
}

impl<'a, K, V, L> ExactSizeIterator for Iter<'a, K, V, L> where L: Limiter<K, V> {}

/// An mutable iterator for the LRU map, values are mutable.
pub struct IterMut<'a, K, V, L>
where
    L: Limiter<K, V>,
{
    map: &'a mut RawTable<Entry<K, V, L::LinkType>>,
    newest: L::LinkType,
    oldest: L::LinkType,
    remaining: usize,
}

impl<'a, K, V, L> Iterator for IterMut<'a, K, V, L>
where
    L: Limiter<K, V>,
{
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        self.remaining -= 1;

        unsafe {
            let bucket = self.map.bucket(self.newest.into_usize());
            let entry = bucket.as_mut();
            self.newest = entry.older;

            Some((&entry.key, &mut entry.value))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V, L> DoubleEndedIterator for IterMut<'a, K, V, L>
where
    L: Limiter<K, V>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        self.remaining -= 1;

        unsafe {
            let bucket = self.map.bucket(self.oldest.into_usize());
            let entry = bucket.as_mut();
            self.oldest = entry.newer;

            Some((&entry.key, &mut entry.value))
        }
    }
}

impl<'a, K, V, L> ExactSizeIterator for IterMut<'a, K, V, L> where L: Limiter<K, V> {}

/// A drain iterator for the LRU map.
pub struct Drain<'a, K, V, L, S>
where
    K: PartialEq + Hash,
    L: Limiter<K, V>,
    S: BuildHasher,
{
    map: &'a mut LruMap<K, V, L, S>,
}

impl<'a, K, V, L, S> Iterator for Drain<'a, K, V, L, S>
where
    K: PartialEq + Hash,
    S: BuildHasher,
    L: Limiter<K, V>,
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.map.pop_newest()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.map.len();
        (remaining, Some(remaining))
    }
}

impl<'a, K, V, L, S> DoubleEndedIterator for Drain<'a, K, V, L, S>
where
    K: PartialEq + Hash,
    S: BuildHasher,
    L: Limiter<K, V>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.map.pop_oldest()
    }
}

impl<'a, K, V, L, S> Drop for Drain<'a, K, V, L, S>
where
    K: PartialEq + Hash,
    S: BuildHasher,
    L: Limiter<K, V>,
{
    fn drop(&mut self) {
        self.map.clear();
    }
}

impl<'a, K, V, L, S> ExactSizeIterator for Drain<'a, K, V, L, S>
where
    K: PartialEq + Hash,
    S: BuildHasher,
    L: Limiter<K, V>,
{
}

#[cfg(test)]
mod tests {
    pub use super::*;

    extern crate std;
    use std::string::String;
    use std::{vec, vec::Vec};

    fn to_vec<K, V, L, S>(lru: &LruMap<K, V, L, S>) -> Vec<(K, V)>
    where
        K: Copy + PartialEq + Hash,
        V: Copy,
        L: Limiter<K, V>,
        S: BuildHasher,
    {
        lru.iter().map(|(key, value)| (*key, *value)).collect()
    }

    #[derive(Copy, Clone, Debug)]
    pub struct ByValue {
        limit: usize,
        cost: usize,
        length: usize,
    }

    impl ByValue {
        fn new(limit: usize) -> Self {
            ByValue {
                limit,
                cost: 0,
                length: 0,
            }
        }
    }

    impl Limiter<usize, usize> for ByValue {
        type KeyToInsert<'a> = usize;
        type LinkType = usize;

        fn is_over_the_limit(&self, length: usize) -> bool {
            assert_eq!(length, self.length);
            self.cost > self.limit
        }

        fn on_insert<'a>(&mut self, length: usize, key: usize, value: usize) -> Option<(usize, usize)> {
            assert_eq!(length, self.length);
            if value > self.limit {
                return None;
            }

            self.cost += value;
            self.length += 1;
            Some((key, value))
        }

        fn on_replace(
            &mut self,
            length: usize,
            _: &mut usize,
            _: usize,
            old_value: &mut usize,
            new_value: &mut usize,
        ) -> bool {
            assert_eq!(length, self.length);
            if *new_value > self.limit {
                return false;
            }

            self.cost += *new_value - *old_value;
            true
        }

        fn on_cleared(&mut self) {
            self.cost = 0;
            self.length = 0;
        }

        fn on_removed(&mut self, _: &mut usize, value: &mut usize) {
            self.cost -= *value;
            self.length -= 1;
        }

        fn on_grow(&mut self, _: usize) -> bool {
            true
        }
    }

    impl Limiter<usize, (usize, usize)> for ByValue {
        type KeyToInsert<'a> = usize;
        type LinkType = usize;

        fn is_over_the_limit(&self, _: usize) -> bool {
            self.cost > self.limit
        }

        fn on_insert<'a>(&mut self, _: usize, key: usize, value: (usize, usize)) -> Option<(usize, (usize, usize))> {
            if value.0 > self.limit {
                return None;
            }

            self.cost += value.0;
            Some((key, value))
        }

        fn on_replace(
            &mut self,
            _: usize,
            _: &mut usize,
            _: usize,
            old_value: &mut (usize, usize),
            new_value: &mut (usize, usize),
        ) -> bool {
            if new_value.0 > self.limit {
                return false;
            }

            self.cost += new_value.0 - old_value.0;
            true
        }

        fn on_cleared(&mut self) {
            self.cost = 0;
        }

        fn on_removed(&mut self, _: &mut usize, &mut (value, _): &mut (usize, usize)) {
            self.cost -= value;
        }

        fn on_grow(&mut self, _: usize) -> bool {
            true
        }
    }

    #[derive(Copy, Clone, Debug, Default)]
    pub struct UnlimitedU8;

    impl<K, V> Limiter<K, V> for UnlimitedU8 {
        type KeyToInsert<'a> = K;
        type LinkType = u8;

        fn is_over_the_limit(&self, _: usize) -> bool {
            false
        }

        fn on_insert<'a>(&mut self, _: usize, key: K, value: V) -> Option<(K, V)> {
            Some((key, value))
        }

        fn on_replace(&mut self, _: usize, _: &mut K, _: K, _: &mut V, _: &mut V) -> bool {
            true
        }

        fn on_cleared(&mut self) {}
        fn on_removed(&mut self, _: &mut K, _: &mut V) {}
        fn on_grow(&mut self, _: usize) -> bool {
            true
        }
    }

    #[derive(Copy, Clone, Debug, Default)]
    pub struct UnlimitedU16;

    impl<K, V> Limiter<K, V> for UnlimitedU16 {
        type KeyToInsert<'a> = K;
        type LinkType = u16;

        fn is_over_the_limit(&self, _: usize) -> bool {
            false
        }

        fn on_insert<'a>(&mut self, _: usize, key: K, value: V) -> Option<(K, V)> {
            Some((key, value))
        }

        fn on_replace(&mut self, _: usize, _: &mut K, _: K, _: &mut V, _: &mut V) -> bool {
            true
        }

        fn on_cleared(&mut self) {}
        fn on_removed(&mut self, _: &mut K, _: &mut V) {}
        fn on_grow(&mut self, _: usize) -> bool {
            true
        }
    }

    #[derive(Copy, Clone, Debug, Default)]
    pub struct Manual {
        overflow: bool,
    }

    impl<K, V> Limiter<K, V> for Manual {
        type KeyToInsert<'a> = K;
        type LinkType = usize;

        fn is_over_the_limit(&self, _: usize) -> bool {
            self.overflow
        }

        fn on_insert<'a>(&mut self, _: usize, key: K, value: V) -> Option<(K, V)> {
            Some((key, value))
        }

        fn on_replace(&mut self, _: usize, _: &mut K, _: K, _: &mut V, _: &mut V) -> bool {
            true
        }

        fn on_cleared(&mut self) {}
        fn on_removed(&mut self, _: &mut K, _: &mut V) {}
        fn on_grow(&mut self, _: usize) -> bool {
            true
        }
    }

    #[derive(Copy, Clone, Debug, Default)]
    pub struct WithCustomInsertKey;
    pub struct InsertKey<'a>(&'a str);

    impl<'a> PartialEq<String> for InsertKey<'a> {
        fn eq(&self, rhs: &String) -> bool {
            self.0 == rhs
        }
    }

    impl<'a> core::hash::Hash for InsertKey<'a> {
        fn hash<H>(&self, state: &mut H)
        where
            H: core::hash::Hasher,
        {
            self.0.hash(state)
        }
    }

    impl<V> Limiter<String, V> for WithCustomInsertKey {
        type KeyToInsert<'a> = InsertKey<'a>;
        type LinkType = usize;

        fn is_over_the_limit(&self, _: usize) -> bool {
            false
        }

        fn on_insert<'a>(&mut self, _: usize, key: InsertKey<'a>, value: V) -> Option<(String, V)> {
            Some((String::from(key.0), value))
        }

        fn on_replace<'a>(&mut self, _: usize, _: &mut String, _: InsertKey<'a>, _: &mut V, _: &mut V) -> bool {
            true
        }

        fn on_cleared(&mut self) {}
        fn on_removed(&mut self, _: &mut String, _: &mut V) {}
        fn on_grow(&mut self, _: usize) -> bool {
            true
        }
    }

    #[test]
    fn insert_works() {
        let mut lru = LruMap::new(UnlimitedCompact);
        assert!(lru.is_empty());
        assert_eq!(lru.len(), 0);
        assert_eq!(lru.iter().collect::<Vec<_>>(), vec![]);

        let mut vec = Vec::new();
        for n in 1..=32 {
            lru.insert(n, n * 10);
            vec.insert(0, (n, n * 10));
            assert!(!lru.is_empty());
            assert_eq!(lru.len(), n);
            assert_eq!(to_vec(&lru), vec);
        }

        lru.assert_check_internal_state();
    }

    #[test]
    fn insert_with_limiter_works() {
        let mut lru = LruMap::new(ByLength::new(3));
        lru.insert(1, 10);
        lru.insert(2, 20);
        lru.insert(3, 30);
        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 20), (1, 10)]);

        lru.insert(4, 40);
        assert_eq!(to_vec(&lru), vec![(4, 40), (3, 30), (2, 20)]);

        lru.insert(5, 50);
        assert_eq!(to_vec(&lru), vec![(5, 50), (4, 40), (3, 30)]);

        lru.insert(6, 60);
        assert_eq!(to_vec(&lru), vec![(6, 60), (5, 50), (4, 40)]);

        lru.insert(5, 500);
        assert_eq!(to_vec(&lru), vec![(5, 500), (6, 60), (4, 40)]);

        lru.insert(4, 400);
        assert_eq!(to_vec(&lru), vec![(4, 400), (5, 500), (6, 60)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn limiter_does_not_allow_the_map_to_grow() {
        let mut lru = LruMap::with_seed(ByLength::new(7), [12, 34, 56, 78]);
        assert_eq!(lru.len(), 0);
        assert_eq!(lru.guaranteed_capacity(), 0);
        for n in 9..32 {
            lru.insert(n, n * 10);
        }
        assert_eq!(lru.len(), 7);
        assert_eq!(lru.guaranteed_capacity(), 7);
        lru.assert_check_internal_state();

        let mut lru = LruMap::new(ByLength::new(8));
        for n in 9..32 {
            lru.insert(n, n * 10);
        }
        assert_eq!(lru.len(), 8);
        assert_eq!(lru.guaranteed_capacity(), 14);
        lru.assert_check_internal_state();
    }

    #[test]
    fn get_or_insert_with_limiter_works() {
        let mut lru = LruMap::new(ByLength::new(3));
        assert_eq!(lru.get_or_insert(1, || 10), Some(&mut 10));
        assert_eq!(lru.get_or_insert(2, || 20), Some(&mut 20));
        assert_eq!(lru.get_or_insert(3, || 30), Some(&mut 30));
        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 20), (1, 10)]);

        assert_eq!(lru.get_or_insert(4, || 40), Some(&mut 40));
        assert_eq!(to_vec(&lru), vec![(4, 40), (3, 30), (2, 20)]);

        assert_eq!(lru.get_or_insert(5, || 50), Some(&mut 50));
        assert_eq!(to_vec(&lru), vec![(5, 50), (4, 40), (3, 30)]);

        assert_eq!(lru.get_or_insert(3, || unreachable!()), Some(&mut 30));
        assert_eq!(to_vec(&lru), vec![(3, 30), (5, 50), (4, 40)]);

        assert_eq!(lru.get_or_insert(5, || unreachable!()), Some(&mut 50));
        assert_eq!(to_vec(&lru), vec![(5, 50), (3, 30), (4, 40)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn get_or_insert_fallible_works() {
        let mut lru = LruMap::new(ByLength::new(2));
        assert_eq!(
            lru.get_or_insert_fallible(1, || Ok::<_, ()>(10)).unwrap(),
            Some(&mut 10)
        );
        assert_eq!(
            lru.get_or_insert_fallible(2, || Ok::<_, ()>(20)).unwrap(),
            Some(&mut 20)
        );
        assert_eq!(to_vec(&lru), vec![(2, 20), (1, 10)]);

        assert_eq!(
            lru.get_or_insert_fallible(3, || Ok::<_, ()>(30)).unwrap(),
            Some(&mut 30)
        );
        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 20)]);

        assert!(lru.get_or_insert_fallible(4, || Err(())).is_err());
        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 20)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn insert_with_memory_usage_limiter_works() {
        let mut lru = LruMap::new(UnlimitedCompact);
        assert_eq!(lru.guaranteed_capacity(), 0);
        assert_eq!(lru.memory_usage(), 0);
        lru.insert(1, 10);
        let memory_usage_step_1 = lru.memory_usage();
        lru.insert(2, 20);
        lru.insert(3, 30);
        lru.insert(4, 40);
        let memory_usage_step_2 = lru.memory_usage();
        assert_ne!(memory_usage_step_1, memory_usage_step_2);

        let mut lru = LruMap::new(ByMemoryUsage::new(memory_usage_step_2));
        assert_eq!(lru.guaranteed_capacity(), 0);
        assert_eq!(lru.memory_usage(), 0);
        lru.insert(1, 10);
        assert_eq!(lru.guaranteed_capacity(), 3);
        assert_eq!(lru.memory_usage(), memory_usage_step_1);
        lru.insert(2, 20);
        lru.insert(3, 30);
        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 20), (1, 10)]);
        assert_eq!(lru.guaranteed_capacity(), 3);
        assert_eq!(lru.memory_usage(), memory_usage_step_1);
        lru.insert(4, 40);
        assert_eq!(to_vec(&lru), vec![(4, 40), (3, 30), (2, 20), (1, 10)]);
        assert_eq!(lru.guaranteed_capacity(), 7);
        assert_eq!(lru.memory_usage(), memory_usage_step_2);
        lru.insert(5, 50);
        lru.insert(6, 60);
        lru.insert(7, 70);
        assert_eq!(
            to_vec(&lru),
            vec![(7, 70), (6, 60), (5, 50), (4, 40), (3, 30), (2, 20), (1, 10)]
        );
        assert!(lru.insert(8, 80));
        assert_eq!(
            to_vec(&lru),
            vec![(8, 80), (7, 70), (6, 60), (5, 50), (4, 40), (3, 30), (2, 20)]
        );

        assert_eq!(lru.guaranteed_capacity(), 7);
        assert_eq!(lru.memory_usage(), memory_usage_step_2);
        lru.assert_check_internal_state();

        let mut lru = LruMap::new(ByMemoryUsage::new(memory_usage_step_2 + 1));
        for n in 1..=8 {
            lru.insert(n, n * 10);
        }
        assert_eq!(lru.len(), 7);
        assert_eq!(lru.guaranteed_capacity(), 7);
        assert_eq!(lru.memory_usage(), memory_usage_step_2);

        let mut lru = LruMap::new(ByMemoryUsage::new(memory_usage_step_1 - 1));
        for n in 1..=8 {
            assert!(!lru.insert(n, n * 10));
        }
        assert_eq!(lru.len(), 0);
        assert_eq!(lru.guaranteed_capacity(), 0);
        assert_eq!(lru.memory_usage(), 0);
    }

    #[test]
    fn remove_works() {
        let mut lru = LruMap::new(UnlimitedCompact);
        lru.insert(1, 10);
        lru.insert(2, 20);
        lru.insert(3, 30);
        lru.insert(4, 40);
        lru.insert(5, 50);
        lru.insert(6, 60);
        assert_eq!(to_vec(&lru), vec![(6, 60), (5, 50), (4, 40), (3, 30), (2, 20), (1, 10)]);

        assert_eq!(lru.remove(&123), None);
        assert_eq!(to_vec(&lru), vec![(6, 60), (5, 50), (4, 40), (3, 30), (2, 20), (1, 10)]);

        assert_eq!(lru.remove(&3), Some(30));
        assert_eq!(to_vec(&lru), vec![(6, 60), (5, 50), (4, 40), (2, 20), (1, 10)]);

        assert_eq!(lru.remove(&1), Some(10));
        assert_eq!(to_vec(&lru), vec![(6, 60), (5, 50), (4, 40), (2, 20)]);

        assert_eq!(lru.remove(&6), Some(60));
        assert_eq!(to_vec(&lru), vec![(5, 50), (4, 40), (2, 20)]);

        assert_eq!(lru.remove(&5), Some(50));
        assert_eq!(lru.remove(&4), Some(40));
        assert_eq!(lru.remove(&2), Some(20));
        assert_eq!(to_vec(&lru), vec![]);
    }

    #[test]
    fn get_works_and_promotes_item_single_item() {
        let mut lru = LruMap::new(UnlimitedCompact);
        lru.insert(1, 10);
        assert_eq!(to_vec(&lru), vec![(1, 10)]);

        // Get an entry which doesn't exist.
        assert!(lru.get(&1000).is_none());
        assert_eq!(to_vec(&lru), vec![(1, 10)]);

        // Get an entry which is simultaneously newest and oldest.
        assert_eq!(*lru.get(&1).unwrap(), 10);
        assert_eq!(to_vec(&lru), vec![(1, 10)]);
        assert_eq!(lru.peek_newest().unwrap(), (&1, &10));
        assert_eq!(lru.peek_oldest().unwrap(), (&1, &10));

        lru.assert_check_internal_state();
    }

    #[test]
    fn get_works_and_promotes_item_two_items() {
        let mut lru = LruMap::new(UnlimitedCompact);
        lru.insert(2, 20);
        lru.insert(1, 10);
        assert_eq!(to_vec(&lru), vec![(1, 10), (2, 20)]);

        // Get an entry which doesn't exist.
        assert!(lru.get(&1000).is_none());
        assert_eq!(to_vec(&lru), vec![(1, 10), (2, 20)]);

        // Get an entry which is already the newest.
        assert_eq!(*lru.get(&1).unwrap(), 10);
        assert_eq!(to_vec(&lru), vec![(1, 10), (2, 20)]);
        assert_eq!(lru.peek_newest().unwrap(), (&1, &10));
        assert_eq!(lru.peek_oldest().unwrap(), (&2, &20));

        // Get an entry which is the oldest.
        assert_eq!(*lru.get(&2).unwrap(), 20);
        assert_eq!(to_vec(&lru), vec![(2, 20), (1, 10)]);
        assert_eq!(lru.peek_newest().unwrap(), (&2, &20));
        assert_eq!(lru.peek_oldest().unwrap(), (&1, &10));

        lru.assert_check_internal_state();
    }

    #[test]
    fn get_works_and_promotes_item_three_items() {
        let mut lru = LruMap::new(UnlimitedCompact);
        lru.insert(3, 30);
        lru.insert(2, 20);
        lru.insert(1, 10);
        assert_eq!(to_vec(&lru), vec![(1, 10), (2, 20), (3, 30)]);

        // Get an entry which doesn't exist.
        assert!(lru.get(&1000).is_none());
        assert_eq!(to_vec(&lru), vec![(1, 10), (2, 20), (3, 30)]);

        // Get an entry which is already the newest.
        assert_eq!(*lru.get(&1).unwrap(), 10);
        assert_eq!(to_vec(&lru), vec![(1, 10), (2, 20), (3, 30)]);
        assert_eq!(lru.peek_newest().unwrap(), (&1, &10));
        assert_eq!(lru.peek_oldest().unwrap(), (&3, &30));

        // Get an entry which is the oldest.
        assert_eq!(*lru.get(&3).unwrap(), 30);
        assert_eq!(to_vec(&lru), vec![(3, 30), (1, 10), (2, 20)]);
        assert_eq!(lru.peek_newest().unwrap(), (&3, &30));
        assert_eq!(lru.peek_oldest().unwrap(), (&2, &20));

        // Get an entry in the middle.
        assert_eq!(*lru.get(&1).unwrap(), 10);
        assert_eq!(to_vec(&lru), vec![(1, 10), (3, 30), (2, 20)]);
        assert_eq!(lru.peek_newest().unwrap(), (&1, &10));
        assert_eq!(lru.peek_oldest().unwrap(), (&2, &20));

        lru.assert_check_internal_state();
    }

    #[test]
    fn insert_existing_key() {
        let mut lru = LruMap::new(UnlimitedCompact);
        lru.insert(3, 30);
        lru.insert(2, 20);
        lru.insert(1, 10);
        assert_eq!(to_vec(&lru), vec![(1, 10), (2, 20), (3, 30)]);

        lru.insert(2, 200);
        assert_eq!(to_vec(&lru), vec![(2, 200), (1, 10), (3, 30)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn insert_succeeds_when_first_element_is_cheap() {
        let mut lru = LruMap::new(ByValue::new(1));
        lru.insert(1, 1);
        assert_eq!(lru.limiter().cost, 1);
        assert_eq!(to_vec(&lru), vec![(1, 1)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn insert_fails_when_first_element_is_too_costly() {
        let mut lru = LruMap::new(ByValue::new(1));
        lru.insert(1, 2);
        assert_eq!(lru.limiter().cost, 0);
        assert_eq!(to_vec(&lru), vec![]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn replacing_existing_value_with_another_with_the_same_cost_always_works() {
        let mut lru = LruMap::new(ByValue::new(1));
        lru.insert(1, (1, 100));
        assert_eq!(lru.limiter().cost, 1);
        assert_eq!(to_vec(&lru), vec![(1, (1, 100))]);

        lru.insert(1, (1, 200));
        assert_eq!(lru.limiter().cost, 1);
        assert_eq!(to_vec(&lru), vec![(1, (1, 200))]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn when_new_value_is_too_costly_an_existing_item_will_be_removed_map_is_cleared() {
        let mut lru = LruMap::new(ByValue::new(1));
        lru.insert(1, 1);
        assert_eq!(lru.limiter().cost, 1);
        assert_eq!(to_vec(&lru), vec![(1, 1)]);

        lru.insert(1, 2);
        assert_eq!(lru.limiter().cost, 0);
        assert_eq!(to_vec(&lru), vec![]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn when_new_value_is_too_costly_an_existing_item_will_be_removed_map_is_not_cleared() {
        let mut lru = LruMap::new(ByValue::new(2));
        lru.insert(1, 1);
        lru.insert(2, 2);
        assert_eq!(lru.limiter().cost, 2);
        assert_eq!(to_vec(&lru), vec![(2, 2)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn when_new_value_is_too_costly_an_existing_item_will_not_be_removed_if_the_key_is_different() {
        let mut lru = LruMap::new(ByValue::new(1));
        lru.insert(1, 1);
        assert_eq!(lru.limiter().cost, 1);
        assert_eq!(to_vec(&lru), vec![(1, 1)]);

        lru.insert(2, 2);
        assert_eq!(lru.limiter().cost, 1);
        assert_eq!(to_vec(&lru), vec![(1, 1)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn when_new_value_is_too_costly_all_items_will_be_removed() {
        let mut lru = LruMap::new(ByValue::new(3));
        lru.insert(1, 1);
        lru.insert(2, 2);
        assert_eq!(lru.limiter().cost, 3);
        assert_eq!(to_vec(&lru), vec![(2, 2), (1, 1)]);

        lru.insert(3, 3);
        assert_eq!(lru.limiter().cost, 3);
        assert_eq!(to_vec(&lru), vec![(3, 3)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn when_new_value_is_too_costly_multiple_items_will_be_removed() {
        let mut lru = LruMap::new(ByValue::new(3));
        lru.insert(1, 1);
        lru.insert(2, 1);
        lru.insert(3, 1);
        assert_eq!(lru.limiter().cost, 3);
        assert_eq!(to_vec(&lru), vec![(3, 1), (2, 1), (1, 1)]);

        lru.insert(4, 2);
        assert_eq!(lru.limiter().cost, 3);
        assert_eq!(to_vec(&lru), vec![(4, 2), (3, 1)]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn pop_oldest_works() {
        let mut lru = LruMap::new(ByValue::new(10));
        lru.insert(1, 1);
        lru.insert(2, 2);
        lru.insert(3, 3);
        assert_eq!(lru.limiter().cost, 6);
        assert_eq!(to_vec(&lru), vec![(3, 3), (2, 2), (1, 1)]);

        assert_eq!(lru.pop_oldest().unwrap(), (1, 1));
        assert_eq!(lru.limiter().cost, 5);

        assert_eq!(lru.pop_oldest().unwrap(), (2, 2));
        assert_eq!(lru.limiter().cost, 3);

        assert_eq!(lru.pop_oldest().unwrap(), (3, 3));
        assert_eq!(lru.limiter().cost, 0);

        assert!(lru.pop_oldest().is_none());

        lru.assert_check_internal_state();
    }

    #[test]
    fn pop_newest_works() {
        let mut lru = LruMap::new(ByValue::new(10));
        lru.insert(1, 1);
        lru.insert(2, 2);
        lru.insert(3, 3);
        assert_eq!(lru.limiter().cost, 6);
        assert_eq!(to_vec(&lru), vec![(3, 3), (2, 2), (1, 1)]);

        assert_eq!(lru.pop_newest().unwrap(), (3, 3));
        assert_eq!(lru.limiter().cost, 3);

        assert_eq!(lru.pop_newest().unwrap(), (2, 2));
        assert_eq!(lru.limiter().cost, 1);

        assert_eq!(lru.pop_newest().unwrap(), (1, 1));
        assert_eq!(lru.limiter().cost, 0);

        assert!(lru.pop_newest().is_none());

        lru.assert_check_internal_state();
    }

    #[test]
    fn clear_works() {
        let mut lru = LruMap::new(ByValue::new(10));
        lru.insert(1, 1);
        lru.insert(2, 2);
        lru.insert(3, 3);
        assert_eq!(lru.limiter().cost, 6);
        assert_eq!(to_vec(&lru), vec![(3, 3), (2, 2), (1, 1)]);

        lru.clear();

        assert_eq!(lru.limiter().cost, 0);
        assert_eq!(to_vec(&lru), vec![]);

        lru.assert_check_internal_state();
    }

    #[test]
    fn drain_works() {
        let mut lru = LruMap::new(ByValue::new(10));
        lru.insert(1, 1);
        lru.insert(2, 2);
        lru.insert(3, 3);
        assert_eq!(lru.limiter().cost, 6);

        let vec: Vec<_> = lru.drain().collect();
        assert_eq!(vec, vec![(3, 3), (2, 2), (1, 1)]);
        assert_eq!(to_vec(&lru), vec![]);
        assert!(lru.is_empty());
        assert_eq!(lru.limiter().cost, 0);

        lru.assert_check_internal_state();
    }

    #[test]
    fn drain_in_reverse_works() {
        let mut lru = LruMap::new(ByValue::new(10));
        lru.insert(1, 1);
        lru.insert(2, 2);
        lru.insert(3, 3);
        assert_eq!(lru.limiter().cost, 6);

        let vec: Vec<_> = lru.drain().rev().collect();
        assert_eq!(vec, vec![(1, 1), (2, 2), (3, 3)]);
        assert_eq!(to_vec(&lru), vec![]);
        assert!(lru.is_empty());
        assert_eq!(lru.limiter().cost, 0);

        lru.assert_check_internal_state();
    }

    #[test]
    fn dropping_drain_clears_the_map() {
        let mut lru = LruMap::new(ByValue::new(10));
        lru.insert(1, 1);
        lru.insert(2, 2);
        lru.insert(3, 3);
        assert_eq!(lru.limiter().cost, 6);

        let vec: Vec<_> = lru.drain().take(1).collect();
        assert_eq!(vec, vec![(3, 3)]);
        assert_eq!(to_vec(&lru), vec![]);
        assert!(lru.is_empty());
        assert_eq!(lru.limiter().cost, 0);

        lru.assert_check_internal_state();
    }

    #[test]
    fn the_maximum_number_of_elements_is_bound_by_the_link_type_u8() {
        let mut lru = LruMap::with_seed(UnlimitedU8, [12, 34, 56, 78]);
        let limit = 112;

        for n in 0..limit {
            lru.insert(n, n);
            assert_eq!(lru.len(), n + 1);
            assert_eq!(lru.peek_oldest().unwrap(), (&0, &0));
            assert_eq!(lru.peek_newest().unwrap(), (&n, &n));
        }

        lru.insert(limit, limit);
        assert!(lru.len() <= limit as usize, "failed with length = {}", lru.len());
        assert_ne!(lru.peek_oldest().unwrap(), (&0, &0));
        assert_eq!(lru.peek_newest().unwrap(), (&limit, &limit));

        lru.assert_check_internal_state();
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Takes way too long.
    fn the_maximum_number_of_elements_is_bound_by_the_link_type_u16() {
        let mut lru = LruMap::with_seed(UnlimitedU16, [12, 34, 56, 78]);
        let limit = 28672;

        for n in 0..limit {
            lru.insert(n, n);
            assert_eq!(lru.len(), n + 1);
            assert_eq!(lru.peek_oldest().unwrap(), (&0, &0), "failed at {}", n);
            assert_eq!(lru.peek_newest().unwrap(), (&n, &n));
        }

        lru.insert(limit, limit);
        assert!(lru.len() <= limit as usize, "failed with length = {}", lru.len());
        assert_ne!(lru.peek_oldest().unwrap(), (&0, &0));
        assert_eq!(lru.peek_newest().unwrap(), (&limit, &limit));
        assert!(lru.get(&0).is_none());

        lru.assert_check_internal_state();
    }

    #[test]
    #[ignore] // Takes way too long and way too much memory.
    fn element_limit() {
        let mut lru = LruMap::with_seed(UnlimitedCompact, [12, 34, 56, 78]);
        let limit = 1879048192_u32;
        lru.reserve_or_panic(limit as usize);

        for n in 0..limit {
            lru.insert(n, ());
            assert_eq!(lru.len(), n as usize + 1, "failed at {}", n);
            assert_eq!(lru.peek_oldest().unwrap(), (&0, &()), "failed at {}", n);
            assert_eq!(lru.peek_newest().unwrap(), (&n, &()));
        }

        lru.insert(limit, ());
        assert!(lru.len() <= limit as usize, "failed with length = {}", lru.len());
        assert_ne!(lru.peek_oldest().unwrap(), (&0, &()));
        assert_eq!(lru.peek_newest().unwrap(), (&limit, &()));
        assert!(lru.get(&0).is_none());
    }

    #[test]
    fn lru_with_a_string_key_works() {
        // This is mostly just to check that it compiles.

        use alloc::string::ToString;
        let mut lru = LruMap::new(UnlimitedCompact);
        lru.insert("1".to_string(), 1);
        lru.insert("2".to_string(), 2);
        lru.insert("3".to_string(), 3);

        assert_eq!(lru.peek("2").unwrap(), &2);
        assert_eq!(lru.get("2").unwrap(), &2);

        let value = lru.get_or_insert("2".to_string(), || 20).unwrap();
        assert_eq!(value, &2);

        let value = lru.get_or_insert("4".to_string(), || 40).unwrap();
        assert_eq!(value, &40);

        let value = lru.get_or_insert("2", || 200).unwrap();
        assert_eq!(value, &2);

        let value = lru.get_or_insert("6", || 6).unwrap();
        assert_eq!(value, &6);

        lru.assert_check_internal_state();
    }

    #[test]
    fn lru_with_a_custom_insert_key_works() {
        // This is mostly just to check that it compiles.

        let mut lru = LruMap::new(WithCustomInsertKey);
        lru.insert(InsertKey("1"), 1);
        lru.insert(InsertKey("2"), 2);
        lru.insert(InsertKey("3"), 3);

        assert_eq!(lru.peek("2").unwrap(), &2);
        assert_eq!(lru.get("2").unwrap(), &2);

        let value = lru.get_or_insert(InsertKey("2"), || 20).unwrap();
        assert_eq!(value, &2);

        let value = lru.get_or_insert(InsertKey("4"), || 40).unwrap();
        assert_eq!(value, &40);

        lru.assert_check_internal_state();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn capacity_growth() {
        let mut lru = LruMap::new(UnlimitedCompact);
        assert_eq!(lru.guaranteed_capacity(), 0);

        let sizes = [
            0, 3, 7, 14, 28, 56, 112, 224, 448, 896, 1792, 3584, 7168, 14336, 28672, 57344, 114688, 229376, 458752,
            917504, 1835008,
        ];

        for pair in sizes.windows(2) {
            for n in pair[0]..pair[1] {
                lru.insert(n, ());
                assert_eq!(lru.guaranteed_capacity(), pair[1]);
            }
        }
    }

    #[test]
    fn inserting_can_evict_the_whole_cache() {
        let mut lru = LruMap::new(Manual { overflow: false });
        lru.insert(1, 10);
        lru.insert(2, 20);
        assert_eq!(lru.len(), 2);

        lru.limiter_mut().overflow = true;
        assert!(lru.get_or_insert(3, || 30).is_none());
        assert!(lru.is_empty());

        lru.limiter_mut().overflow = false;
        lru.insert(1, 10);
        lru.insert(2, 20);
        assert_eq!(lru.len(), 2);

        lru.limiter_mut().overflow = true;
        assert!(!lru.insert(3, 30));
        assert!(lru.is_empty());
    }

    #[test]
    fn insert_and_remove_a_lot_of_elements() {
        let mut lru = LruMap::with_seed(UnlimitedCompact, [12, 34, 56, 78]);
        for n in 0..1024 {
            lru.insert(n % 256, 255);
            lru.insert(65535, 255);
            lru.remove(&65535);

            if n % 1024 == 0 {
                lru.assert_check_internal_state();
            }
        }
    }

    #[test]
    fn randomly_insert_and_remove_elements_in_a_memory_bound_map() {
        let limiter = ByMemoryUsage::new(512);
        let mut lru = LruMap::with_seed(limiter, [12, 34, 56, 78]);

        let count = if cfg!(miri) { 1024 * 4 } else { 1024 * 64 };

        let mut rng = oorandom::Rand32::new(1234);
        for n in 0..count {
            let key = rng.rand_range(0..255) as u16;
            lru.insert(key, n as u8);

            let key = rng.rand_range(0..255) as u16;
            lru.remove(&key);

            if n % 1024 == 0 {
                lru.assert_check_internal_state();
            }
        }
    }

    #[test]
    fn peek_works() {
        let mut lru = LruMap::new(UnlimitedCompact);
        lru.insert(1, 10);
        lru.insert(2, 20);
        lru.insert(3, 30);

        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 20), (1, 10)]);
        assert_eq!(*lru.peek(&2).unwrap(), 20);
        // Order's not changed.
        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 20), (1, 10)]);

        assert_eq!(*lru.peek_mut(&2).unwrap(), 20);
        // Order's not changed.
        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 20), (1, 10)]);

        *lru.peek_mut(&2).unwrap() = 200;
        assert_eq!(to_vec(&lru), vec![(3, 30), (2, 200), (1, 10)]);
    }

    #[test]
    fn iter_mut_works() {
        let mut lru = LruMap::new(UnlimitedCompact);
        assert!(lru.is_empty());
        assert_eq!(lru.len(), 0);
        assert_eq!(lru.iter_mut().collect::<Vec<_>>(), vec![]);

        lru.insert(0, 1);
        lru.insert(1, 2);
        lru.insert(2, 3);
        assert!(!lru.is_empty());
        assert_eq!(lru.len(), 3);
        for (key, value) in lru.iter_mut() {
            if key % 2 == 0 {
                *value *= 2;
            }
        }
        // only key which is even has new value which is double of the old value
        // so for key 2, the value 3 is doubled to 6
        assert_eq!(lru.get(&2), Some(&mut 6));

        // After using key 2, the iterator should get [2, 1, 0]
        let keys: Vec<_> = lru.iter_mut().map(|(key, _value)| key.clone()).collect();
        assert_eq!(keys, vec![2, 1, 0]);

        // next_back should return the last key which is 0
        let last_key = lru.iter_mut().next_back().unwrap().0;
        assert_eq!(last_key, &0);

        // After using key 0, the iterator should get [0, 2, 1]
        lru.get(&0);
        let keys: Vec<_> = lru.iter_mut().map(|(key, _value)| key.clone()).collect();
        assert_eq!(keys, vec![0, 2, 1]);

        // next_back should return the last key which is 1
        let last_key = lru.iter_mut().next_back().unwrap().0;
        assert_eq!(last_key, &1);
        lru.assert_check_internal_state();
    }
}
