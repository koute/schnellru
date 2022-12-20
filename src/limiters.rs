use crate::Limiter;

/// A limiter for a map which is limited by the number of elements.
#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct ByLength {
    max_length: u32,
}

impl ByLength {
    /// Creates a new length limiter with a given `max_length`.
    ///
    /// If you don't need to strictly cap the number of elements and just want to limit
    /// the memory usage then prefer using [`ByMemoryUsage`].
    pub const fn new(max_length: u32) -> Self {
        ByLength { max_length }
    }

    /// Returns the max length.
    pub const fn max_length(&self) -> u32 {
        self.max_length
    }
}

impl<K, V> Limiter<K, V> for ByLength {
    type KeyToInsert<'a> = K;
    type LinkType = u32;

    #[inline]
    fn is_over_the_limit(&self, length: usize) -> bool {
        length > self.max_length as usize
    }

    #[inline]
    fn on_insert(&mut self, _length: usize, key: Self::KeyToInsert<'_>, value: V) -> Option<(K, V)> {
        if self.max_length > 0 {
            Some((key, value))
        } else {
            None
        }
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
    fn on_grow(&mut self, _new_memory_usage: usize) -> bool {
        true
    }
}

/// A limiter for a map which is limited by memory usage.
#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct ByMemoryUsage {
    max_bytes: usize,
}

impl ByMemoryUsage {
    /// Creates a new memory usage limiter with a given limit in bytes.
    pub const fn new(max_bytes: usize) -> Self {
        ByMemoryUsage { max_bytes }
    }

    /// Returns the max memory usage.
    pub const fn max_memory_usage(&self) -> usize {
        self.max_bytes
    }
}

impl<K, V> Limiter<K, V> for ByMemoryUsage {
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
        new_memory_usage <= self.max_bytes
    }
}

/// A limiter for a map which can hold an unlimited number of elements.
///
/// With this limiter the map will act like a normal ordered hashmap.
///
/// On 64-bit systems it is less efficient and uses more memory than [`UnlimitedCompact`],
/// but can hold a truly unlimited number of elements.
///
/// On 32-bit systems it is exactly the same as [`UnlimitedCompact`].
#[derive(Copy, Clone, Debug, Default)]
pub struct Unlimited;

impl<K, V> Limiter<K, V> for Unlimited {
    type KeyToInsert<'a> = K;
    type LinkType = usize;

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
    fn on_grow(&mut self, _new_memory_usage: usize) -> bool {
        true
    }
}

/// A limiter for a map which can hold an unlimited** number of elements.
///
/// ** - limited to around somewhere between a billion elements and two billion elements.
/// If you need to store more use [`Unlimited`].
#[derive(Copy, Clone, Debug, Default)]
pub struct UnlimitedCompact;

impl<K, V> Limiter<K, V> for UnlimitedCompact {
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
    fn on_grow(&mut self, _new_memory_usage: usize) -> bool {
        true
    }
}
