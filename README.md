# A fast and flexible LRU map

[![Documentation](https://docs.rs/schnellru/badge.svg)](https://docs.rs/schnellru/*/schnellru/)

This repository contains a fast and flexible LRU map.

  * Blazingly fast. Up to twice as fast as the [`lru`](https://github.com/jeromefroe/lru-rs) crate, and with less memory overhead.
  * Can be also used as an ordered map, with roughly the same performance as [`indexmap`](https://github.com/bluss/indexmap),
    but with added support for O(1) removals without changing the element order (where `indexmap` only supports O(n) non-perturbing removals).
  * Customizable. Out-of-box can be limited by length or by memory usage, but supports custom limiters which can be made to limit the map by whatever you want.
  * Tested, miri-clean, clippy-clean and fuzzed.
  * Supports `no_std`.

## Examples

```rust
use schnellru::{LruMap, ByLength};
let mut map = LruMap::new(ByLength::new(3));

// Insert three elements.
map.insert(1, "one");
map.insert(2, "two");
map.insert(3, "three");
assert_eq!(map.len(), 3);

// They're ordered according to which one was inserted last.
let mut iter = map.iter();
assert_eq!(iter.next().unwrap(), (&3, &"three"));
assert_eq!(iter.next().unwrap(), (&2, &"two"));
assert_eq!(iter.next().unwrap(), (&1, &"one"));

// Access the least recently inserted one.
assert_eq!(*map.get(&1).unwrap(), "one");

// Now the order's changed.
// The element we've accessed was moved to the front.
let mut iter = map.iter();
assert_eq!(iter.next().unwrap(), (&1, &"one"));
assert_eq!(iter.next().unwrap(), (&3, &"three"));
assert_eq!(iter.next().unwrap(), (&2, &"two"));

// Insert a fourth element.
// This will automatically pop the least recently accessed one.
map.insert(4, "four");

// Still the same number of elements.
assert_eq!(map.len(), 3);

// And this is the one which was removed.
assert!(map.peek(&2).is_none());

// And here's the new order.
let mut iter = map.iter();
assert_eq!(iter.next().unwrap(), (&4, &"four"));
assert_eq!(iter.next().unwrap(), (&1, &"one"));
assert_eq!(iter.next().unwrap(), (&3, &"three"));
```

## License

Licensed under either of

  * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
  * MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
