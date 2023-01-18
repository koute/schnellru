# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

## 0.2.1 - 2023-01-18

### Changed

- `peek` has now an explicit lifetime annotation

### Added

- Added `peek_mut` and `peek_by_hash_mut`

## 0.2.0 - 2023-01-13

### Changed

- `hashbrown` was updated to 0.13.2
- The version of `hashbrown` is now pinned to the exact minor version
- The `Into<K>` bound from `insert`, `get_or_insert_fallible` and `get_or_insert` was removed
- `get_or_insert` and `get_or_insert_fallible` now accept borrowed keys

### Fixed

- Rehash the map in-place instead of trying to resize it from scratch with the same bucket count
  when there are a lot of deleted elements; this fixes a performance regression where the map was
  getting recreated a lot more often than necessary

## 0.1.1 - 2022-12-20

### Security

- Fix `insert` returning `true` even though all of the elements were popped

## 0.1.0 - 2022-12-20

### Added

- Initial release.
