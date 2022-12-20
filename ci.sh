#!/bin/sh

set -euxo pipefail

cargo check
cargo check --benches

cargo fmt --check --all
cargo clippy -- -D warnings

cargo check --no-default-features

cargo test
cargo miri test

export HFUZZ_RUN_ARGS="--timeout 5 --verbose --iterations 10000000 --exit_upon_crash"

cd fuzz
cargo hfuzz run fuzz-behavior-matches-lru
cargo hfuzz run fuzz-internal-invariants
cargo hfuzz run fuzz-by-memory-usage-works

echo "All OK!"
