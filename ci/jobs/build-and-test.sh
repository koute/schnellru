#!/bin/bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
cd ../..

echo ">> cargo check"
cargo check

echo ">> cargo check (benches)"
cargo check --benches

echo ">> cargo check (no-default-features)"
cargo check --no-default-features

echo ">> cargo test"
cargo test --all

echo ">> cargo test (release)"
cargo test --all --release

echo ">> cargo test (randomize-layout)"
RUSTFLAGS="-Z randomize-layout" rustup run nightly-2024-05-08 cargo test

echo ">> cargo test (randomize-layout, release)"
RUSTFLAGS="-Z randomize-layout" rustup run nightly-2024-05-08 cargo test --release

echo ">> cargo miri"
rustup run nightly-2024-05-08 cargo miri test

echo "All OK!"
