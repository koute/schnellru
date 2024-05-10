#!/bin/bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
cd ../..

export HFUZZ_RUN_ARGS="--timeout 5 --verbose --iterations 10000000 --exit_upon_crash"

cd fuzz
echo ">> hfuzz fuzz-behavior-matches-lru"
cargo hfuzz run fuzz-behavior-matches-lru

echo ">> fuzz-internal-invariants"
cargo hfuzz run fuzz-internal-invariants

echo ">> fuzz-by-memory-usage-works"
cargo hfuzz run fuzz-by-memory-usage-works

echo "All OK!"
