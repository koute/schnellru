#!/bin/bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
cd ..

./ci/jobs/build-and-test.sh
./ci/jobs/fuzz.sh
./ci/jobs/clippy.sh
./ci/jobs/rustfmt.sh

echo "----------------------------------------"
echo "All tests finished!"
