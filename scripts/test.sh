#!/usr/bin/env bash
# Runtime tests (contract §7 table), the Python demo and the chunked prefill example.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
cd "$PP_ROOT"

PY="${PP_PYTHON:-python3}"
cargo +"$PP_RUST_TOOLCHAIN" test -p pageproof-core
if [[ ! -f "$PP_ROOT/python/pageproof.so" ]]; then
  echo "test.sh: python/pageproof.so missing; run scripts/build.sh first" >&2
  exit 1
fi
(cd "$PP_ROOT/python" && "$PY" demo.py && "$PY" chunked_prefill.py)
echo "test.sh: OK"
