#!/usr/bin/env bash
# Verification gate: full Verus verification of pageproof-core under a fixed rlimit.
# Fails on any error, timeout, or rlimit exhaustion. Prints source hashes for provenance.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
cd "$PP_ROOT/crates/pageproof-core"

echo "== sources"
shasum -a 256 src/*.rs
echo "== verus (rlimit $PP_RLIMIT)"
log="$(mktemp)"
# Force re-verification of this crate (cargo would otherwise reuse a cached result).
cargo clean -p pageproof-core >/dev/null 2>&1
set +e
cargo verus verify -- --rlimit "$PP_RLIMIT" --triggers-mode silent 2>&1 | tee "$log"
status=${PIPESTATUS[0]}
set -e
summary="$(grep -E '^verification results::' "$log" | tail -1 || true)"
rm -f "$log"
echo "== $summary"
if [[ $status -ne 0 ]]; then
  echo "verify.sh: FAILED (exit $status)" >&2
  exit 1
fi
if ! [[ "$summary" =~ ,\ 0\ errors$ ]]; then
  echo "verify.sh: unexpected summary" >&2
  exit 1
fi
echo "== verified client (public-spec usability)"
cd "$PP_ROOT/crates/pageproof-client"
cargo clean -p pageproof-client >/dev/null 2>&1
log="$(mktemp)"
set +e
cargo verus verify -- --rlimit "$PP_RLIMIT" --triggers-mode silent 2>&1 | tee "$log"
status=${PIPESTATUS[0]}
set -e
summary="$(grep -E '^verification results::' "$log" | tail -1 || true)"
rm -f "$log"
echo "== client $summary"
if [[ $status -ne 0 ]] || ! [[ "$summary" =~ ,\ 0\ errors$ ]]; then
  echo "verify.sh: client FAILED" >&2
  exit 1
fi
echo "verify.sh: OK"
