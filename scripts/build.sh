#!/usr/bin/env bash
# Builds the verified core and the Python extension from the same sources the gate verified.
# Runs the verification gate first; the build is only produced if it passes.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
cd "$PP_ROOT"

"$PP_ROOT/scripts/verify.sh"
"$PP_ROOT/scripts/audit.sh"

PY="${PP_PYTHON:-python3}"
echo "== build (rust $PP_RUST_TOOLCHAIN, python $("$PY" --version 2>&1))"
PYO3_PYTHON="$(command -v "$PY")" cargo +"$PP_RUST_TOOLCHAIN" build --release -p pageproof-core -p pageproof-py
mkdir -p "$PP_ROOT/python"
cp "$PP_ROOT/target/release/libpageproof.dylib" "$PP_ROOT/python/pageproof.so"
shasum -a 256 "$PP_ROOT/python/pageproof.so"
echo "build.sh: OK"
