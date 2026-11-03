#!/usr/bin/env bash
# Clippy gate for the entire workspace, including tests and the Python facade.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
cd "$PP_ROOT"

# These suggestions change proof-sensitive Verus signatures, contracts, or loop bodies.
# Revisit each exception alongside verification rather than applying Clippy's fixes blindly.
cargo +"$PP_RUST_TOOLCHAIN" clippy --workspace --all-targets -- \
  -D warnings \
  -A clippy::len_without_is_empty \
  -A clippy::manual_unwrap_or_default \
  -A clippy::len_zero \
  -A clippy::ptr_arg \
  -A clippy::single_match \
  -A clippy::manual_map \
  -A clippy::too_many_arguments \
  -A clippy::assign_op_pattern \
  -A clippy::manual_div_ceil

echo "lint.sh: OK"
