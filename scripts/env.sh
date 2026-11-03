# Source this file: sets up the pinned Verus toolchain for pageproof-rs.
# All tool state lives under .toolchain/ (gitignored); nothing is written to ~/.cargo.
PP_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PP_ROOT
export VERUS_DIR="$PP_ROOT/.toolchain/verus-arm64-macos"
export CARGO_HOME="$PP_ROOT/.toolchain/cargo-home"
export PATH="$VERUS_DIR:$PATH"
# Toolchain required by the locked Verus release (see toolchain.json).
export PP_RUST_TOOLCHAIN="1.99.1-aarch64-apple-darwin"
# Fixed per-query resource limit; the verify gate must pass under it (no timeouts).
export PP_RLIMIT="${PP_RLIMIT:-20}"
