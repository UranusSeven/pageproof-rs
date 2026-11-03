#!/usr/bin/env bash
# Installs the pinned Verus release into .toolchain/ and checks its SHA-256 (see toolchain.json).
# Requires rustup; installs the Rust toolchain that this Verus release is built against.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"

VERUS_VERSION="0.2026.11.02.8bf68ee"
VERUS_ZIP="verus-${VERUS_VERSION}-arm64-macos.zip"
VERUS_URL="https://github.com/verus-lang/verus/releases/download/release/${VERUS_VERSION}/${VERUS_ZIP}"
VERUS_SHA256="3086974d1afebf8b9f6fee2939b626486a12248c0dab528b9262ea652b863326"

if [[ "$(uname -s)-$(uname -m)" != "Darwin-arm64" ]]; then
  echo "setup.sh: only the arm64 macOS release is pinned; edit toolchain.json for other platforms" >&2
  exit 1
fi

mkdir -p "$PP_ROOT/.toolchain" "$CARGO_HOME"
if [[ ! -x "$VERUS_DIR/verus" ]]; then
  tmp="$(mktemp -d)"
  curl -sSL --fail -o "$tmp/$VERUS_ZIP" "$VERUS_URL"
  echo "$VERUS_SHA256  $tmp/$VERUS_ZIP" | shasum -a 256 -c -
  unzip -q -o "$tmp/$VERUS_ZIP" -d "$PP_ROOT/.toolchain"
  rm -rf "$tmp"
fi

rustup toolchain list | grep -q "^${PP_RUST_TOOLCHAIN}" || rustup install "$PP_RUST_TOOLCHAIN"

"$VERUS_DIR/verus" --version
