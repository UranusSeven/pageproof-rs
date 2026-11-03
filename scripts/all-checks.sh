#!/usr/bin/env bash
# Full gate: verify + audit + build + tests + demo.
set -euo pipefail
here="$(dirname "${BASH_SOURCE[0]}")"
"$here/build.sh"
"$here/test.sh"
echo "all-checks.sh: OK"
