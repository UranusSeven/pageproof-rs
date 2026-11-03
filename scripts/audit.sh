#!/usr/bin/env bash
# Trusted-base audit for the verified core. Fails if any proof escape hatch appears outside the
# allow-list below. The allow-list is exactly the contract's E8 wrapper.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
cd "$PP_ROOT/crates/pageproof-core/src"

fail=0
check() {
  local pattern="$1" allowed="$2" what="$3"
  local hits
  hits="$(grep -nE "$pattern" -- *.rs || true)"
  local count
  count="$(printf '%s' "$hits" | grep -c . || true)"
  if [[ "$count" -ne "$allowed" ]]; then
    echo "audit: $what: expected $allowed, found $count"
    printf '%s\n' "$hits"
    fail=1
  else
    echo "audit: $what: $count (allowed $allowed)"
    if [[ -n "$hits" ]]; then printf '  %s\n' "$hits"; fi
  fi
  return 0
}

# Proof escape hatches: none allowed.
check '\bassume\s*\(' 0 'assume('
check '\badmit\s*\(' 0 'admit('
check 'assume_specification' 0 'assume_specification'
check '\baxiom\b|broadcast axiom' 0 'axiom'
check 'verifier::external\b|verifier::external\]|#\[verifier::external\]' 0 'verifier::external'
check 'external_fn_specification|external_type_specification|external_trait_specification' 0 'external specs'
check 'verifier::exec_allows_no_decreases_clause|decreases \*' 0 'unchecked termination'
check 'verifier::truncate' 0 'verifier::truncate'
check 'verifier::assume_termination|verifier::loop_isolation\(false\)' 0 'termination/isolation overrides'
check '\bunsafe\b' 0 'unsafe'
check '\bfn\s+\w+\s*\([^)]*\)\s*->[^{]*\bno_unwind\b' 0 'no_unwind claims'
# Exactly one external_body: the E8 SHA-256 wrapper in e8.rs.
check 'verifier::external_body' 1 'external_body (E8 wrapper only)'
grep -nA2 'verifier::external_body' e8.rs | grep -q 'fn sha256' || {
  echo "audit: the only external_body must be e8::sha256"
  fail=1
}
# Everything must be inside verus! blocks except module declarations/uses and docs.
for f in *.rs; do
  if ! grep -q 'verus! {' "$f"; then
    echo "audit: $f has no verus! block"
    fail=1
  fi
done

# The verified client must contain no escape hatches at all.
client_hits="$(grep -nE '\bassume\s*\(|\badmit\s*\(|external_body|assume_specification|\baxiom\b|\bunsafe\b' "$PP_ROOT/crates/pageproof-client/src/"*.rs || true)"
if [[ -n "$client_hits" ]]; then
  echo "audit: escape hatch in pageproof-client:"
  printf '%s\n' "$client_hits"
  fail=1
else
  echo "audit: pageproof-client: no escape hatches"
fi

if [[ $fail -ne 0 ]]; then
  echo "audit.sh: FAILED" >&2
  exit 1
fi
echo "audit.sh: OK"
