# Trusted computing base

## What is proved

`scripts/verify.sh` runs Verus on `crates/pageproof-core` at a fixed `--rlimit 20` and fails on
any error, timeout or rlimit exhaustion. Every public method of `Manager` (C0–C6) is proved on its
real body, with machine integers, against the contract v0.2.1. See
[SPEC_NOTES.md](SPEC_NOTES.md) for the exact statement of each result and any deviations.

## What is trusted

| Component | Version | Role |
|---|---|---|
| Verus | 0.2026.11.02.8bf68ee | verifier, erasure, rustc driver |
| Z3 | 4.16.0 (bundled with Verus) | SMT solver |
| vstd | 0.0.0-2026-11-01-0251 | specs for `Vec`, `HashMap`, slices, atomics, and the set/map/seq axioms |
| rustc | 1.99.1 | compiles the erased code |
| `sha2` | 0.10.9 | SHA-256 inside the E8 wrapper |
| PyO3 shim | `crates/pageproof-py` | type conversion only (unverified I/O shim) |
| Scripts | `scripts/` | orchestration |

Exact hashes are in [toolchain.json](toolchain.json).

### Proof escape hatches in `pageproof-core`

`scripts/audit.sh` checks the sources and fails on any of these: `assume`, `admit`,
`assume_specification`, axioms, `external`, `external_fn/type/trait_specification`,
`decreases *`, `truncate`, `unsafe`. It also requires that there be **exactly one**
`#[verifier::external_body]`:

- `e8::sha256` (the E8 assumption). Its spec says the result is `sha256_spec(input)`, and that
  if this digest is already in the manager's ghost `DenLog`, it was recorded for the same input.
  It then records the input. It does **not** say SHA-256 is injective, which would be false and
  would make the logic inconsistent. A proof of `false` from this spec would require a real
  SHA-256 collision among the inputs one manager hashes. That is exactly E8, with
  `ε ≤ Q²/2²⁵⁷ + Q/2²⁵⁶`.

The core also uses these vstd-provided specs (vstd's own trusted base, not added here):
`Vec` push/pop/index/set/swap_remove/extend_from_slice, `HashMap` get/insert/remove/contains_key
(with the `u64` key model axiom), `slice_subrange`, `slice_to_vec`, and `AtomicU64`
load/compare_exchange.

## External assumptions (contract §9.0)

| | Status here |
|---|---|
| E1 completion is real | Assumed. `finish_write` requires `Completion { ticket }` to name the ticket; truth is the executor's obligation. |
| E2 KV depends only on the prefix | Assumed. Ghost `V` records provenance, not numerics. |
| E3 single-threaded | Enforced in Rust by `&mut self`. The PyO3 class is `unsendable`. The process-global manager-id counter is atomic. |
| Manager-id uniqueness | Trusted (see SPEC_NOTES). Relies on `AtomicU64` behaving as a counter. vstd gives no spec for its return values. Runtime-tested only. |
| E4 writes always succeed | Assumed; there is no abort path (v0.2 scope). |
| E5 executor uses the planned slots and B | Assumed. The plan's slots are proved equal to `slot(h,j)`. |
| E6 Namespace completeness | Caller's obligation. The namespace is an opaque byte string (v0.2 dummy). |
| E7 canonical encoding | **Proved**: `lemma_enc_inj`, `lemma_node_input_inj`, `lemma_seed_input_inj`, `lemma_seed_ne_node`. The exec encoders are proved equal to the spec. A runtime test also checks them byte-for-byte against an independent `sha2` re-implementation. |
| E8 SHA-256 collision resistance | The single trusted wrapper above. |

## Not covered

- `crates/pageproof-py` and `python/demo.py` are not verified. The shim only converts types. Its
  one judgement call is that `finish_write(ticket)` constructs `Completion { ticket }`: calling it
  is the executor's E1 assertion.
- The OS, allocator, CPython, and the dynamic loader.
- Allocation failure, panics in std, and process termination (contract §5 excludes these).
- Byte-level memory. The proof bounds element counts (`Manager::lemma_bounded`). That `Vec` and
  `HashMap` memory tracks their peak element count is trusted about std.
