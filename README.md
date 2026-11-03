# pageproof-rs

A KV-cache block manager for LLM serving, written in Rust and verified with
[Verus](https://github.com/verus-lang/verus) against the pageproof block-manager contract v0.2
([docs/block-manager-contract.md](docs/block-manager-contract.md)).

Every public method (create, attach, extend, begin_write, finish_write, release, inspect,
slot_of) is proved on its real body, with machine integers. Each proof covers:

- the invariant `Valid(S)` (I1–I10, including I5b)
- the method's functional postcondition and exact frame
- strong failure atomicity on every declared error

The chained SHA-256 cache key is implemented byte-for-byte as specified. The only trusted
function in the verified core is the SHA-256 call, whose spec is exactly the contract's E8
assumption.

## Layout

| Path | Contents |
|---|---|
| `crates/pageproof-core/src/spec.rs` | §3.3 encodings, chained key, `den`, E7 and chain lemmas |
| `crates/pageproof-core/src/e8.rs` | the single trusted SHA-256 wrapper; verified canonical encoders |
| `crates/pageproof-core/src/model.rs` | abstract `Valid(S)` and frame lemmas |
| `crates/pageproof-core/src/manager.rs` | `Manager`, refinement relation, C0 |
| `crates/pageproof-core/src/ops_*.rs` | C1–C6 and their preservation proofs |
| `crates/pageproof-core/src/{idxset,index,arith}.rs` | verified free set, key index, arithmetic |
| `crates/pageproof-core/tests/edge_cases.rs` | runtime tests for the §7 table |
| `crates/pageproof-py` | thin PyO3 facade (unverified I/O shim) |
| `crates/pageproof-client` | a verified client that uses the public specs |
| `python/demo.py` | end-to-end demo through Python |

## Usage

```bash
./scripts/setup.sh       # pinned Verus into .toolchain/, Rust 1.99.1 via rustup
./scripts/verify.sh      # Verus, fixed rlimit; fails on any error/timeout
./scripts/audit.sh       # escape-hatch audit (exactly one external_body: E8)
./scripts/build.sh       # verify + audit, then build core + python/pageproof.so
./scripts/test.sh        # Rust edge-case tests + Python demo
./scripts/all-checks.sh  # everything
```

`CARGO_HOME` lives under `.toolchain/`, and nothing is written to `~/.cargo`. Set `PP_PYTHON` to
choose the Python interpreter (default `python3`).

```python
import pageproof as pp
m = pp.BlockManager(num_pages=1024, block_size=16, namespace=b"model-v1")
h, cached, pages = m.attach(prompt_ids)
plan = m.begin_write(h, len(prompt_ids) - cached)
# ... executor runs plan.input_ids at plan.positions, writes KV to plan.write_slots ...
m.finish_write(plan.ticket)
```

## Scope

v0.2 scope: single-threaded, writes always succeed, no abort, no speculative decoding, no
offload/adopt, no COW. See [TRUSTED.md](TRUSTED.md) for the trusted base and the external
assumptions, and [SPEC_NOTES.md](SPEC_NOTES.md) for a clause-by-clause map from contract to proof.
