# pageproof-rs

A KV-cache block manager for LLM serving, written in Rust and verified with
[Verus](https://github.com/verus-lang/verus) against the pageproof block-manager contract v0.3
([docs/block-manager-contract.md](docs/block-manager-contract.md)).

v0.3 adds a **slab arena** shared by several unit classes. **Paged classes** hold KV pages with
prefix reuse. **State classes** hold one fixed-size recurrent-state slot per lease. A
**coordinator** keeps every operation all-or-nothing across classes. Slabs are acquired on
demand, free slabs first. An idle slab can be reclaimed even when its pages still have cache
keys; reclaiming revokes them.

Every public method of `Coordinator` (create, attach, extend, begin_write, finish_write, release,
inspect, slot_of, arena) is proved on its real body, with machine integers. Each proof covers:

- the invariant `Valid(S)` (I1–I15: per-class v0.2.1 invariants, slab ownership, confinement,
  live state slots and their provenance, lockstep paged classes)
- the method's functional postcondition, including the exact capacity rule `Cap(d, Prot)` and the
  slab-plan relation (each class gains exactly `need_c` slabs; reclaim only when free slabs run
  out)
- strong failure atomicity on every declared error, across all classes

Arena disjointness is a theorem: owned units of different classes never overlap
(`Coordinator::theorem_arena_disjoint`). Metadata is bounded by the unit counts
(`Coordinator::lemma_bounded`). The v0.2.1 single-class `Manager` is still exported and verified.

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
| `crates/pageproof-core/src/ops_*.rs` | v0.2.1 C1–C6 and their preservation proofs; `ops_slab.rs`: slab grant/reclaim on one paged class |
| `crates/pageproof-core/src/state.rs` | state class: live slots and their ghost provenance |
| `crates/pageproof-core/src/coord.rs` | `Coordinator`, its invariant, public view `CoordV`, `Cap`, C0 |
| `crates/pageproof-core/src/slabplan.rs`, `cnt.rs` | the §3.5 slab plan and its counting proofs |
| `crates/pageproof-core/src/coord_attach.rs`, `coord_ops.rs` | v0.3 C1–C7, arena disjointness, bounds |
| `crates/pageproof-core/src/{idxset,index,arith}.rs` | verified free set, key index, arithmetic |
| `crates/pageproof-core/tests/edge_cases.rs`, `coord_edge_cases.rs` | runtime tests for the §7 table (v0.2.1 and v0.3 rows) |
| `crates/pageproof-py` | thin PyO3 facade (unverified I/O shim) |
| `crates/pageproof-client` | a verified client that uses the public specs |
| `python/demo.py` | end-to-end demo through Python |

## Usage

```bash
./scripts/setup.sh       # pinned Verus into .toolchain/, Rust 1.99.1 via rustup
./scripts/verify.sh      # Verus, fixed rlimit; fails on any error/timeout
./scripts/audit.sh       # escape-hatch audit (exactly one external_body: E8)
./scripts/lint.sh        # Clippy on the full workspace (including tests)
./scripts/build.sh       # verify + audit, then build core + python/pageproof.so
./scripts/test.sh        # Rust edge-case tests + Python demo
./scripts/all-checks.sh  # everything
```

`CARGO_HOME` lives under `.toolchain/`, and nothing is written to `~/.cargo`. Set `PP_PYTHON` to
choose the Python interpreter (default `python3`). The lint gate uses the pinned Rust toolchain
and treats Clippy warnings as errors, with exceptions for proof-sensitive Verus code and items
used only during verification. Run `scripts/verify.sh` for proof checking; Clippy does not verify
contracts. Formatting is not part of the lint gate because existing Verus sources are not
`cargo fmt --check`-clean. GitHub Actions runs the same lint gate on pushes and pull
requests using an arm64 macOS runner and the pinned toolchains
([lint workflow](.github/workflows/lint.yml)).

```python
import pageproof as pp
# 1024 slabs of 1.875 MiB = lcm(96 KiB page, 640 KiB recurrent state).
co = pp.Coordinator(num_slabs=1024, slab_bytes=1966080, paged_units=[96 << 10],
                    state_units=[640 << 10], block_size=16, namespace=b"model-v1")
h, cached, lease = co.attach(prompt_ids)        # lease = {"tables": [...], "slots": [...]}
plan = co.begin_write(h, len(prompt_ids) - cached)
# ... executor writes KV to plan.write_slots[c], reads/writes state in plan.state_slots,
#     initialising them first when plan.init is set ...
co.finish_write(plan.ticket)
```

The v0.2.1 single-pool API is still available as `pp.BlockManager(num_pages, block_size, namespace)`.

## Scope

v0.3 scope: single-threaded, writes always succeed, no abort, no speculative decoding (including
state rollback), no offload/adopt, no COW, no state checkpoints (so no prefix hits when a state
class exists), no static caches in the arena. See [TRUSTED.md](TRUSTED.md) for the trusted base and the external
assumptions, and [SPEC_NOTES.md](SPEC_NOTES.md) for a clause-by-clause map from contract to proof.
