# pageproof-rs

A KV-cache block manager for LLM serving, written in Rust and verified with
[Verus](https://github.com/verus-lang/verus) against the pageproof block-manager contract v0.6
([docs/block-manager-contract.md](docs/block-manager-contract.md)).

A **slab arena** is shared by several unit classes. **Paged classes** hold KV pages with prefix
reuse; **drafter classes** are paged classes for a speculative drafter. **State classes** hold
one fixed-size recurrent-state slot per lease. A **coordinator** keeps every operation
all-or-nothing across classes. Slabs are acquired on demand, free slabs first; an idle slab can be
reclaimed even when its pages still have cache keys, and reclaiming revokes them.

On top of the v0.3 arena, v0.6 supports:

- **Speculative decoding** (linear draft chains): a verify ticket feeds up to `λ` drafts and its
  completion commits the accepted prefix. Every lease reserves `μ` positions past its input, so
  `begin_write` and `finish_write` never allocate.
- **Zero-overhead scheduling** with depth `δ = 1`: the next step of a lease can be planned before
  the previous step's token reaches the host (`extend_deferred`), including behind a verify step,
  whose acceptance count bounds the next step's start.
- **Stop**: a completion can end a lease at an EOS inside the accepted span; later tickets become
  orphans that change nothing.

Every public method of `Coordinator` (create, attach, extend, extend_deferred, begin_write,
finish_write, release, inspect, slot_of, arena) is proved on its real body, with machine
integers. Each proof covers:

- the invariant `Valid(S)` (I1–I18: per-class v0.2.1 invariants, slab ownership, confinement,
  live state slots and their provenance, lockstep paged classes, the draft reservation, the ticket
  queue and deferred tail, stopped leases)
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
| `crates/pageproof-core/src/coord_attach.rs`, `coord_ops.rs` | C1–C7 and C2b across classes, arena disjointness, bounds |
| `crates/pageproof-core/src/{idxset,index,arith}.rs` | verified free set, key index, arithmetic |
| `crates/pageproof-core/tests/edge_cases.rs`, `coord_edge_cases.rs` | runtime tests for the §7 table (v0.2.1 through v0.6 rows) |
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

Speculative decoding with a drafter class and ZOS:

```python
sd = pp.Coordinator(1024, 1966080, [96 << 10], [], 16, b"model-v1",
                    drafter_units=[96 << 10], max_drafts=4, zos_depth=1)
h, cached, _ = sd.attach(prompt_ids)
if cached < len(prompt_ids) - 1:                     # a repeat prompt can be cached up to its last token
    p = sd.begin_write(h, len(prompt_ids) - 1 - cached)  # prefill all but the last token
    sd.finish_write(p.ticket)
v = sd.begin_write(h, 1, drafts, propose=True)       # verify step: the last token + drafts
sd.extend_deferred(h)                                # plan the next step now
c = sd.begin_write(h, 1, propose=True, deferred_drafts=4)
# The device runs v, then c. If v accepted n1 drafts, c's window in paged class i is
#   c.write_slots[i][n1 : n1 + c.num_inputs + c.num_drafts]
# plus max_drafts proposal rows in a drafter class with propose (D24, E13).
sd.finish_write(v.ticket, accepted=n1, token=bonus1)
sd.finish_write(c.ticket, accepted=n2, drafts=accepted_drafts_of_c)
```

The v0.2.1 single-pool API is still available as `pp.BlockManager(num_pages, block_size, namespace)`.

## Scope

v0.6 scope: single-threaded, writes always succeed, no abort, linear draft chains only (no tree
drafts), one state slot per lease (the executor rebuilds the accepted state in place, E11), ZOS
depth at most 1, drafter classes paged only, no offload/adopt, no COW, no state checkpoints (so no
prefix hits when a state class exists), no static caches in the arena. See [TRUSTED.md](TRUSTED.md) for the trusted base and the external
assumptions, and [SPEC_NOTES.md](SPEC_NOTES.md) for a clause-by-clause map from contract to proof.
