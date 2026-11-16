# pageproof-rs

[![Lint](https://github.com/UranusSeven/pageproof-rs/actions/workflows/lint.yml/badge.svg)](.github/workflows/lint.yml)

**A formally verified cache manager for LLM serving.** Written in Rust and proved with
[Verus](https://github.com/verus-lang/verus) against the
[pageproof contract v0.6](docs/block-manager-contract.md).

Every public `Coordinator` method is proved on its real body, with machine integers. Each one
keeps the invariant, meets its functional spec, and changes nothing when it returns an error.

- **Hybrid models:** KV pages, drafter KV and recurrent state share one memory arena.
- **Prefix caching** with chained SHA-256 keys.
- **Speculative decoding:** linear draft chains; a completion commits the accepted prefix.
  `begin_write` and `finish_write` never allocate.
- **Zero-overhead scheduling:** plan a lease's next step before the previous token reaches the
  host, even behind a verify step.
- **Stop:** end a lease at an EOS inside the accepted span; later tickets become no-op orphans.

## How it works

```text
                 Coordinator
       ┌──────────────┼──────────────┐
    Manager        Manager       StatePool
    (paged)       (drafter)       (state)
       └──────────────┼──────────────┘
         Slab arena: N slabs of S bytes
```

- **Coordinator** (`coord*.rs`) is the public API. It runs all paged classes in lockstep, so one
  handle or ticket names the same lease in every class. Operations are all-or-nothing: if any
  class cannot satisfy a call, the call fails and no class changes.
- **Manager** (`manager.rs`, `ops_*.rs`) runs one paged class: leases, page tables, reference
  counts, the prefix-cache index and the ticket queue. State classes use a simpler `StatePool`
  (`state.rs`) that gives each lease one recurrent-state slot.
- **Slabs** (`slabplan.rs`, `ops_slab.rs`) are the unit of memory. Each slab is free or owned by
  one class, which splits it into units of its own size. Classes take slabs on demand, free slabs
  first. When none are free, an idle slab is reclaimed from another class, even if its pages still
  have cache keys; reclaiming revokes them.

## Quick start

```bash
./scripts/setup.sh       # pinned Verus into .toolchain/, Rust 1.99.1 via rustup
./scripts/all-checks.sh  # lint, verify, audit, build, test
```

| Script | Does |
|---|---|
| `verify.sh` | Runs Verus with a fixed rlimit; fails on any error or timeout |
| `audit.sh` | Checks proof escape hatches: exactly one `external_body`, the SHA-256 call |
| `lint.sh` | Clippy on the whole workspace, warnings as errors |
| `build.sh` | Verify and audit, then build the core and `python/pageproof.so` |
| `test.sh` | Rust edge-case tests, the Python demo and the chunked prefill example |

Nothing is written to `~/.cargo`: `CARGO_HOME` lives under `.toolchain/`. Set `PP_PYTHON` to pick
the Python interpreter (default `python3`). CI runs the lint gate on an arm64 macOS runner.

## Python

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

Chunked prefill: `attach` allocates pages for the whole prompt, and each chunk is one ticket that
advances the computed frontier. Every block a chunk completes is published, so a request with the
same prefix attached mid-prefill reuses the blocks finished so far.

```python
h, done, _ = co.attach(prompt_ids)
while done < len(prompt_ids):
    plan = co.begin_write(h, min(chunk, len(prompt_ids) - done))  # positions [done, done + n)
    # ... executor reads the KV of [0, done) through plan.page_tables and writes the chunk ...
    done = co.finish_write(plan.ticket)              # the new computed frontier
```

Speculative decoding with a drafter class and zero-overhead scheduling:

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

See [python/demo.py](python/demo.py) for a runnable end-to-end demo, and
[python/chunked_prefill.py](python/chunked_prefill.py) for chunked prefill in a scheduler loop that
mixes prefill chunks with decodes.

## Layout

| Path | Contents |
|---|---|
| `crates/pageproof-core` | The verified core: the three layers above, plus `spec.rs` (encodings, chained key), `e8.rs` (SHA-256 wrapper), `model.rs` (abstract `Valid(S)`) and verified helpers `idxset.rs`, `index.rs`, `arith.rs` |
| `crates/pageproof-core/tests` | Runtime tests for the contract's §7 edge-case table |
| `crates/pageproof-py` | Thin PyO3 bindings (unverified I/O shim) |
| `crates/pageproof-client` | A verified client that uses the public specs |
| [SPEC_NOTES.md](SPEC_NOTES.md) | Clause-by-clause map from contract to proof |
| [TRUSTED.md](TRUSTED.md) | Trusted base and external assumptions |

## Scope

Not yet supported: multiple threads, aborting a write (writes always succeed), tree drafts, more
than one state slot per lease (the executor rebuilds the accepted state in place), scheduling
depth above 1, non-paged drafter classes, offload/adopt, COW, state checkpoints (so no prefix hits
when a state class exists), and static caches in the arena.
