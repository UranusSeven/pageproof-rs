# Block Manager Functional Contract v0.8 (draft)

Status: specification draft for review. v0.8 is **not yet implemented**. `crates/pageproof-core` implements v0.7, and Verus proves every public method against v0.7's C0–C8 and C2b. v0.7 added the hit limit and `probe` of D26 and the extend rule of D27 to v0.6 (`Coordinator`, merged in [pageproof-rs#7](https://github.com/UranusSeven/pageproof-rs/pull/7)). `SPEC_NOTES.md` maps each v0.7 clause and §9.1 obligation to its proof and lists the deviations, among them that the refinement obligations 14, 18, 20, 24 and 28 are not proved as observational equivalences. With an empty host tier (`N_H = 0`), v0.8 behaves exactly like v0.7 (§9.1 obligation 31), so the v0.7 proofs are the base for v0.8. By design, with `δ = 0`, v0.6 behaves exactly like v0.4.1 (obligation 20). With `δ = 0`, `λ = 0` and no drafter class, it behaves exactly like v0.3 (obligation 18). With `λ = 0`, it behaves exactly like v0.5 (obligation 24). `attach(T)` of v0.7 is v0.6's attach, and v0.7's extend succeeds wherever v0.6's did (obligation 28). So the v0.3 proofs were the base for v0.4.1, v0.4.1 for v0.5, v0.5 for v0.6, and v0.6 for v0.7.
Date: 2026-11-19 (v0.7: 2026-11-17; v0.6: 2026-11-13; v0.5: 2026-11-12; v0.4.1: 2026-11-12; v0.4: 2026-11-12; v0.3: 2026-11-04; v0.2.1: 2026-11-03; v0.2: 2026-11-02; v0.1: 2026-11-01).
Reference code: nano-vLLM `bb823b3e06983d71485a8e1f23715ebd87d98ef8`: `block_manager.py`, `sequence.py`, `scheduler.py`; `prefix_keys` in `shell/offload.py` (the existing implementation of chained keys).
Layout reference: DeepInfer `0d0a93ff09c99af7a8521f230e16507bf3e00dda`: `deepinfer/kv_spec/kvspec.py` (`LogicalSpec`, `layout`, `PhysicalPlan`), `deepinfer/kv_spec/deepseek_v4.py`, `deepinfer/worker/kv_cache_views.py`.
Speculative-decoding reference: vLLM `9d61ade7f657833df27e43c4561455523c78c8fb`: `vllm/models/kimi_k3/nvidia/ops/recoverssm.py` (`_kda_recoverssm_verify_kernel`, `_commit_kda_state_kernel`, `_compact_conv_state_kernel`), `vllm/model_executor/layers/mamba/abstract.py` (`num_speculative_blocks`), `vllm/model_executor/layers/mamba/mamba_utils.py` (`append_kda_recoverssm_record`), `vllm/v1/worker/gpu/model_states/recoverssm.py` (`RecoverSSMState.commit_step`).
Drafter model: an MTP drafter that, in the verify forward, projects the target model's hidden states from a few selected layers into drafter keys at every verified position, and then proposes all `λ` drafts in one further forward (D20).
Zero-overhead scheduling (ZOS): requested in [pageproof-rs#2](https://github.com/UranusSeven/pageproof-rs/issues/2).
ZOS-with-speculation reference: vLLM `9d61ade7f657833df27e43c4561455523c78c8fb`: `vllm/v1/core/sched/async_scheduler.py` (spec-token placeholders).
Offload reference: vLLM `9d61ade7f657833df27e43c4561455523c78c8fb`: `vllm/v1/kv_offload/base.py` (`OffloadingManager`), `vllm/v1/kv_offload/cpu/manager.py` (`ref_cnt`, `prepare_store`, `complete_store`), `vllm/distributed/kv_transfer/kv_connector/v1/offloading/scheduler.py` (`request_finished`, and the flush of pending stores whose blocks are re-allocated).

Changes in v0.8 relative to v0.7:
- A **host tier**: a second slab arena of `N_H` slabs of `S_H` bytes in host memory (DRAM), owned by the coordinator. Every paged class, target and drafter, has a **host class** with the same unit size and in-unit layout. Host classes hold cache entries only: no leases, page tables, frontier or tickets of their own. They take and give up host slabs by §3.5's slab plan, and capacity is the same predicate over the host arena (D28, D29, §3.1, §3.5).
- **Store** (C9 `begin_store`, C10 `finish_store`): copies complete blocks of a lease into fresh host units, and never evicts the host copies of the blocks in its range that it skips. Each source page holds a **store reference** until the store completes, so a lease can be released while its stores are in flight, and no stored page is reused under the copy. A store credits nothing in the device arena, so it may fail (D30).
- **Load**: attach continues the device hit run with the blocks that every host class holds, up to the same limits. Those blocks get fresh pages, and a **load ticket** heads `Q_h`; its completion through `finish_write` credits, publishes and unpins them. `c_h` still advances only when a ticket completes (D31, C1, C4).
- probe also returns how many of its tokens a load would copy (C8).
- I2 counts store references; I6, I7, I9, I10, I11, I12 and I13 are restated for stores, load tickets and the host arena. New invariants I19–I22 and the copy-isolation theorem (§4). E4 is restated (a store may fail); new assumptions E14 (copy executor) and E15 (host arena). New proof obligations 31–37, and the refinement obligations 14, 18, 20, 24 and 28 now assume no host tier.

Changes in v0.7 relative to v0.6:
- attach takes a **hit limit** `κ`: `k*` is also capped at `floor(κ/B)` blocks, so `c_h = k*·B <= κ`. A scheduler that decides where a request resumes (it asks where a prefix resumes, then schedules the request's first step from that position, or from 0 to compute it cold) passes that position. `attach(T)` is `attach(T, L)`, which caps nothing, so v0.6 callers see no change (D26, C1).
- New read-only **C8 `probe(T, κ)`**: the `c_h` that `attach(T, κ)` would set now, without attaching. A scheduler asks it to rank candidates and to answer where a request resumes (D26).
- **extend no longer needs `p_h = L_h`**: known tokens may wait to be scheduled, as after attach. A scheduler that plans steps ahead of execution learns a request's tokens before earlier positions are computed; it appends them, and its tickets cover them later. extend_deferred keeps `p_h = L̂_h` (D27, C2).
- New proof obligations 28–30. I1–I18 are unchanged.

Changes in v0.6 relative to v0.5:
- ZOS combined with speculative decoding. A verify ticket, or a ticket with a proposal, may have a ticket queued behind it. Such a **continuation** takes as input the producer's bonus token and up to `λ` drafts that the producer's proposal forward made on the device. None of these are on the host when the continuation is issued (D21, D22, D24).
- A pending ticket's start is a **bounded start**: a host-known lower bound `lo` plus an unknown shift in `[0, s]`, where the slack `s` is the number of drafts that older pending tickets may still accept. The plan lists write slots for every position the ticket can write, and the executor uses the resolved window inside them (D24, §3.3, C3).
- The reservation covers the longest outcome of every ticket in flight: `μ = (δ + 1)·λ`, plus `λ` with drafter classes. `begin_write` and `finish_write` still never allocate, and a rejection still never frees (D18, I16).
- A continuation's completion reports the drafts it accepted, because the host never saw them. The block manager now records accepted drafts that the drafter proposed on the device (D22, C4).
- A completion may carry `stop`. It commits a prefix of what the device accepted, marks every younger ticket of the lease **orphaned**, and makes the lease terminal: orphans complete in order without crediting anything, and the lease can only be inspected or released (D25, C4).
- New invariant I18 (orphans and stopped leases). I9, I11, I15, I16 and I17 are restated over bounded starts. E11 and E13 are restated for continuations. New proof obligations 24–27.

Changes in v0.5 relative to v0.4.1:
- Zero-overhead scheduling (ZOS) with depth `δ ∈ {0, 1}`, fixed at create. A lease may hold up to `δ + 1` pending tickets. Each later ticket starts at the planned frontier `p_h`, the end of the ticket before it, and a lease's tickets complete in issue order (D21, §3.4, C3, C4).
- A token that is not yet on the host is a position of the deferred tail `X_h`, which follows `T_h`. `extend_deferred` appends one such position, produced by the newest pending ticket. That ticket's completion reports the token, and `finish_write` appends it to `T_h` (D22, C2b, C4).
- Keys, publication, I4, I5 and I5b are unchanged. In-order completion keeps every position below `c_h` inside `T_h`, so no key is ever computed over an unknown token (D23).
- `extend` may run while pipelined tickets are pending. Verify tickets and tickets with a proposal are never pipelined, so ZOS combined with speculation stays out of scope (D21, §1.1).
- New invariant I17; I9, I11 and I16 are restated over queues of `δ + 1` tickets and the planned input length `L̂_h`. New assumption E13. New proof obligations 20–23.

Changes in v0.4.1 relative to v0.4:
- The draft track is removed. Drafter paged classes `Cx` are paged classes on the one frontier `c_h`, with the same key chain and the same tickets as the target classes, because the drafter writes its KV at every position of a ticket in the same forward, from the target model's hidden states (D14, D20, E12).
- A ticket that ends at the end of the input may carry a proposal. Its plan extends the drafter classes' write range by `λ` positions, where the drafter's single proposal forward writes `λ` rows after the accepted prefix. No frontier is ever credited for proposal rows (D20, C3).
- With drafter classes, the reservation grows from `λ` to `μ = 2λ` positions past the input, so a proposal always fits (D18, I16).
- Removed: the draft frontier `e_h`, `begin_draft` (C3b), the ticket's track, and the per-class frontier notation `f_h^c` (every class now uses `c_h`). Drafters whose KV at accepted positions comes from a separate forward over those tokens become a non-goal (§1.1). D14, D20, E12 and obligation 17 are restated for drafter classes.

Changes in v0.4 relative to v0.3:
- Speculative decoding with linear draft chains. A target ticket may carry up to `λ` draft tokens after the end of the input. Its completion reports how many were accepted. The frontier advances past the accepted drafts, they are appended to `T_h`, and rejected drafts never enter `T_h` (D16, D17, §6 C3, C4).
- Every lease reserves capacity for `λ` positions beyond its input, so `begin_write` and `finish_write` still never allocate and a rejection never frees (D18, I16).
- State classes keep exactly one slot per lease. The executor rebuilds the state at the accepted length inside that slot, from the checkpoint and per-token records, as vLLM's KDA RecoverSSM does (D19, E11).
- Optional draft paged classes form a second track with their own frontier `e_h` and their own tickets (`begin_draft`). This replaces D14's single frontier with one frontier per track. The draft frontier never moves past `T_h`, so draft KV at tentative positions is never trusted (D14, D20).
- New invariant I16; I1, I4–I6, I9, I11 and I15 are restated over tracks and the reservation. New assumptions E11, E12. New proof obligations 15–19.
- Ticket bookkeeping is stated as a queue: each lease keeps its pending tickets in issue order, at most `Q = 1` of them, and a target ticket starts at the planned frontier `p_h`. The invariants on a pending ticket say how the lease may change while the ticket is live (it may only grow) instead of saying that nothing changes. With `Q = 1` this is exactly the single pending ticket of v0.3. It lets v0.5 (zero-overhead scheduling) raise `Q` without restating I9 (§3.4, I9, I11, C3, C4, §9.0).

Changes in v0.3 relative to v0.2.1:
- Physical memory becomes a slab arena: `N` slabs of `S` bytes, each free or owned by exactly one unit class. Several managers share it, replacing the "separate pools per manager" rule of §1 (D10–D12, §3.1, §3.5).
- Unit classes have their own unit size. Paged classes keep the v0.2.1 page semantics. State classes hold one fixed-size, in-place recurrent state slot per lease (D13).
- Base assumption A1: every unit size divides the slab size (`S = lcm` of the unit sizes is the smallest choice). It is checked at create, and it makes unit addressing `g·u_c` valid for existing block-table kernels (§3.1).
- A slab whose units all have `ref = 0` is reclaimable even when its pages are still keyed; reclaiming revokes those keys (D11). Capacity becomes the exact per-class-plus-slab predicate `Cap` (§3.5).
- A coordinator owns handles, tickets, inputs and the frontier, and makes every multi-class operation atomic (D14). One ticket's plan covers every class.
- No state cache hits in v0.3: a lease of a configuration with a state class always attaches with `k* = 0` (D13, §6 C1). Spec-decode rollback stays a non-goal (resolved for linear chains in v0.4).
- New invariants I12–I15; I1, I3, I8 and I11 are restated over dynamic unit universes. New assumptions E9, E10. New proof obligations 10–14.

Changes in v0.2.1 relative to v0.2: new invariant I11 (bounded metadata) with the supporting fact I11a (§4). I8 is tightened: a key whose candidate set is empty keeps no stored Index entry. §7 adds a churn edge case, and §9.1 adds proof obligation 9.

Changes in v0.2 relative to v0.1:
- Keys became chained 256-bit digests that serve as both identity and index key. Collisions enter the trusted base as an explicit probabilistic assumption (D4, §3.3, §9).
- Added the completeness invariant I5b, the `den` ghost, and concrete `Canon`/`Enc` encodings (§3.3).
- Added the representation and derived invariants of `Index`/`Pending` (§3.4).
- Made explicit: single-threading, writes always succeed, non-goals, and the main theorem and external assumptions (§5, §1.1, §9.0).
- C1 gained `IdentifierExhausted`, and page-table views are snapshots.
- `Pending` dropped the redundant `table_ver`.

## 1. Goals and responsibilities

The goal is an executable block manager that admits static program proof. The proof must cover the actual method bodies and their calls, not merely check runtime traces or verify a separate model.

The system has three layers behind one public interface:

- **Slab arenas.** The device arena of `N` slabs of `S` bytes, and, from v0.8, an optional host arena of `N_H` slabs of `S_H` bytes in host memory (DRAM). Each gives slabs to unit classes and reclaims them. It never moves or compacts a slab.
- **Unit-class managers.** Each class `c` cuts its slabs into units of `u_c` bytes. A paged class manages KV pages with the v0.2.1 semantics (page tables, prefix reuse, publication). A state class manages one fixed-size live state slot per lease. Paged classes hold the target model's KV or the drafter's KV (drafter classes `Cx`); state classes belong to the target model. Every paged class has a host class in the host arena, with the same unit size, that holds copies of published pages: cache entries only, with no leases or frontier (D28).
- **Coordinator.** Owns leases, inputs, deferred tails, the computed frontier, the draft reservation, ticket queues and pending stores. It turns each public operation into an all-or-nothing change across both arenas and every class.

This module is responsible for: slab ownership, physical unit allocation in every class, request page tables and state slots, whole-block prefix reuse in paged classes (keyed by chained digests), capacity growth including the draft reservation, the computed frontier, unit protection during execution (including pipelined tickets), committing accepted drafts and deferred tokens, cache publication, reference release, and, from v0.8, copying published blocks to the host tier and back, with the units of every copy in flight protected.

Choosing draft tokens and deciding acceptance (rejection sampling) belong to the executor and the sampler. The block manager only records the drafts a verify ticket feeds and the acceptance count its completion reports. It sees proposed tokens only after acceptance: a continuation's completion reports the drafts it accepted (D22), and rejected proposals never reach the block manager.

The following semantics belong to other modules: choosing which requests to schedule each step, prefill/decode priority, token budget, EOS and max_tokens, the model's context limit, the byte layout inside a unit (the KV spec planner, e.g. DeepInfer's `kvspec.layout`), numerical correctness of the model, GPU kernels and communication, and moving bytes between the arenas (the copy engine, E14). Which blocks to store and when, and whether a request should load or recompute, are scheduling policy: the caller chooses them through `begin_store` and the hit limit `κ`. The block manager does not modify this business state.

The module guarantees that the page tables, state slots and plans it outputs conform to this contract; the external executor must execute according to the plan. The correctness guarantees hold only given a fixed KV namespace, valid external completion events, and a correct executor.

One coordinator serves one model configuration and owns its arenas. External code cannot bypass it to overwrite completed KV, write a live state slot, or reuse a unit in either arena. Several coordinators need separate arenas; sharing one arena, device or host, across coordinators is out of scope.

### 1.1 Explicit non-goals and write assumption for v0.8

v0.4 supports speculative decoding with **linear draft chains**: a verify ticket feeds the last input token followed by up to `λ` drafts, and its completion accepts a prefix of them. Rejected drafts never enter `T_h`, so no truncate primitive is needed (D17). v0.5 adds zero-overhead scheduling for steps without drafts or proposals: up to `δ` further steps of a lease may be planned before the previous step's sampled token reaches the host (D21, D22). v0.6 lets such a step follow a verify step whose acceptance count is not yet known: the step's start is bounded, and its inputs and drafts come from the device (D24). v0.8 adds a host tier: published blocks can be stored in host memory and loaded back when a lease attaches (D28–D31). The following capabilities are still not in this version's state machine. Callers must handle them separately and must not treat them as proved properties:

- Tree drafts (EAGLE-2, Medusa trees): the accepted path would sit in non-contiguous slots, which needs a KV compaction step in the plan.
- More than one state slot per lease for rollback (vLLM's default path, which keeps `num_speculative_tokens` extra state blocks per request, or kvspec `State.copies > 1`). This contract keeps exactly one slot and relies on the executor to rebuild the accepted state inside it (D19, E11). A state executor that cannot do that must run with `λ = 0`.
- Host-known drafts behind a pending ticket: a ticket whose drafts the host already holds (n-gram prompt lookup, an external proposer) needs an empty ticket queue. Behind a pending ticket, drafts come only from that ticket's proposal forward on the device (D21, D24).
- Device proposers without KV in the arena (a device n-gram proposer): `propose` requires `Cx ≠ ∅`, so ZOS with speculation needs a drafter class.
- Drafter state classes (a drafter with recurrent layers). Drafter classes are paged only.
- Drafters whose KV at an accepted position is computed in a separate forward over the accepted tokens, instead of in the ticket's own forward: an independent small draft model that runs behind the target, or vLLM's EAGLE proposer, whose re-feed pass shifts the input so that the drafter KV at j depends on the token at j+1. Such a drafter needs its own frontier and its own tickets (the draft track of v0.4).
- State cache hits: there are no state checkpoints. A state slot is never keyed, published or shared, so a configuration with a state class never reuses a prefix (D13), from the device arena or from the host tier. State classes have no host class. kvspec's `on_hit` (`restore` / `replay` / `empty`) is ignored by v0.3 through v0.8.
- External KV import (adopt): the only way to advance `c_h` is the executor's completion event for a ticket. A v0.8 load ticket imports KV only from this coordinator's own host tier. Importing from another instance or a shared store, as a disaggregated decode instance or a store service would, needs further primitives.
- Write-back of cached pages: `begin_store` copies blocks of a live lease. A cached page that no lease holds cannot be stored, so a fresh allocation or a reclaim that revokes it loses it.
- Failed loads: a load ticket must complete successfully, like a compute ticket (E4). Only a store may fail.
- Loading at extend: only attach looks up the host tier, so a lease grown by extend gets no host hits for its suffix.
- A host tier shared by several coordinators, and tiers beyond host memory (local disk, remote stores).
- Static caches shared by all requests (kvspec `Static`, e.g. sink tokens): allocated by the caller outside the arena.
- Windowed lifetimes: sliding or tumbling windows and rings, which free or overwrite the pages a lease no longer reads. A lease keeps every page of its input, so such a layout only runs as if every state were full.
- Layers that read tokens after their position (a token shift). Whether a layer does depends on where it stores each entry. The first MTP module combines the target model's hidden state at p with token p + 1; stored at p, as vLLM stores it, that entry reads a token after its position. That breaks E2 (E12(1) in a drafter class), which needs each entry to depend only on the tokens up to its own position, and no hit limit repairs it. `κ = 0` keeps other leases from reusing a published block's last entries, which depend on a token outside the block's key. Within one lease, though, the token after a position can still differ from the one its entry read: after a verify that rejects a draft, the entry at the last accepted position read the rejected draft, and a teacher-forced token appended with extend while the step that computes the position before it is in flight need not be the token that step's entry read. So stored at p, such a layer is outside this contract, with or without hits. Stored at p + 1 instead, the entry depends only on tokens up to its own position and hits are exact. But a lease that attached with a hit of `k*` blocks must then compute the entry at `k*B` from the hidden state at `k*B - 1`, which no page holds unless the executor also stores it in block `k* - 1`'s page, whose key covers everything it depends on.
- Slab compaction, defragmentation, or moving a live unit.
- ZOS depth above 1 (`δ >= 2`): create rejects it. Stop (D25) would cover the EOS case of v0.5, but deeper queues need the reservation and the bounded-start rules restated for chains of continuations (§10).
- Multi-threaded concurrent calls: see the single-thread assumption E3 in §5.

This version **assumes writes always succeed** (E4): every issued ticket, load tickets included, eventually completes successfully, with no failed completion, silent drop, or process termination. There is therefore no abort path, and no promise of progress under GPU faults (see C4). Rejecting drafts is not an abort: the completion is successful and reports how many drafts were accepted. A store is not a ticket: it may complete as failed, and then publishes nothing (C10).

Until these primitives exist, an adapter must not claim to cover every feature of the existing scheduler (in particular tree `spec_decode`, and `store` beyond this coordinator's own host tier).

## 2. Design decisions adopted in this version

| ID | Decision | Rationale or cost |
|---|---|---|
| D1 | Each coordinator fixes `N`, `S`, the class table, `B` and the KV namespace; there is no globally mutable block size | Multiple processes or instances do not depend on one implicit global value |
| D2 | attach reserves pages in every paged class for all current input tokens, and one slot in every state class | Keeps upstream's eager allocation; chunked prefill only advances the computed frontier |
| D3 | Reuse only a contiguous prefix of completed whole blocks; attach always leaves the last logical block for recomputation. With a state class present, `k* = 0` (D13) | Keeps upstream's convention for computing the first output; the last block is excluded even when the input length is an exact multiple of B |
| D4 | Cache hits are decided by chained 256-bit digest identity; the digest is also the index key | The key is a chain `H(parent, block)`, O(1) per block. Identity exactness rests on "SHA-256 is collision resistant" as an explicit probabilistic assumption (E8). No 64-bit practical hash, and no per-candidate exact comparison |
| D5 | Complete prefixes may be shared read-only; units being written must be exclusive; no COW in this version | Writes the boundary between sharing and writing into the spec. A live state slot is written in place but is always exclusive, so it is consistent with D5 |
| D6 | The core interface uses atomic `attach` / `extend` that check capacity and mutate together, across all classes | Avoids relying on possibly stale can_allocate/can_append results, and avoids a lease that got pages but no state slot |
| D7 | `begin_write` / `finish_write` make in-flight work explicit; in-flight requests cannot release, and can extend only as D21 allows | Protects units through a metadata protocol; whether the GPU actually completed remains the executor's responsibility |
| D8 | Keep every published cache entry until its page is reused or its slab is reclaimed; lookup is complete and the hit prefix is the longest | An explicit cache-functionality promise, stronger than upstream's single-valued hash index. Slab reclaim happens only when free slabs do not suffice (D11) |
| D9 | Free-unit choice, eviction order, reclaimed-slab choice, and page choice among equal keys are not fixed, except that a class takes its unkeyed free units before its cached ones (§7); when a referenced hit candidate exists, it is preferred | Leaves room for optimization and ensures no spurious failure when resources suffice |
| D10 | Memory is one arena of `N` slabs of `S` bytes. Unit class `c` has unit size `u_c` with `u_c \| S` (A1, checked at create); `S = lcm_c u_c` is the smallest valid choice and the recommended default. Unit `g` of class `c` occupies bytes `[g·u_c, (g+1)·u_c)` | Each class sees the arena as a regular `[N·n_c, u_c]` array, so block-table kernels that compute `base + id·stride` work unchanged, and a slab has no tail waste. Cost: when the `u_c` share few factors the LCM is large; pad unit sizes (kvspec `stride_align`) to keep `S` reasonable |
| D11 | Slabs are acquired on demand, free slabs first. A slab whose units all have `ref = 0` is reclaimable even if some are keyed; reclaiming revokes those keys. Release never returns a slab; slabs never move | Keeps cached pages as long as possible and lets a class whose pages are all idle give memory to another class. Cost: reclaiming loses cache entries |
| D12 | Capacity is exact per class plus slabs (`Cap`, §3.5). Free units of one class never serve another class unless a whole slab is reclaimed | Keeps success-iff-capacity provable. Fragmentation is part of the contract: free bytes spread over partly used slabs do not count for another class |
| D13 | A state class holds exactly one exclusive live slot per lease, updated in place, never keyed, published or shared. There are no state cache hits in v0.3 through v0.8 | A page-prefix hit is useless without the matching recurrent state, so a configuration with a state class attaches at `c = 0`. Checkpoints and joint hits are deferred (§10) |
| D14 | The coordinator owns handles, tickets, `T_h`, the frontier `c_h`, the reach `ρ_h` and `Pending`. One frontier per lease covers every class, target and drafter, and one ticket's plan covers every class (as in v0.3; v0.4 had a separate draft track with its own frontier) | Multi-class operations are atomic, and frontiers cannot diverge between classes. The drafter writes its KV at every position a ticket writes, in the same forward (D20), so its valid prefix always equals the target's |
| D15 | All paged classes of a coordinator, target and drafter, share `B` and one key chain per lease; each paged class has its own `Index` | The executor computes all classes for the same positions, so they complete the same blocks together. Different `B` per paged class is deferred |
| D16 | Speculative decoding uses linear draft chains of at most `λ` tokens, with `λ >= 0` fixed at create. A **verify ticket** is a ticket whose input reaches the end of `T_h`, followed by `k <= λ` drafts. Its completion reports the accepted count `n <= k` | The accepted drafts are a prefix of the written positions, so their KV is already in the right slots and no copy is needed. Trees are deferred (§1.1) |
| D17 | Drafts are not part of `T_h` until accepted. `finish_write` appends exactly the accepted drafts to `T_h` and sets `c_h` past them. Rejected drafts never enter `T_h`, any key, or any published page | No truncate primitive, and no published state can ever depend on a rejected token. The bonus token sampled after the last accepted position is appended by the caller with `extend`, as in v0.3 |
| D18 | Every lease reserves `μ` positions past the planned input, with `μ = (δ + 1)·λ` when there is no drafter class and `μ = (δ + 1)·λ + λ` otherwise: its page table in every paged class covers the reach `ρ_h = L̂_h + μ` set by the last attach, extend or extend_deferred. `begin_write` and `finish_write` never allocate, and a rejection never frees | A verify never fails for capacity and a completion never fails, which keeps E4. Each of the up to `δ + 1` tickets in flight may write `λ` drafts past its input, and the newest one's proposal rows reach up to `λ` positions past its last draft (D20), hence `(δ + 1)·λ`, plus `λ` with a drafter. With `δ = 0` this is v0.4.1's `λ` or `2λ`; with `λ = 0` it is v0.5's 0. Cost: at most `ceil(μ/B)` extra pages per paged class per lease, held even when the lease is not speculating; with `B = 64`, `δ = 1` and `3λ <= 64` that is one page. Allocating for the longest outcome per step and returning the rest when the step is processed would hold fewer pages (§10); a static reach keeps `begin_write` and `finish_write` allocation-free |
| D19 | A state class keeps exactly one slot per lease when `λ > 0`. A verify ticket's plan names that slot, and the executor leaves in it the state after the accepted prefix. How it does so (checkpoint plus per-token records, recomputation, or extra copies inside the unit) is the executor's business (E11) | Matches vLLM's KDA RecoverSSM path for Kimi K3: verify reads the checkpoint `S_0` without writing it back and saves per-token records; commit rebuilds `S_n` in closed form from `S_0` and the first `n` records. Records cost about `3·head_dim` elements per head per token against `head_dim²` for a full state. The records and the widened conv window live inside the state unit, so `u_c` grows with `λ`, but the slot count stays at one |
| D20 | Drafter paged classes `Cx ⊆ Cp` (possibly empty) hold the drafter's KV in the same arena and on the same frontier as the target classes. A ticket's forward writes drafter KV at every position it writes, `[a, w)`, projected from the target model's hidden states. A ticket that ends at the end of the input may carry a **proposal**: after the sampler has fixed the acceptance count n and the bonus token at `z + n`, the drafter runs one forward over the bonus token and `λ - 1` noise tokens, writes drafter KV at `[z+n, z+n+λ)`, and samples `λ` drafts for the next verify. The plan extends the drafter classes' write range to `[a, w + λ)`, which contains those rows for every n. No frontier is credited for them | Accepted drafter KV is already in its slots when the verify commits, so the drafter needs no frontier, ticket or catch-up pass of its own, and its pages are published and hit like target pages. Proposal rows lie at or past the new frontier `z + n`; the next verify starts at `z + n` and overwrites them with drafter KV from target hidden states. Cost: `λ` more reserved positions (D18). Drafters that compute accepted KV in a separate forward are a non-goal (§1.1). The block manager never sees the proposed tokens |
| D21 | ZOS depth `δ ∈ {0, 1}` is fixed at create, and each lease keeps a FIFO queue `Q_h` of at most `δ + 1` pending tickets. A ticket with host-known drafts needs an empty queue. Behind pending tickets, a new ticket either has known inputs, no drafts and every pending ticket has `k = 0` and no `propose` (as in v0.5), or it is a continuation of the newest pending ticket (D24). A ticket starts where the previous one's input and accepted drafts end, and `finish_write` accepts only the oldest ticket of its lease | With `δ = 1`, step n stays on the device while step n+1 is planned: two tickets per lease. In-order completion matches a scheduler that processes step outputs in step order, and it is what keeps `c_h` a contiguous computed prefix. Host-known drafts cannot follow a pending ticket: a proposer would need tokens the host does not have yet, so behind a pending ticket drafts come from that ticket's proposal forward on the device. `δ >= 2` is rejected at create (§1.1, §10). The rules below are written for a general `δ` so that a later version can lift the cap |
| D22 | A token that is not yet on the host is a position of the deferred tail `X_h`, which follows `T_h`. `extend_deferred(h)` appends one such position, the bonus token of the newest pending ticket of h, with the same capacity rule as `extend`. When that ticket has drafts, the position is counted at its lowest possible place, as if every pending draft were rejected. The producer's completion reports its acceptance count n and the token x, and `finish_write` appends `D[0:n] ++ [x]` to `T_h`. A continuation's completion also reports the drafts it accepted, because they were proposed on the device. An unknown token is never a hole inside `T_h` | `T_h` stays a plain token sequence, so keys, `Enc`, I4, I5 and I5b need no notion of a resolved prefix. The plan names the producer of each deferred input, and the executor gathers the token and the drafts on the device |
| D23 | No separate publication rule for deferred tokens: a block is published when the frontier passes it, as in v0.4.1 | A producer is always older than the ticket that consumes its token, and completion is in issue order, so every position below `c_h` already has its token in `T_h` (I17). An EOS sampled by step n while step n+1 is in flight is appended when step n completes; step n+1 then completes the block, which is published with the real EOS token. Without speculation this needs only `δ <= 1`: step n+1 is the newest ticket and not in `X_h`, so its token is ignored and nothing after the EOS enters `T_h`. With speculation, step n+1 is a continuation whose accepted drafts would follow the EOS, so the caller reports the EOS with `stop` (D25) |
| D24 | A ticket whose input is a deferred token is a **continuation** of that token's producer, the newest pending ticket. Its start is bounded: `a = lo + σ`, where `lo` is known at issue and `σ ∈ [0, s]` is the number of drafts the older pending tickets of the lease will accept, with slack `s` their total draft count. Its drafts, if any, are the ones its producer's proposal forward samples, and the coordinator learns them only from the continuation's completion. The plan lists write slots for every position the ticket can write, `[lo, lo + s + 1 + k)` (plus `λ` in drafter classes with `propose`), and the executor writes the window that starts at `a` | The executor resolves the context and the inputs on the device from the producer's outputs: its acceptance count, its bonus token and its proposal (E13). Listing every slot keeps E5: the executor selects addresses from the plan. A runner that instead derives the slots on the device from the block table and the shifted positions makes the same selection when the block table it reads is the plan's page mapping (E5). A continuation needs no host-known drafts, so the host never waits for the device's proposal. The v0.5 deferred decode is the special case `s = 0`, `k = 0` |
| D25 | A completion may carry `stop`. It commits a prefix of what the device accepted, appends the bonus token only if one is given and the ticket heads `X_h`, orphans every younger ticket of the lease, and makes the lease **stopped**. An orphan completes in issue order and credits, publishes and binds nothing. A stopped lease accepts no new work; it can only be inspected and, once its queue is empty, released | The device does not apply stop rules, so its acceptance count can run past an EOS inside the accepted span, and the continuation already started from that count. After a truncation, the continuation's window starts past the coordinator's frontier and its inputs follow the EOS, so its KV is not KV of `T_h` and must not be credited. Making the lease terminal keeps the frontier and the state slot from ever depending on an orphan's writes |
| D26 | attach and probe take a **hit limit** `κ` from the caller: `k*` is the joint run of hits capped at `ceil(L/B) - 1` and at `floor(κ/B)` blocks. `attach(T)` is `attach(T, L)`. probe returns the position attach would resume from, without changing anything (from v0.8 also the part of it a load would copy, C8) | The scheduler, not the block manager, decides where a request resumes: it asks where a prefix resumes and then schedules the request's first step from that position, or from 0 when it computes the request cold, which it may do even when the prefix is cached. A lease that took more hits than the scheduler planned for would have shared, published pages under positions its step recomputes (I7). With probe, the answer and the attach right after it agree: both compute the same `k*` from the same state |
| D27 | extend appends known tokens whatever the planned frontier: `p_h <= L_h` replaces v0.6's `p_h = L_h`. extend_deferred still needs `p_h = L̂_h` | Known tokens may wait to be scheduled, as they already do after attach (D2). A scheduler that plans steps ahead of execution learns a request's tokens one step at a time, before the steps that compute earlier positions have run; with v0.6 it could not grow the lease until every earlier position was computed or ticketed, and the queue holds at most `δ + 1` tickets. Every other C2 rule stays: no deferred position, Busy behind a ticket with drafts or `propose` or a full queue, and the demand and `Cap` of C2 |
| D28 | The **host tier** is a second slab arena of `N_H >= 0` slabs of `S_H` bytes in host memory, owned by the coordinator. Every paged class c, target and drafter, has a **host class** with unit size `u_c` and c's in-unit layout, under base assumption A1^H: `u_c \| S_H`. A host class holds cache entries only: copies of published device pages, keyed and indexed like them, with no leases, page tables, frontier or tickets of its own. Host slabs move between host classes by §3.5's slab plan. State classes have no host class. `N_H = 0` is no host tier | Host memory is managed like the device arena, so `Cap`, the slab plan, reclaim and the cache rules carry over, and so do their proofs. A host unit is a byte copy of a device page, so a copy converts nothing and a key means the same in both arenas (`den`). A host class needs no frontier, because it holds only whole published blocks, and no coordinator of its own: the coordinator runs the host slab plan and makes each copy all-or-nothing across classes. Mirroring every paged class keeps hits joint: a load needs a block in every host class, as a device hit needs it in every paged class. State classes wait for state checkpoints (D13, §10): a configuration with a state class attaches at `k* = 0` and never loads. Cost: free host units fragment across host slabs as device units do (D12) |
| D29 | A host unit is **referenced** by the pending load tickets that read it and by the pending store that writes it. A host unit is free when it is owned and unreferenced; a free host unit with a key is a host cache entry. Fresh host units are taken unkeyed first, then from cache entries, whose keys are revoked, but never from the copies a store protects (D30). A host slab whose units are all unreferenced is reclaimable even if keyed, and reclaiming it revokes those keys. A host class holds at most one unit per key | These are I2, I3, D9 and D11 with copies in flight in place of leases, so the device arena's proofs of `Cap`, the slab plan and reclaim apply to the host arena. A load's source can be neither evicted nor reclaimed under the copy, and a store's destination cannot be given to another store. A store writes a key only where its host class holds no copy and no store is writing one (D30), so a host lookup has no candidates to choose from |
| D30 | `begin_store(h, i0, i1)` copies the complete blocks `[i0, i1)` of lease h (`i1·B <= c_h`) to the host tier. In each host class it skips the blocks that class holds or a pending store is writing there, and it protects the copies it skips: they count in its demand and their host slabs are not reclaimed, as attach does for the free cache hits it reactivates. It takes a fresh host unit for each remaining block, and adds a **store reference** to that block's device page in the class. It also returns the pending stores it relies on for the blocks it skipped. `finish_store` publishes the host units under the blocks' keys and drops the store references; a failed store frees its host units unkeyed. begin_store is all-or-nothing on host capacity | A store reference is a lease reference without a lease: the page is not free, so it is never reallocated or reclaimed under the copy, and `Cap`, `R_c` and I3 keep their wording. release never waits for a store, and the executor needs no ordering between a store and later writes, because nothing writes a published page (I7) and a page with a store reference is not reused. A store reads only complete blocks, whose bytes no longer change. It credits nothing in the device arena, so it may fail, unlike a ticket (E4). Deduplication keeps one copy per key per host class, as vLLM's store skips blocks that are stored or being stored. Without the protection, a store could evict the host copy of an earlier block of its own range to make room for a later one, and a load, which needs a contiguous run, could then use neither; vLLM likewise never evicts the blocks offered to a store. A store that skipped a block another store is writing relies on that store: if it fails, the block is not in the host tier, and the caller, told which stores it relied on, can store the range again. Cost: a page stays allocated until its store completes, even after its lease is released. Returning the page at release and making a later writer wait for the copy, as vLLM's offloading scheduler does by flushing pending stores whose blocks are re-allocated, would hold fewer pages, at the price of an ordering assumption on the executor (§10) |
| D31 | attach continues the joint device hit run of `k_d` blocks with the **host run**: the blocks after it that every host class holds, under the same limits as `k*` (the last block and `κ`). They get fresh pages, and `c_h = k_d·B`. When the host run is not empty, the lease's first ticket is a **load ticket** for positions `[k_d·B, k*·B)`; it completes with `finish_write`, which credits and publishes those positions. A load ticket feeds no tokens to a model and has no drafts | `c_h` still advances only when a ticket completes, so I4 and publication keep their shape, and a load ticket is a ticket with `k = 0` and no `propose`, which D21, I9, I16 and I17 already allow. With `δ = 1` the first compute step can queue behind the load; with `δ = 0` it waits for the load, as a scheduler waits for an asynchronous load before it schedules the request. The host run starts where the device run ends, because every page above `c_h` must be exclusive and unpublished (I16): a block past `k_d` that the device arena also caches is loaded into a fresh page, not shared. The demand and `Prot` are those of the device run, so whether attach succeeds does not depend on the host tier, apart from the ticket id a load needs. A load reads only host units that a completed store published, so it waits for nothing but its own copy (E14). `κ` bounds the host run too: a scheduler that would rather recompute than load passes `κ = k_d·B`, which probe reports (C8) |

D1–D31 are proposed semantics, not claims that upstream already satisfies them. D4, D6–D8, D10–D14 and D16–D31 in particular require changes to the implementation and interface; this contract does not promise function-by-function compatibility with the old API.

## 3. Abstract state

### 3.1 Fixed configuration

- `N >= 1`: number of slabs, `SlabId = {0,...,N-1}`.
- `S >= 1`: bytes per slab.
- `Classes = Cp ∪ Cs`: a finite, disjoint, ordered set of unit classes. `Cp` (paged classes) contains at least one class that is not a drafter class; `Cs` (state classes) may be empty. `Cx ⊆ Cp` are the **drafter classes** (D20), possibly empty.
- For each class `c`: unit size `u_c >= 1` bytes, with **base assumption A1: `u_c | S`**. Let `n_c = S / u_c >= 1` (units per slab). The unit ids of class `c` are `{0,...,N·n_c - 1}`; unit `g` lies in slab `slab_c(g) = floor(g / n_c)`, and `units_c(s) = [s·n_c, (s+1)·n_c)`.
- `B >= 1`: token slots per unit of every paged class, target and drafter (D15).
- `λ >= 0`: the maximum number of draft tokens per ticket (D16), which is also the number of drafts the drafter proposes in one forward (nextn). `Cx ≠ ∅` requires `λ >= 1`. With `λ = 0` and `Cx = ∅` the configuration is a v0.3 configuration. The **reservation margin** is `μ = (δ + 1)·λ` when `Cx = ∅` and `μ = (δ + 1)·λ + λ` otherwise (D18): `λ` or `2λ` when `δ = 0`, and `2λ` or `3λ` when `δ = 1`. For a state class, `u_c` must already include whatever the executor needs to rebuild the state after a partial acceptance of up to `λ` drafts (per-token records, the widened conv window); this is part of E11, not checked by create.
- `δ ∈ {0, 1}`: the ZOS depth, the number of further steps of a lease that may be planned before the previous step's sampled token reaches the host (D21). `δ + 1` bounds the ticket queue of a lease. create rejects `δ >= 2` (C0, §1.1). With `δ = 0` the configuration is a v0.4.1 configuration.
- `N_H >= 0`: number of host slabs, `SlabId^H = {0,...,N_H-1}`, and `S_H >= 1`: bytes per host slab (D28). With `N_H = 0` there is no host tier, and the configuration is a v0.7 configuration.
- For each paged class `c ∈ Cp`, target and drafter, a **host class**, also written c where the arena is clear from context. Its unit size is `u_c`, with **base assumption A1^H: `u_c | S_H`**, checked at create, also when `N_H = 0` (create without host arguments passes `S_H = S`, which A1 already satisfies). Let `n^H_c = S_H / u_c >= 1`. The host unit ids of class c are `{0,...,N_H·n^H_c - 1}`; host unit g lies in host slab `floor(g / n^H_c)`, and `units^H_c(s) = [s·n^H_c, (s+1)·n^H_c)`. `S_H = lcm_{c ∈ Cp} u_c` is the smallest valid choice. State classes have no host class.
- `Namespace`: the configuration identity that decides cache reusability, an opaque byte string. The final field table should cover model and weight version, adapters, positional encoding/scaling, attention semantics (including sliding window), B, and, for every class, its kind, `u_c` and in-unit layout (the kvspec `LogicalSpec` and `PhysicalPlan` regions). It should align with `Engine.store_identity()`. v0.6 through v0.8 still use a dummy (an implementation may pass a fixed string such as `"dummy-v0.6"`); when `Cx ≠ ∅` it must also cover the drafter (E12). Completeness remains the caller's obligation (E6); the field table is deferred. Host units carry the same keys as device pages, so the Namespace covers them too (E15).
- `Token`: the type of valid token ids; sequences are finite and 0-indexed.

**Addressing.** Unit `g` of class `c` occupies arena bytes `[g·u_c, (g+1)·u_c)`. By A1 this range lies inside slab `slab_c(g)`'s bytes `[s·S, (s+1)·S)`, so a class's units are exactly the arena viewed as a `[N·n_c, u_c]` array. Inside a unit, the kvspec plan decides where each layer's region lies. For a paged class, `u_c` is the plan's paged-pool stride for `block_tokens = B`; for a state class it is the state-pool stride. Arena base alignment is E9.

**Host addressing.** Host unit g of class c occupies host-arena bytes `[g·u_c, (g+1)·u_c)`, inside host slab `floor(g/n^H_c)` by A1^H, and holds the bytes of one page of class c in c's in-unit layout. So a copy between a page and a host unit moves `u_c` bytes verbatim, with no conversion, and both hold the B token slots of one block. The host arena's base and pinning are E15.

**Capacity of a request size.** Let `Fits(m) ⇔ Σ_{c ∈ Cp} ceil(m / n_c) + |Cs| <= N`. This is whether a lease with `m` blocks in every paged class fits in an otherwise empty arena. A lease's block count includes its draft reservation (D18, §3.3).

The abstract spec uses mathematical integers. A concrete implementation must prove that machine-integer arithmetic on slab ids, unit ids, lengths, reaches `L + μ`, counts and byte addresses does not overflow (in particular `N·S` bytes and `N·n_c·B` token slots, and with a host tier `N_H·S_H` bytes and `N_H·n^H_c` host unit ids), and must reject unrepresentable configurations at construction. Other limits, such as CUDA's current requirement that B be a multiple of some value and its int32 slot limit (now on `N·n_c·B` per paged class), must be added explicitly by the corresponding implementation or adapter, never silently ignored.

### 3.2 Mutable state

| Symbol | Meaning |
|---|---|
| `owner[s]` | The class that owns slab s, or `Free` |
| `FS` | `{s | owner[s] = Free}`, the free slabs |
| `U_c` | Derived: `{g | owner[slab_c(g)] = c}`, the units class c currently owns |
| `Req[h]` | An attached lease: the input sequence `T_h` (never modified in place; it only grows, by `extend`, by accepted drafts and by bound deferred tokens), the computed frontier `c_h`, the reach `ρ_h`, for each `c ∈ Cp` a page table `M_h^c`, for each `c ∈ Cs` a live slot `σ_h^c`, the queue `Q_h` of its pending tickets in issue order, with `\|Q_h\| <= δ + 1`, the deferred tail `X_h`, and the flag `stopped_h` (D25) |
| `p_h` | Derived: the planned frontier, `c_h` plus the input length `ℓ_t` of every ticket t in `Q_h`. A new ticket's start bound `lo` is `p_h`. It is a lower bound: the true planned frontier is `p_h + σ`, where `σ ∈ [0, s_h]` is the number of drafts the pending tickets will accept. With `δ = 0`, a ticket is issued only when `Q_h` is empty, so it starts at `p_h = c_h` |
| `s_h` | Derived: the planned slack, the total draft count `Σ k_t` of the tickets in `Q_h`. Zero when no verify ticket is pending, and then `p_h` is v0.5's planned frontier |
| `X_h` | The deferred tail (D22): a sequence of pending tickets of h. Ticket `X_h[i]` will append its accepted drafts and then the token it samples after them; the coordinator does not know that token yet. Counted with every pending draft rejected, it is position `L_h + i`. Empty when `δ = 0` |
| `L̂_h` | Derived: the planned input length `L_h + \|X_h\|`, counted with every pending draft rejected. Every position below `L̂_h` has a token, known (below `L_h`) or deferred. The true planned length lies in `[L̂_h, L̂_h + s_h]` |
| `ρ_h` | The reach of lease h: the number of token positions its page tables cover. Set to `L̂_h + μ` by attach, extend and extend_deferred, unchanged by every other method (D18) |
| `ref_c[g]` | How many active leases reference unit g of class c, plus, in a paged class, how many pending stores read it (at most one, D30) |
| `F_c` | Units of class c that are owned and referenced by no lease or store; for paged classes this includes free cache pages that still hold reusable data |
| `key_c[g]` | Paged classes only: page g's reusable cache identity (a chained 256-bit digest), or None |
| `Index_c[K]` | Paged classes only: all candidate pages of class c whose published key is K |
| `Pending[t]` | A submitted but not yet completed computation or load: the lease, the kind (compute, or load with its host sources, D31), the start bound `lo` and slack `s`, the input length `ℓ`, the draft part (known drafts or a deferred count), the proposal flag, the orphan flag, and execution plan `plan` (§3.4). Its start `a` and input end `z = a + ℓ` are exact once it is the oldest ticket of its lease |
| `V_c` | Paged classes (target and drafter): ghost KV-provenance marker; records the Namespace and full causal token prefix of each token slot of class c. The prefix may run past `T_h` for a slot written at a tentative position or by a proposal |
| `W_c` | State classes: ghost marker; `W_c[g]` is `(Namespace, τ)` when unit g holds the state after prefix τ, or `⊥`. Under ZOS the device may already have run later tickets of the lease, so `W_c[σ_h^c]` is the state the next ticket in issue order reads, not necessarily the slot's current bytes (E13) |
| `owner^H[s]` | The host class that owns host slab s, or `Free` (D28) |
| `FS^H` | `{s \| owner^H[s] = Free}`, the free host slabs |
| `U^H_c` | Derived: `{g \| owner^H[floor(g/n^H_c)] = c}`, the host units host class c currently owns |
| `ref^H_c[g]` | How many pending load tickets read host unit g of class c, plus one if a pending store writes it (D29) |
| `F^H_c` | Host units of class c that are owned and unreferenced, including host cache entries |
| `key^H_c[g]` | Host unit g's cache identity, the key of the block it holds a copy of, or None |
| `Index^H_c[K]` | The host units of class c whose key is K: at most one (D29) |
| `V^H_c` | Ghost provenance of the token slots of host class c, as `V_c`: slot `g·B + b` is slot b of host unit g |
| `Stores[st]` | A pending store: for every `c ∈ Cp`, the pairs `(i, K, g, g^H)` it copies, block i with key K from page g to host unit `g^H` (D30, §3.4) |
| `den` | Ghost used by the proof: a partial function from digest to `(Namespace, full causal prefix)`; it gives chained keys their meaning |

The domain of `den` is exactly the chain outputs `{Seed(ns)} ∪ {K(h,i)}`. It is injective in the ideal model, and E8 covers this for the concrete instance. It is not part of the executable state.

Request handles, execution tickets and store ids use distinct types that cannot be confused, and are bound to the coordinator and to their generation. An invalidated handle, ticket or store id can never become valid again on a later object. If a concrete implementation's counter space is exhausted, it must safely reject new operations and never wrap around and reuse ids. A load ticket is an execution ticket: it shares the ticket space and the queue `Q_h`.

A request in this contract means a block-manager lease, not the scheduler's WAITING/RUNNING/FINISHED state. The scheduler still manages its business requests; releasing a lease does not delete the user request or its output.

### 3.3 Semantic conventions

Let `L_h = |T_h|` and `m_h = ceil(ρ_h/B)`, the number of blocks the page tables cover. In v0.3, `ρ_h = L_h`; in v0.4, `L_h <= ρ_h <= L_h + λ`; in v0.4.1, `L_h <= ρ_h <= L_h + μ`; in v0.5 through v0.8, `L̂_h <= ρ_h <= L̂_h + μ` unless the lease is stopped (I16).

Page-table entry `M_h^c[i]` is the page of logical block i in paged class c. The token-slot index of position j in class c is:

\[
slot_c(h,j)=M^c_h[\lfloor j/B\rfloor]\cdot B+(j\bmod B).
\]

It is defined for `0 <= j < ρ_h` and lies in `[0, N·n_c·B)`. The bytes a slot occupies follow from the unit address `M_h^c[floor(j/B)]·u_c` and the kvspec regions; this contract fixes only the unit.

`c_h` is the length of the contiguous computed prefix, shared by every class (D14): positions `[0,c_h)` have valid KV in every paged class, target and drafter, `[c_h,L_h)` are not all done, and every live state slot of h holds the state after `T_h[0:c_h]` (I15). `c_h <= L_h`. Reserved capacity does not mean the KV is valid, and positions in `[L_h, ρ_h)` never count as computed.

**Draft chains (D16).** A ticket covers an **input interval** `[a,z)` of length `ℓ = z - a >= 1`, and a **draft count** `k` with `0 <= k <= λ`. The oldest ticket of a lease that is not an orphan has `a = c_h`. A later ticket has a **bounded start** `a = lo + σ`: its start bound `lo` and slack `s` are fixed at issue, and `σ ∈ [0, s]` is the number of drafts the older pending tickets of the lease will accept (D24). `k > 0` is allowed only when the input ends at the end of the planned input: for host-known drafts `Q_h` is empty and `z = L_h`; otherwise the ticket is a continuation (below).

- A **ticket** (`begin_write`) has `lo = p_h` and `s = s_h`. A ticket with known inputs has `s = 0`, so its start is exact. It feeds `T_h[a:z] ++ D` at positions `[a, z+k)`, so its **write end** is `w = z + k`. With `k > 0` it is a **verify ticket**: the model's outputs at positions `[z-1, z+k)` are what the sampler checks the drafts against.
- Every ticket has `lo + s + ℓ + k <= ρ_h`, so every position it can write is covered. Positions `[z, w)` are **tentative**: their slots are written, but no frontier is credited for them by the ticket that wrote them.
- **Proposal (D20).** When `Cx ≠ ∅`, a ticket whose input ends at the end of the planned input (`z = L_h` with `Q_h` empty, or a continuation) may carry `propose`. In every drafter class its write end is then `w_c = w + λ`; other classes write `[a, w)`. After sampling, the drafter writes its proposal rows at `[z+n, z+n+λ)`, where n is the acceptance count the device used, and `z + n + λ <= z + k + λ = w_c`. The proposal rows lie at or past the new frontier `z + n`, so no frontier is credited for them.

**Acceptance (D17).** The completion of a ticket reports `n` with `0 <= n <= k`, the number of leading drafts the sampler accepted. Committing it sets `T'_h = T_h ++ D[0:n]` (followed by the bonus token when the ticket heads `X_h`, below) and `c'_h = z + n`. The KV the ticket wrote at positions `[z, z+n)` is then KV of `T'_h`, so it is credited. Slots of the rejected positions `[z+n, z+k)` keep whatever the executor wrote and are rewritten by later tickets. The bonus token the sampler draws at position `z + n` (the model's output after the last accepted draft) is not part of the ticket. Without ZOS the caller appends it with `extend`; under ZOS the ticket is a producer in `X_h` and its completion reports it.

**Deferred tail (D22).** With `δ >= 1`, the caller may plan the next step of a lease before the current step's outputs are on the host. While the newest pending ticket t ends at the planned input end (its input covers position `L̂_h - 1`, and `p_h = L̂_h`), the caller calls `extend_deferred(h)`. This appends t to `X_h`. Position `L̂_h` then has a token, the one t samples after its last input position and its accepted drafts, but its value is unknown. Counted with every pending draft rejected, it is at `L̂_h`; its true place is `z_t + n_t`. When t completes with acceptance count n and token x, and t heads `X_h`, `finish_write` sets `T'_h = T_h ++ D[0:n] ++ [x]` and removes t from `X_h`. So `L_h` grows by `n + 1`, and `L̂_h` grows by n. A ticket that does not head `X_h` produces no token for the coordinator, and a token in its completion is ignored. That is the case for a step whose output the caller drops.

**Continuation (D24).** The ticket issued right after `extend_deferred` is a continuation of t: its input is the one deferred position, `ℓ = 1`, its start bound is `lo = p_h = L̂_h - 1`, and its slack is `s = s_h`, which counts t's drafts. Its true start is `a = z_t + n_t`, the bonus position. It may carry `k <= λ` drafts only if t has `propose`; they are the drafts t's proposal forward samples after the bonus, and the caller gives only their number (`Deferred(k)`). The plan lists write slots for `[lo, lo + s + 1 + k)`, plus `λ` in drafter classes with `propose`, and the executor writes the window `[a, a + 1 + k)` (plus `λ`) inside them. A continuation of a ticket without drafts has `s = 0` and `k = 0`: that is v0.5's deferred decode step.

The tickets of a lease are contiguous: each starts where the previous one's input and accepted drafts end. The last ticket of `X_h` ends at the lowest planned position, so the consumer of a deferred position is the ticket issued right after its producer, and a producer is always older than its consumer. The oldest pending ticket of a lease therefore reads only known tokens: its `z <= L_h` (I17). With in-order completion, every completed position is in `T_h`, and `c_h <= L_h` holds as in v0.4.1.

The cache key of logical block i is a chained 256-bit digest. Let `H` be a 256-bit collision-resistant hash (SHA-256 in the implementation), `Tag` the scheme version (e.g. `"mg-block-key-v1"`), `Canon` the canonical encoding of the Namespace, and `Enc` the fixed-width encoding of B tokens:

\[
\begin{aligned}
Seed(ns) &= H(Tag \,\|\, 0x00 \,\|\, Canon(ns))\\
K(h,0) &= H(Tag \,\|\, 0x01 \,\|\, Seed(ns) \,\|\, Enc(T_h[0:B]))\\
K(h,i) &= H(Tag \,\|\, 0x01 \,\|\, K(h,i-1) \,\|\, Enc(T_h[iB:(i+1)B]))
\end{aligned}
\]

The key does not depend on the class (D15). One chain per lease serves every paged class, and the per-class `Index_c` keeps hits inside their class: a page of class c can only be found through `Index_c`.

**Encoding (E7).** `Canon(ns)` encodes the namespace byte string as `u32 len || ns_bytes`. (While the namespace is an opaque byte string; once it has fields, they are encoded in a fixed order, each as `u32 tag || u32 len || bytes`.) `Enc(blk)` writes each of the B tokens as a 4-byte little-endian uint32, concatenated at fixed width: exactly `4B` bytes. The parent digest is always 32 bytes, and `Tag` with `0x00`/`0x01` provides domain separation, so `Tag || 0x01 || parent || Enc(blk)` splits in only one way. This uniqueness does not depend on the hash (E7); the hash is only responsible for E8. Counterexamples: concatenating variable-length tokens directly, joining strings with a separator, or JSON with unspecified key order can each encode two different prefixes to the same byte string. The collision probability is then 1, not `2^-256`.

`K(h,i)` is defined only for complete blocks, `(i+1)B <= L_h`; an incomplete tail block has no key and is never published. Tokens at tentative positions are not in `T_h`, so no key is ever computed over a draft before it is accepted, and never over a rejected draft. Deferred positions are not in `T_h` either, and none lies below `c_h` (I17), so no key is computed over an unknown token. A key means the full causal prefix `(Namespace, T_h[0:(i+1)B])`, given by the ghost `den`; the chained construction is only its O(1) representation. Any difference in an earlier block must change every later key. The chain guarantees this; "current-block tokens only", "token hash only" or "same length" are all insufficient.

In the ideal hash model (`H` injective) the chain lemma holds:

\[
K(h,i)=K(h',i') \iff ns=ns' \land i=i' \land T_h[0:(i+1)B]=T_h'[0:(i+1)B].
\]

For the concrete instance (SHA-256) the equivalence holds with probability `>= 1 - \epsilon`, `\epsilon <= Q^2/2^{257} + Q/2^{256}`, where `Q` is the number of key generations and comparisons during the deployment (E8). `den` is injective on chain outputs (ideal model), and E8 likewise covers the concrete instance; hence `den(K(h,i)) = (Namespace, T_h[0:(i+1)B])` is the meaning of a key.

A key lives as long as its page stays published: the digest is stored on the page, and the `Index_c` entry is removed when the key is revoked, either because the page is chosen as a new writable page or because its slab is reclaimed. There is no intern table, ancestor chain, or GC. A page that is released but not reused keeps its key (C5), so total metadata is O(owned units) digests (made precise by I11). The chain head (the key of the last published complete block, or `Seed(ns)`) lets `finish_write` compute the keys of new blocks incrementally; it is an implementation detail.

In v0.3 through v0.8, keys are still computed and published when `Cs ≠ ∅`, even though no lease of such a configuration can hit them (D13). This keeps the paged-class semantics identical to v0.2.1 and prepares for state checkpoints. Drafter classes use the same chain and the same frontier: block i of a drafter class is published under `K(h,i)` when the frontier passes it, together with the other paged classes.

**Host copies (D28–D30).** A host unit of class c holds a copy of one published page of class c. When `key^H_c[g] = K` with `den(K) = (ns, τ)` and `|τ| = qB`, host unit g holds the KV of τ's last block: for every `b < B`, `V^H_c[g·B + b] = (ns, τ[0 : (q-1)B + b + 1])`, which is what a published page with key K holds (I5). A block's host and device copies share its key `K(h,i)`, so a hit in either arena means the same prefix. A store of block i of lease h copies page `M_h^c[i]` into a fresh host unit, which is published under `K(h,i)` when the store completes. No forward reads or writes a host unit: host units are written only by stores and read only by load tickets.

**Load ticket (D31).** A load ticket t of lease h is the first ticket of h, issued by attach when the host run is not empty. Its input interval is the host run, `[a, z) = [k_d·B, k*·B)`, with `lo = a = c_h`, `s = 0`, `ℓ = (k* - k_d)·B`, `k = 0`, no `propose` and no producer. It feeds no tokens to a model: for every `c ∈ Cp` and `i ∈ [k_d, k*)`, it copies the host unit of class c whose key is `K(h,i)` into page `M_h^c[i]`. Its completion credits `[a, z)` as a ticket with `n = 0` does: `c'_h = z`, and `T_h` is unchanged. Until then those pages lie above `c_h`, so they are exclusive and unpublished, and no other plan writes them (I16).

### 3.4 Representation of Index and Pending

**Index.** For each `c ∈ Cp`, `Index_c : Map<Key, Set<UnitId>>`, with `Index_c[K] = {g | key_c[g] = K}` (I8).
- It is the inverse relation of `key_c` and covers only published pages. `F_c` contains both published pages (still findable through `Index_c`) and unpublished ones; `key_c[g]` tells them apart.
- One key may map to several pages of the class. At each hit position, `attach` prefers a candidate with `ref > 0`; otherwise it reactivates a candidate with `ref = 0`.
- Entries are removed when `key_c` is revoked (C1/C2 fresh allocation, slab reclaim, I7). `release` does not remove entries (C5).
- The total number of entries is ≤ `|U_c|`, and a key whose candidate set becomes empty keeps no stored entry (I11).

**Host index.** For each `c ∈ Cp`, `Index^H_c : Map<Key, Set<HostUnitId>>`, with `Index^H_c[K] = {g | key^H_c[g] = K}` (I20). A store publishes a key only in a host class where it has no candidate and no other store is writing it, so every stored set has exactly one element (D29), and an implementation may store a single unit id per key. Entries are removed when `key^H_c` is revoked: by a fresh host allocation in begin_store, or by a host slab reclaim. Nothing else removes them; in particular a load leaves its sources published.

**Pending.** `Pending : Map<TicketId, PendingRec>`. `dom(Pending)` corresponds both ways to the queues `Q_h` (I9):

```
PendingRec = {
  lease   : Handle,          // h
  kind    : Compute | Load(src : for each c ∈ Cp, Seq<HostUnitId>),  // a load names the host unit it copies for each block of [k_d, k*) (D31)
  propose : Bool,            // proposal rows in the drafter classes (D20); only if the input ends at the end of the planned input
  orphaned: Bool,            // set when an older ticket of the lease completed with stop (D25)
  lo      : Nat,             // start bound: p_h when the ticket was issued
  s       : Nat,             // slack: s_h when the ticket was issued; 0 for a ticket with known inputs
  ℓ       : Nat,             // input length, ℓ >= 1; 1 for a continuation
  k       : Nat,             // draft count, k <= λ
  drafts  : Known(Seq<Token>) | Deferred,  // D with |D| = k, or drafts the producer proposes on the device (D24)
  producer: Option<Ticket>,  // the ticket whose bonus token is this ticket's input; Some exactly for a continuation
  plan    : ExecutionPlan,   // the immutable plan returned by begin_write, or by attach for a load ticket (a load plan)
}
```

The ghost `base_t` is `lo` when t is issued and grows by n whenever an older ticket of the same lease completes without `stop` with acceptance count n. For a ticket that is not an orphan, the true start is `a = base_t + Σ n_{t'}` over the older pending tickets t', so it is exact, `a = base_t`, once t is the oldest; then `z = a + ℓ`, and `z_lo = base_t + ℓ` is the input end counted with every pending draft rejected. An orphan's start is known only to lie in `[c_h, lo + s]`: the completion with `stop` may have reported fewer accepted drafts than the device used (E13), so `base` no longer tracks it.

Let the plan's span be `W = lo + s + ℓ + k`, and `W_c = W + λ` for a drafter class `c ∈ Cx` in a plan with `propose`, `W_c = W` otherwise. A **plan** contains at least `ticket`, `h`, `B`, `lo`, `slack = s`, `num_inputs = ℓ`, `num_drafts = k`, `propose`, `producer`, `input_ids`, and, for each `c ∈ Cp`, `write_slots_c = [slot_c(h,j) | j in [lo, W_c)]` and the page mapping of class c for `[0, W_c)`; for each `c ∈ Cs`, the live slot `σ_h^c` and `init = (lo = 0)`.
- For a ticket with known inputs, `s = 0`, `input_ids = T_h[lo : lo + ℓ] ++ D` and `positions = [lo .. W - 1]`, as in v0.4.1.
- For a continuation, `input_ids` is `ℓ + k` placeholders 0 and `positions = [lo .. lo + ℓ + k - 1]` are those of the lowest outcome. The executor shifts them by `σ = a - lo`, which it takes from the producer's device outputs (D24, E13): the window is the `ℓ + k` entries of `write_slots_c` starting at index σ (plus `λ` more in drafter classes with `propose`), its inputs are the producer's bonus token followed by the first k drafts of the producer's proposal, and its positions are `[a .. a + ℓ + k - 1]`. The executor selects slots from the plan; computing `slot_c(h, a + i)` on the device from the plan's page mapping for `[0, W_c)` and B is the same selection (E5).
- `producer` names the ticket that samples the input token. It replaces v0.5's `deferred` list, which a continuation no longer needs: its only deferred input is at offset 0 of its window.

A **load plan** (D31) contains `ticket`, `h`, `B`, the blocks `[k_d, k*)`, and, for each `c ∈ Cp`, `u_c` and the pairs `(src_c[i], M_h^c[i])` for `i ∈ [k_d, k*)`: the host unit of class c that holds `K(h,i)`, and the page of class c it is copied into. It has no `input_ids`, no forward and no state slots. The executor copies host-arena bytes `[src·u_c, (src+1)·u_c)` to device-arena bytes `[g·u_c, (g+1)·u_c)` for every pair (E14).

**Stores.** `Stores : Map<StoreId, StoreRec>` (D30):

```
StoreRec = {
  pairs : for each c ∈ Cp, Seq<(i : Nat, key : Digest, src : UnitId, dst : HostUnitId)>,
          // the blocks of J_c in increasing order (C9): key = K(h,i), src = M_h^c[i] at issue, dst a fresh host unit
  plan  : StorePlan,  // the immutable plan returned by begin_store: for each c ∈ Cp, u_c and the pairs (src, dst)
}
```

A store keeps no handle. From issue on it depends only on the units it references, so its lease may grow, stop or be released while it is pending. Its pairs are fixed at issue, stores complete in any order, and `finish_store` consumes a record exactly once. The executor copies device-arena bytes `[src·u_c, (src+1)·u_c)` to host-arena bytes `[dst·u_c, (dst+1)·u_c)` for every pair (E14).

**Ticket queue.** `Q_h` lists the pending tickets of lease h in issue order. `δ + 1` is the largest queue length. With `δ = 0`, `Q_h` is empty or holds one ticket, exactly the optional pending ticket of v0.3 and v0.4.1. v0.4 already stated these rules for a queue of at most one ticket (written `Q = 1` there); v0.5 raised the bound to `δ + 1`, and v0.6 lets a continuation follow a verify ticket or a ticket with `propose`. A load ticket is issued only by attach, as the first ticket of its lease, so it is the oldest ticket in `Q_h` until it completes, and a ticket behind it has known inputs (D21, D31).

Calls are single-threaded (E3). While a ticket is live, the lease may only grow: `T_h` may only be appended to, every `M_h^c` may only gain entries at its end, `ρ_h` may not decrease, and every `σ_h^c` is unchanged. `release` is forbidden while `Q_h` is non-empty. With `δ >= 1`, `extend` and `extend_deferred` may run while pipelined tickets are pending (C2, C2b), and `finish_write` of one ticket may run while later ones are pending. Each of them only appends to `T_h`, `X_h`, `M_h^c` and `ρ_h`, except that `finish_write` moves the head of `X_h` into `T_h`. With `δ = 0`, nothing about the lease changes until the ticket completes, as in v0.4.1. A plan's known inputs and page mapping stay valid because they lie in the prefix that cannot change, so no version number is needed. A continuation's input and drafts are not in that prefix when the plan is issued. They are bound once, when its producer and then the continuation itself complete, and from then on `T_h` holds the reported tokens at those positions; by E13(2) they are the tokens the executor fed the continuation. Derived invariant, where `T_h^t`, `M_h^{c,t}` and `ρ_h^t` are the values when t was issued:

```
t ∈ Q_h  ⇔  t ∈ dom(Pending) ∧ Pending[t].lease = h
t ∈ dom(Pending)  ⇒  T_h^t ⊑ T_h  ∧  M_h^{c,t} ⊑ M_h^c  ∧  ρ_h^t <= ρ_h  ∧  σ_h^c unchanged since t was issued
t is the oldest ticket in Q_h, not an orphan  ⇒  base_t = c_h
t is a later ticket in Q_h, not an orphan  ⇒  base_t = base_{t'} + ℓ_{t'} for the ticket t' issued just before it
                               (never true when δ = 0)
t ∈ dom(Pending), not an orphan  ⇒  lo_t <= base_t  ∧  base_t - lo_t + Σ k_{t'} <= s_t   (t' over the older tickets of t's lease)
t is an orphan  ⇒  the window it writes starts in [c_h, lo_t + s_t]   (E13)
X_h[i] ∈ Q_h  ∧  ¬Pending[X_h[i]].orphaned  ∧  z_lo(X_h[i]) = L_h + i
Pending[t].producer = Some(t')  ⇒  (t' ∈ Q_h ∧ t' is issued just before t ∧ t' = X_h[|X_h| - 1])
                                     ∨  (t' completed, t is the oldest in Q_h, and either t is orphaned
                                         or T_h[base_t] is the token t' reported)
```

`⊑` is "is a prefix of". With `δ = 0` every pending ticket is the oldest in its queue, `X_h` is empty, `s = 0` and `lo = base = a`, the prefix relations are equalities, and these lines say exactly what v0.3 says: `a` equals the frontier, and `T_h`, `ρ_h`, `c_h`, `M_h^c` and `σ_h^c` are unchanged. With `λ = 0` every slack is 0, every continuation is v0.5's deferred decode step, and these lines say what v0.5 says.

`finish_write` accepts only a `t ∈ dom(Pending)` that is the oldest ticket in its lease's `Q_h`, with a matching binding. Atomically, it removes the entry and removes t from `Q_h`. For an orphan nothing else changes. Otherwise, with acceptance count n (`n <= k`, and `n = 0` when `k = 0`) and D the plan's drafts or, for a continuation, the drafts its completion reports:
- it appends `D[0:n]` to `T_h`, then the reported bonus token when t heads `X_h`, and removes t from `X_h`;
- it sets `c_h = z + n`, and, without `stop`, adds n to `base` of every later ticket of the lease;
- it updates the ghosts `V_c` and `W_c`, publishes the newly completed blocks in every paged class, and updates their `Index_c`;
- for a load ticket, it also drops the ticket's reference on each of its host sources;
- with `stop`, it marks every later ticket of the lease orphaned, empties `X_h`, sets `stopped_h`, and sets `W_c` of the lease's state slots to `⊥` (D25, C4).

A completion event is consumed only once.

### 3.5 Slab plan and the capacity predicate

`attach`, `extend` and `extend_deferred` are the only operations that change device slab ownership, and `begin_store` the only one that changes host slab ownership (below). Each of the first three computes a **demand** `d_c >= 0` per class (the number of units of class c it will take from `F_c`, counting reactivated cache hits) and a set of **protected slabs** `Prot` that it must not reclaim. Then, from the pre-call state:

\[
\begin{aligned}
need_c &= \lceil \max(0,\ d_c - |F_c|) / n_c \rceil\\
R_c &= \{ s \mid owner[s]=c \land s \notin Prot \land \forall g \in units_c(s):\ ref_c[g] = 0 \}\\
give_c &= \begin{cases} \min(|R_c|,\ \lfloor (|F_c| - d_c)/n_c \rfloor) & \text{if } |F_c| \ge d_c\\ 0 & \text{otherwise}\end{cases}\\
Cap(d, Prot) &\iff \textstyle\sum_c need_c \le |FS| + \sum_c give_c.
\end{aligned}
\]

`R_c` is the set of reclaimable slabs of class c. Keyed pages do not block reclaim (D11); referenced units do. A pending ticket's units are referenced by its lease (I2, I9), and a pending store's source pages by the store (D30), so units in flight are never reclaimed. `give_c` is how many whole slabs class c can give up while keeping `d_c` free units outside them.

**Slab plan.** On success the operation performs exactly this, before allocating units:

1. Each class c receives exactly `need_c` slabs; no other class receives one.
2. Slabs come from `FS` first. Only if `|FS| < Σ need_c`, exactly `Σ need_c - |FS|` slabs are reclaimed, each from some `R_{c'}` with class `c'` giving up at most `give_{c'}` slabs. Which donors and slabs are chosen is not fixed (D9).
3. Reclaiming slab s from class `c'` revokes `key_{c'}[g]` for every `g ∈ units_{c'}(s)`, removes those units from `Index_{c'}` and `F_{c'}`, and sets `W_{c'}[g] = ⊥` and `V_{c'}` of their token slots to unconstrained. Then `owner[s]` changes to the receiving class. The units of a received slab enter `F_c` with `ref_c = 0`, `key_c = None` (paged) and `W_c = ⊥` (state).
4. Units are then allocated from `F_c` as the operation specifies. A class never takes units from a slab given up in the same call.

A class with a deficit (`|F_c| < d_c`) never gives up a slab: giving up `n_c` free units would raise `need_c` by exactly one, a net loss. So `Cap` is exactly "a slab plan following rules 1–4 exists" (§9.1 obligation 11).

**Lemma (refines v0.2.1 capacity).** With one class c and `Prot = ∅`, `Cap(d, ∅) ⇔ d <= |F_c| + n_c·|FS|`. That equals v0.2.1's `|F| >= d` when units in free slabs are counted as unkeyed free pages.

**Draft reservation (D18).** `Cap`, `need_c`, `R_c` and `give_c` are unchanged; they range over every class, including `Cx`. Only the demands change: attach, extend and extend_deferred size every paged class's page table for the new reach `ρ' = L̂' + μ`, where `L̂'` is the planned input length after the call, so a paged class's demand counts `ceil(ρ'/B)` blocks instead of `ceil(L̂'/B)` (C1, C2, C2b). No other method changes device slab ownership or takes units from any `F_c`. In particular `begin_write` and `finish_write` never allocate, whatever the acceptance count and whether or not a ticket is a continuation or a load. With `λ = 0` every demand equals its v0.5 value, and with `λ = 0` and `δ = 0` its v0.3 value.

**Host slab plan (D28, D29).** Host classes use the same predicate over the host arena. `begin_store` computes a host demand `d^H_c` for every `c ∈ Cp` and a set `Prot^H` of protected host slabs (C9). `need^H_c`, `R^H_c`, `give^H_c` and `Cap^H(d^H, Prot^H)` are the formulas above with `F^H_c`, `ref^H_c`, `n^H_c`, `owner^H`, `FS^H` and `Prot^H` in place of their device counterparts, and rules 1–4 apply to the host arena: free host slabs first, reclaim only from surplus host classes and never from `Prot^H`, and reclaiming host slab s from class c revokes `key^H_c` of every unit of `units^H_c(s)` and sets their `V^H_c` to unconstrained. A host slab with a unit that a pending load reads or a pending store writes is not in any `R^H_c`. Only `begin_store` takes host units from an `F^H_c`. attach takes none and changes no host owner, but its load ticket's references take its sources out of `F^H_c` until the load completes. `finish_write` of a load ticket and `finish_store` return host units to `F^H_c`. A host demand never affects the device arena, and a device demand never affects the host arena.

## 4. Global invariant Valid(S)

The following properties hold after construction and on return from every public method. Each invariant stated for pages, `ref`, `key`, `F`, `Index`, `V` holds separately in every paged class `c ∈ Cp`, target and drafter, with `PageId` replaced by `U_c`. I1–I18 are about the device arena; I19–I22 state the host tier's counterparts and the rules for stores and load tickets.

**I1 Unit domain and page tables.** All unit ids of class c are in `U_c`. Each active lease's page table in every paged class has no duplicates; `L_h >= 1`, `Fits(m_h)` with `m_h = ceil(ρ_h/B)`, and `|M_h^c| = m_h` for every `c ∈ Cp`.

**I2 Exact references.** For every class c and unit g:

\[
ref_c[g]=|\{h\in dom(Req): g\in set(M^c_h)\}| + |\{st\in dom(Stores): g \text{ is a source of } st \text{ in class } c\}| \quad (c \in Cp), \qquad ref_c[g]=|\{h\in dom(Req): \sigma^c_h = g\}| \quad (c \in Cs).
\]

Negative counts, missing references and extra references are all forbidden. The count is the number of lease references plus the number of store references (D30); at most one pending store reads a page (I21). A pending ticket protects its units because its lease cannot be released, not by inflating this count. A pending store needs references of its own, because its lease may be released before the store completes.

**I3 Exact free set.** `g ∈ F_c ⇔ g ∈ U_c ∧ ref_c[g] = 0`. A referenced unit is never reallocated as a writable unit. Free only means reclaimable; it must not be read as "the data is gone" or "zeroed".

**I4 Valid frontier.** `0 <= c_h <= L_h`. For every `c ∈ Cp` and `j < c_h`, `V_c[slot_c(h,j)]` corresponds to `Namespace, T_h[0:j+1]`. No claim is made about slots at positions `>= c_h`, in particular tentative positions, proposal rows and rejected drafts. This is a KV provenance property; floating-point numerical correctness is the executor's external spec.

**I5 Published cache is genuine.** When `key_c[g] != None`, there exist `q >= 1` and a prefix `τ` of length `qB` such that `den(key_c[g]) = (ns, τ)` and page g of class c holds valid KV for the last complete block of `τ`. A key identifies one definite logical block position and context.

For any active lease h that references a published page g of class c, if `M_h^c[i]=g` then also `key_c[g]=K(h,i)` and `c_h >= (i+1)B`. This applies to pages with ref=1 too, so a request never writes over one of its own published pages as if it were an uncomputed tail.

**I5b Complete implies published.** For every active lease h, `c ∈ Cp` and `i < m_h`, if `(i+1)B <= c_h` then `key_c[M_h^c[i]] = K(h,i)`. I5 only gives "published ⇒ correct"; I5b gives the converse. This makes D8's "lookup is complete" a property of the state, rather than a conclusion that needs replaying history.

**I6 Shared means read-only.** If `ref_c[g]>1`, or a pending store reads g, then `c ∈ Cp` and g has a published key. For every referencing lease h, that key equals `K(h,i)` for g's position i in h, and `c_h >= (i+1)B`. So no referencing lease ever writes to g as if it were an uncomputed tail, and no page that a store is copying is written (I7).

**I7 No overwrite after publication.** A page with a non-empty key must not be overwritten in place by any write plan or load plan. A new round of writes may start only once `ref_c[g]=0` and the key and index entry have been revoked, either because the page was chosen as a new page or because its slab was reclaimed and given out again.

**I8 Index consistent both ways.** `Index_c[K] = {g | key_c[g]=K}`. Invalidated pages are not found; published candidates whose page was not reused and whose slab was not reclaimed are found. Under E8, equal digests are treated as equal prefixes, so candidates in `Index_c[K]` need no token-by-token comparison. A key whose candidate set is empty has no stored entry in the concrete representation (I11).

**I9 In-flight protection.** Each active lease has a queue `Q_h` of at most `δ + 1` pending tickets, and the queues and the Pending table correspond both ways. A load ticket counts as a ticket; I22 adds its own rules.
- A ticket is bound to a real lease, its start bound `lo`, slack `s`, input length `ℓ >= 1`, draft count `k <= λ` and its drafts (known, or a count for a continuation), with `lo + s + ℓ + k <= ρ_h`, plus `λ` in drafter classes when it has `propose`. `k > 0` only if its input ends at the end of the planned input when it is issued: host-known drafts with `Q_h` empty and `z = L_h`, or a continuation whose producer has `propose`. A ticket with `propose` has `Cx ≠ ∅` and its input ends at the end of the planned input.
- A ticket that is not an orphan starts where the lease's earlier tickets end: the oldest one in `Q_h` starts at `c_h`, and a later one at the previous ticket's input end plus that ticket's accepted drafts; its start lies in `[lo, lo + s]` (derived invariant, §3.4). An orphan starts in `[c_h, lo + s]` (E13).
- Queue shape (D21): for any two consecutive tickets `t'`, `t` in `Q_h`, either t is a continuation of `t'`, or `t'` has `k = 0` and no `propose` and t has known inputs and no drafts.
- The units it needs, in every class, stay referenced until completion.
- Every listed write slot of a pending plan lies within the valid slot range of each class and inside the lease's page tables, and every listed slot at a position `>= c_h` is on an exclusive, unpublished page. The true start of every pending ticket that is not orphaned is at least `c_h`, and so is the window an orphan writes (E13). So no window touches a published or shared page, although a continuation may list slots below `c_h` once its producer has completed. Its state slots are the lease's own live slots.
- Tickets of different leases have disjoint write slots in every class and different state slots. Tickets of one lease write windows that start, in issue order, where the previous ticket's input and accepted drafts end. A later window may overlap the earlier ticket's rejected rows and proposal rows, which are never credited. The executor applies the tickets of a lease in issue order (E13; with `δ = 0` there is never more than one).
- While a ticket is live, the lease only grows (`T_h`, every `M_h^c` and `ρ_h` only extend, every `σ_h^c` is unchanged). With `δ = 0`, nothing about the lease changes until the ticket completes.

**I10 Immutable configuration.** N, S, the class table (`Cp`, `Cx`, `Cs`, every `u_c`), B, `λ`, `δ`, `N_H`, `S_H` and Namespace do not change during the coordinator's lifetime; all addresses in execution, load and store plans are computed with this instance's values.

**I11 Bounded metadata.** The element count of every metadata container is bounded by the fixed configuration, independent of how many operations have been performed:

- `|dom(Req)| <= N · min_c n_c`;
- `|dom(Pending)| <= (δ + 1) · |dom(Req)|` (at most `δ + 1` tickets per lease, I9, orphans included), and `|X_h| <= δ` for every lease (I17);
- per paged class, the number of stored `Index_c` entries, however the representation groups keys, is at most `|{g | key_c[g] != None}| <= |U_c| <= N·n_c`; an entry exists only for a non-empty candidate set;
- for every lease and `c ∈ Cp`, `|M_h^c| <= N·n_c`, and `Fits(m_h)` bounds `ρ_h`, hence `L_h <= L̂_h <= ρ_h`;
- the drafts stored in a pending ticket number at most `λ`, and a continuation stores none; a completion carries at most `λ` drafts;
- per-unit state (`ref_c`, `key_c`, membership in `F_c`) has exactly `N·n_c` slots per class, and `owner` has exactly N;
- `|dom(Stores)| <= Σ_{c ∈ Cp} N_H·n^H_c`: every pending store references at least one host unit, and no two reference the same one (I19). A store holds at most `N·n_c` pairs in class c, one per block of one lease (I21). A load ticket holds `k* - k_d <= N·n_c` sources per class;
- per host class, the number of stored `Index^H_c` entries is at most `|U^H_c| <= N_H·n^H_c`; per-unit host state (`ref^H_c`, `key^H_c`, membership in `F^H_c`) has exactly `N_H·n^H_c` slots per class, and `owner^H` has exactly `N_H`;
- reference counts stay small: `ref_c[g] <= |dom(Req)| + 1` in a paged class (at most one pending store reads a page), and `ref^H_c[g] <= |dom(Req)| + 1` (a lease has at most one load ticket, and at most one pending store writes a host unit).

**I11a Distinct last pages and slots** (supporting fact). For distinct active leases `h != h'` and every `c ∈ Cp`, `M_h^c[m_h-1] != M_{h'}^c[m_{h'}-1]`. A lease's last page is always a fresh page taken from `F_c`: attach takes it fresh because `k* <= ceil(L_h/B)-1 <= m_h-1`, and extend and extend_deferred either add fresh pages or keep the old last page. Page-table entries never change afterwards. For every `c ∈ Cs`, `σ_h^c != σ_{h'}^c` by I2 and I14. So `|dom(Req)| <= |U_c| <= N·n_c` for every class.

I11 bounds element counts. Total token storage is therefore at most `|dom(Req)| · max{L | Fits(ceil(L/B))}` tokens plus `λ` drafts per pending ticket, because each lease keeps its full input. Whether byte-level memory is bounded additionally depends on the runtime's containers using memory proportional to their peak element count, which is outside the proof.

**I12 Slab ownership.** `owner : SlabId -> Classes ∪ {Free}` is total, and `FS = {s | owner[s] = Free}`. Every slab has exactly one owner or is free. Likewise `owner^H : SlabId^H -> Cp ∪ {Free}` is total, and `FS^H = {s | owner^H[s] = Free}`: every host slab is free or owned by one host class.

**I13 Confinement.** For every class c and unit `g ∉ U_c`: `ref_c[g] = 0`, `g ∉ F_c`, and (paged) `key_c[g] = None` and g is in no `Index_c` entry, or (state) `W_c[g] = ⊥`. Every page-table entry, live slot, key, Index candidate and pending write of class c lies in `U_c`, and so does every source page of a pending store in class c. In the host tier, for every `c ∈ Cp` and host unit `g ∉ U^H_c`: `ref^H_c[g] = 0`, `g ∉ F^H_c`, `key^H_c[g] = None`, and g is in no `Index^H_c` entry. Every load source, store destination, key and `Index^H_c` candidate of host class c lies in `U^H_c`.

**I14 Live state slots.** For every `c ∈ Cs` and active lease h, `σ_h^c ∈ U_c` and `ref_c[σ_h^c] = 1`. Distinct leases have distinct slots. A state class has no keys and no Index.

**I15 State provenance.** For every `c ∈ Cs` and active lease h that is not stopped: if `c_h > 0` then `W_c[σ_h^c] = (Namespace, T_h[0:c_h])`. If `c_h = 0`, no claim is made about the slot's contents; the next plan carries `init` (C3, E10). With `λ > 0` this still names one slot per lease: after a verify ticket the slot holds the state after the accepted prefix, never after a rejected draft (D19, E11). A stopped lease has `W_c[σ_h^c] = ⊥`: the next ticket in issue order is an orphan, which reads the state after the tokens the device accepted rather than after `T_h[0:c_h]`, and no ticket reads the slot after the orphans (D25). Per-token records and other scratch bytes that the executor keeps inside the unit carry no provenance.

**I16 Draft reservation.** For every active lease h that is not stopped:
- `L̂_h <= ρ_h <= L̂_h + μ`;
- every pending ticket's span fits: `lo + s + ℓ + k <= ρ_h`, plus `λ` in drafter classes with `propose` (I9);
- room to issue: if `p_h < L̂_h`, then `L̂_h + s_h + λ + λ·[Cx ≠ ∅] <= ρ_h`.

attach, extend and extend_deferred set `ρ_h = L̂_h + μ`, and the third clause then holds because `s_h <= δ·λ` (C2 needs `s_h = 0`; C2b needs `|Q_h| <= δ`). A completion without stop adds its acceptance count n to both `L̂_h` and `p_h` and removes its k from `s_h`, with `n <= k`, so the third clause is preserved. So a ticket with `k <= λ` drafts always fits its reservation, and so do its proposal rows and those of a continuation behind a verify, for every acceptance count. Between two calls that set the reach, `L̂_h` grows by at most `δ·λ`, so the demand of extend_deferred is at most `ceil((1 + δ·λ)/B)` pages per paged class: one page when `1 + λ <= B`. Every page that covers a position `j >= c_h` is exclusive (`ref_c = 1`) and unpublished in every `c ∈ Cp`. With `λ = 0`, `μ = 0`, every slack is 0, and I16 is v0.5's I16. A stopped lease keeps its reach; only the second clause is still needed, for its orphans.

Exclusivity of the reserved pages follows from I5 and I6: a published or shared page at block i of h has `(i+1)B <= c_h`, so it covers no position `>= c_h`. I16 states it so that no ticket needs to check it. Accepted drafts consume the reservation: after a verify accepts n drafts, `ρ_h - L̂_h` drops by n, and the next attach, extend or extend_deferred restores it to `μ`.

**I17 Deferred tail.** For every active lease h: `|X_h| <= δ`; for every `i < |X_h|`, `X_h[i]` is a pending, non-orphaned ticket of h, every older ticket in `Q_h` has `k = 0`, and its input end is exactly `L_h + i`; a continuation is younger than its producer; and, if the lease is not stopped, the oldest ticket in `Q_h`, if any, has `z <= L_h`. The last part follows from the others and the contiguity in I9. It is what `finish_write` needs: the ticket it accepts read only known tokens, so the KV it credits is KV of `T_h`. With I4 it gives `c_h <= L_h <= L̂_h`. With `δ = 0`, `X_h` is empty and I17 is trivial.

**I18 Orphans and stopped leases** (D25). For every active lease h: if a ticket in `Q_h` is orphaned, then `stopped_h` holds and every younger ticket in `Q_h` is orphaned too. If `stopped_h`, then every ticket in `Q_h` is orphaned, `X_h` is empty, and `T_h`, `c_h`, `ρ_h`, every `M_h^c` and every `V_c` claim below `c_h` stay unchanged until release. An orphan's window lies at or past `c_h` (E13), so I4, I5, I5b and I6 are unaffected by it.

**I19 Host references and free set** (D29). For every `c ∈ Cp` and host unit g:

\[
ref^H_c[g]=|\{t\in dom(Pending): t \text{ is a load ticket with source } g \text{ in class } c\}| + |\{st\in dom(Stores): g \text{ is a destination of } st \text{ in class } c\}|,
\]

and `g ∈ F^H_c ⇔ g ∈ U^H_c ∧ ref^H_c[g] = 0`. A store's destination has `ref^H_c[g] = 1` and no key, so no load reads it and no other store writes it. A load ticket's source has a key. A referenced host unit is never taken as a fresh unit, and its host slab is in no `R^H_c`. Free only means reclaimable, as in I3.

**I20 Host cache genuine and indexed.** For every `c ∈ Cp` and host unit g with `key^H_c[g] = Some(K)`: `den(K) = (ns, τ)` with `|τ| = qB` for some `q >= 1`, and for every `b < B`, `V^H_c[g·B + b] = (ns, τ[0 : (q-1)B + b + 1])`: host unit g holds class c's KV for the last block of τ. `Index^H_c[K] = {g | key^H_c[g] = K}` has at most one element, and a key with no candidate has no stored entry. A host unit with a key is never written (I7 for the host tier): host units are written only as destinations of pending stores, which have no key, and a key is revoked, by a fresh allocation in begin_store or a host slab reclaim, before its unit can become a destination again.

**I21 Stores** (D30). For every pending store st and `c ∈ Cp`, the pairs `(i, K, g, g^H)` of st in class c have distinct blocks i, and each satisfies:
- `K = K(h,i)` over `T_h` of the lease h that issued st, at issue, so `den(K) = (ns, τ)` with `|τ| = (i+1)B`;
- g is a page of class c with `key_c[g] = K`, so it holds class c's KV for τ's last block (I5), and `ref_c[g]` counts st (I2);
- `g^H ∈ U^H_c` has no key, and st is its only reference (I19).

For every key K and `c ∈ Cp`, at most one pending store writes K in class c, and none does while `Index^H_c[K]` is non-empty. So at most one pending store reads a page, and a store that completes with `stored` publishes keys that have no other candidate in their host class.

**I22 Load tickets** (D31). For every pending load ticket t of lease h: t is the oldest ticket in `Q_h`, h is not stopped, and t's interval is `[k_d·B, k*·B)` with `c_h = k_d·B` and `k_d < k*`, `k*·B < L_h`. For every `c ∈ Cp` and `i ∈ [k_d, k*)`, t's source in class c is a host unit with key `K(h,i)` whose `ref^H_c` counts t, and its destination `M_h^c[i]` lies above `c_h`, so it is exclusive and unpublished (I16). No other plan writes `M_h^c[i]`, and the lease's later tickets, which start at `k*·B`, read it only after t's copies have finished (E13(1)).

**Arena disjointness** (theorem, from A1 and I12). For any two distinct pairs `(c,g) ≠ (c',g')` with `g ∈ U_c` and `g' ∈ U_{c'}`, the byte ranges `[g·u_c, (g+1)·u_c)` and `[g'·u_{c'}, (g'+1)·u_{c'})` are disjoint. Within one class, distinct ids are disjoint. Across classes, the units lie in different slabs (I12) and each unit lies inside its own slab (A1). Together with I6, I9, I14 and I16, this gives: no planned write, including a write at a tentative position, touches a published page, a shared page, another lease's state slot, another lease's reservation, or another class's unit. In particular drafter-class writes, including proposal rows, never alias target-class KV.

**Copy isolation** (theorem, from I2, I5, I6, I7, I9, I16 and I19–I22). In either arena, no unit is written by one pending plan or copy while another pending plan or copy reads or writes it, except between the tickets of one lease, a load ticket included: the executor applies those in issue order (E13(1), E14(3)), so a later ticket reads what an earlier one writes only after it is written, and overlaps an earlier ticket's writes only at the rejected rows and proposal rows I9 allows. A load writes exclusive unpublished pages of its own lease, which no store reads and no plan of another lease touches, and reads published host units, which no store writes and which are neither taken nor reclaimed while it is pending. A store reads published pages, which no plan writes and which are neither reallocated nor reclaimed while it is pending, even after its lease is released, and writes host units that only it references. A compute ticket, an orphan included, writes only pages at or past `c_h`, which are exclusive and unpublished (I5, I6), so no store reads them and no load of another lease writes them. Units of distinct host classes lie in distinct host slabs, and each host unit lies inside its own host slab (A1^H, I12), so distinct pairs `(c, g)` of host units occupy disjoint host-arena bytes, as in the device arena.

## 5. General method conventions

A real implementation must encapsulate its internal state: external code may update it only through the verified methods. `Valid(S)` must not be treated as a condition that an arbitrary external Python caller will always respect voluntarily.

Every method must satisfy:

1. If the entry state is Valid, the state on normal return is also Valid.
2. The method terminates on every finite valid input, with no out-of-bounds access, counter overflow, or unspecified state change.
3. Declared error results are strongly failure-atomic: `S'=S`, including slab ownership in both arenas, every class's page tables, slots, reference counts and index, every host class's references, keys and index, frontiers, pending tickets, pending stores, and id-allocation state.
4. The inputs, page tables, state slots, frontiers and pending tickets of uninvolved leases stay unchanged; existing KV referenced by multiple leases and the live state of other leases must not change. The only changes to device units not referenced by the calling lease are the slab-plan steps of §3.5 and the release of a store's source pages by `finish_store`. In the host tier, the only changes are begin_store's slab plan and fresh units, the references a load ticket adds and drops, and what `finish_store` does to its own destinations.
5. Externally observable outputs satisfy each method's functional postcondition, not merely "the state is still valid".

These failure-atomicity requirements cover the specified input, capacity and phase errors. Process termination, runtime OOM and hardware faults are outside this version's state-machine promises.

This contract assumes methods are called sequentially on one thread (or serialized by the caller), and claims no multi-threaded linearizability (E3). Computing a chained key is a pure function and modifies no state. `owner`, `owner^H`, every `Index_c` and every `Index^H_c` change only on successful methods. So the strong failure atomicity of item 3 covers slab ownership, page tables, slots, references, every index and id-allocation state in both arenas, with no separate key-store state to cover.

## 6. API contracts

### C0. create(N, S, classes, B, λ, δ, Namespace, N_H, S_H) -> Result<Coordinator>

`classes` is an ordered list of `(kind ∈ {Paged, DrafterPaged, State}, u_c)`. `Paged` and `DrafterPaged` classes form `Cp`, `DrafterPaged` classes form `Cx`, `State` classes form `Cs`. Every class in `Cp` gets a host class (D28). `create` without host arguments is `create(..., 0, S)`: no host tier.

**Success:** the configuration is fixed; every slab of both arenas is free; Req, Pending, Stores, every `Index_c` and every `Index^H_c` are empty; every unit of every class has ref=0, key=None and `W = ⊥`, and every host unit has `ref^H = 0` and no key; every `U_c`, `F_c`, `U^H_c` and `F^H_c` is empty; Valid holds.

**Failure:** return an explicit ConfigError and produce no usable coordinator if `N`, `S` or `B` is non-positive; there is no paged class that is not a drafter class; some `u_c` is non-positive; **some `u_c` does not divide `S` (A1)**; `Cx ≠ ∅` and `λ = 0`; `δ >= 2` (D21); `¬Fits(ceil((1+μ)/B))`, so that not even a one-token lease could attach; `S_H` is non-positive or **some `u_c` with `c ∈ Cp` does not divide `S_H` (A1^H)**, also when `N_H = 0`; or the configuration cannot be safely represented in machine integers (including `N·S`, `N·n_c·B`, `L + μ` for every `L` with `Fits(ceil(L/B))`, `N_H·S_H` and `N_H·n^H_c`). `δ` needs no further representation check: it is at most 1, and ticket ids are already guarded by IdentifierExhausted.

With `δ = 0`, `λ = 0` and `Cx = ∅`, C0–C7 below reduce to their v0.3 text (obligation 18); C8 is new in v0.7, and C9 and C10 in v0.8. With `δ = 0`, C0–C7 reduce to their v0.4.1 text and C2b never succeeds (obligation 20). With `λ = 0`, they reduce to their v0.5 text (obligation 24). Each reduction holds for completions without `stop`, which is new in v0.6, for attach without a limit (`κ = L`), and for extend in the phases where v0.6 also accepted it (`p_h = L_h`), both new in v0.7 (obligation 28), and without a host tier (`N_H = 0`), new in v0.8. With `N_H = 0`, C0–C10 reduce to v0.7's C0–C8 (obligation 31): attach never issues a load ticket, probe reports no loaded tokens, begin_store returns RequestTooLarge on every valid range, and finish_store has no store to complete.

### C1. attach(T, κ) -> Result<(Handle, cached_tokens, LeaseView, Option<(Ticket, LoadPlan)>)>

Purpose: handle a request for the first time, or re-acquire resources from the retained full input after a request was preempted and released.

`κ` is the hit limit (D26): the caller resumes the request at most `κ` positions in, `κ = 0` attaches cold. It bounds device and host hits alike (D31). `attach(T)` is `attach(T, L)`; that limit caps nothing, since `floor(L/B) >= m - 1`, so with it and without a host tier this clause is v0.6's C1 (obligations 28, 31). The implementation names the general method `attach_capped`.

**Valid input:** T is a non-empty sequence of valid tokens with `Fits(ceil((L+μ)/B))`, and its Namespace is this coordinator's fixed configuration. An input that is too large, including its draft reservation, returns RequestTooLarge; an invalid or empty sequence returns InvalidArgument.

**Exact definition of prefix and capacity:** let `m=ceil(L/B)` be the input's block count, `m^+ = ceil((L+μ)/B)` the reserved block count (D18), and `k_max = min(m-1, floor(κ/B))`. Computed from the pre-call state:

\[
\begin{aligned}
k_d&=\begin{cases}0 & \text{if } Cs \ne \varnothing,\\ \max\{k\in[0,k_{max}]\mid\forall c\in Cp,\ \forall i<k,\ Index_c[K(h,i)]\ne\varnothing\} & \text{otherwise,}\end{cases}\\
k^*&=\begin{cases}0 & \text{if } Cs \ne \varnothing,\\ \max\{k\in[k_d,k_{max}]\mid\forall c\in Cp,\ \forall i\in[k_d,k),\ Index^H_c[K(h,i)]\ne\varnothing\} & \text{otherwise.}\end{cases}
\end{aligned}
\]

`k_d` is the **device run**, v0.7's `k*`, and the blocks `[k_d, k*)` are the **host run** (D31). With `N_H = 0` every `Index^H_c` is empty, so `k* = k_d`. `K(h,i)` is computed incrementally along the §3.3 chain, starting from `Seed(ns)`. The tail block has no key, so the upper bound `m-1` agrees with "the last block is recomputed". The bound `floor(κ/B)` keeps `k*·B <= κ` (D26). The first case is D13: there are no state checkpoints, so no prefix can be resumed. (A future version replaces it with "and a state checkpoint at `kB` exists".) Both runs are joint over target and drafter classes: a prefix cached for the target model but not for the drafter is not a hit, in either arena. The host run continues the device run and stops at the first block that some host class lacks, even if the device arena holds it (D31).

For `c ∈ Cp`, let `r_c` be the number of the `k_d` device-run positions that have at least one candidate in `Index_c` with `ref>0`. Demand and protected slabs:

\[
\begin{aligned}
d_c &= m^+-r_c \quad (c\in Cp), \qquad d_c = 1 \quad (c \in Cs),\\
Prot &= \{ slab_c(g) \mid c\in Cp,\ i<k_d,\ \text{no candidate of } Index_c[K(h,i)] \text{ has } ref>0,\ g\in Index_c[K(h,i)] \}.
\end{aligned}
\]

`Prot` holds the slabs of the free candidates this call may reactivate. It depends only on the pre-call state and T, so a call never reclaims a cache entry it is about to hit. With `Cs ≠ ∅`, `k* = k_d = 0` and `Prot = ∅`. The host run adds no demand: its blocks get fresh pages, as every block from `k_d` on does, and attach takes no host unit. So the demand, `Prot` and the success condition below are those of v0.7 for `k_d`, whatever the host tier holds.

**Success if and only if:** for valid input with the handle space not exhausted, and, when `k* > k_d`, the ticket space not exhausted, attach must succeed when `Cap(d, Prot)` holds and must return NoCapacity otherwise. It must not return NoCapacity because of a poor candidate, donor or slab choice when a feasible plan exists. When the handle space is exhausted, or a load ticket is needed and the ticket space is exhausted, it returns `IdentifierExhausted` (consistent with C3), and the state is unchanged.

**Postconditions on success:**

- The slab plan of §3.5 is performed for `(d, Prot)`.
- Returns a fresh valid handle h with `T_h=T`, `c_h=k_d·B`, `ρ_h = L + μ`, an empty deferred tail `X_h`, `stopped_h` false, `|M_h^c| = m^+` for every `c ∈ Cp`, and one live slot `σ_h^c` for every `c ∈ Cs`. Its ticket queue `Q_h` is empty when `k* = k_d`, and otherwise holds one fresh load ticket t for `[k_d·B, k*·B)` (§3.3), so `p_h = k*·B`.
- For `c ∈ Cp` and `i<k_d`, the page-table entry is chosen from the corresponding pre-call `Index_c`. If a referenced candidate exists it is chosen; otherwise a free cached candidate is reactivated.
- For `c ∈ Cp` and `i>=k_d`, distinct free pages of class c are allocated, including the host run's blocks `[k_d, k*)` and the reserved blocks `[m, m^+)`; these pages must not overwrite the cache-hit pages chosen in this call. A page with a key is allocated only if every unkeyed free page of class c, after the slab plan, is allocated too.
- For `c ∈ Cp` and `i ∈ [k_d, k*)`, t's source in class c is the one host unit in the pre-call `Index^H_c[K(h,i)]`, and its `ref^H_c` grows by one; t's destination is `M_h^c[i]`. Nothing else in the host tier changes: attach takes no host unit and changes no host owner, key or `Index^H_c`.
- For `c ∈ Cs`, `σ_h^c` is a fresh unit taken from `F_c`, with `ref_c = 1`; its contents are unconstrained (`W_c = ⊥`).
- Every old reference count increases by exactly one for each new page-table entry or slot that refers to it. Units taken from `F_c` are removed from it.
- The old keys of pages newly allocated as writable are revoked, and their `Index_c` entries correctly removed. Hit pages' keys and KV are unchanged.
- Other active leases' contents, valid KV and live state are unchanged. The returned LeaseView is an immutable snapshot; later extend calls do not change a view already returned.
- Returns `cached_tokens = k*·B`, the position where the lease's first compute ticket starts, and, when `k* > k_d`, the load ticket t with its load plan (§3.4).

The demand formula distinguishes reusing an active page from reusing a free cache page: the former saves one free-unit slot, the latter still consumes one. Finding a cache hit does not mean no physical capacity is needed. A host hit saves no device capacity at all: it saves the forward that would compute the block, at the cost of a copy.

attach does not implicitly preempt other requests, does not evict referenced units, does not advance GPU computation, and copies nothing: the load ticket's copies run when the executor executes its plan. Which free page or slab is evicted is not part of this contract, except that reclaim happens only when free slabs do not suffice, and that unkeyed free units are allocated before cached ones (above). A reclaim still revokes every key in the slab it takes (§3.5 rule 3), whatever unkeyed units the donor class keeps elsewhere.

### C2. extend(h, suffix) -> Result<LeaseView>

Purpose: append the tokens that need computing next to a lease, and atomically reserve their capacity.

**Calling phase:** h is valid and not stopped, and `X_h` is empty. Known input positions may be neither computed nor covered by a pending ticket: `p_h <= L_h` (D27; v0.6 required `p_h = L_h`). Pending tickets are allowed only if `|Q_h| <= δ` and every ticket in `Q_h` has `k = 0` and no `propose` (D21), so `s_h = 0`; otherwise extend returns Busy. A stopped lease returns InvalidPhase, checked first; Busy is checked next; then a non-empty `X_h` returns InvalidPhase. With `δ = 0` any pending ticket returns Busy, as in v0.4.1. suffix is non-empty with valid tokens; the existing prefix may not be modified.

After a verify, this is how the caller appends the bonus token sampled after the last accepted draft (D17). With `δ >= 1`, it is also how the caller appends a token that is already known on the host, such as a teacher-forced (golden) token, while the step that consumes the previous position is in flight.

Let the old length be L, the old block count `m = m_h = ceil(ρ_h/B)`, `L'=L+|suffix|`, and `m'=ceil((L'+μ)/B)`. Because `ρ_h <= L + μ < L' + μ`, `m' >= m`. Demand: `d_c = m'-m` for `c ∈ Cp`, `d_c = 0` for `c ∈ Cs`; `Prot = ∅`.

**Success if and only if:** in a valid phase with `Fits(m')`, extend succeeds if and only if `Cap(d, ∅)`. `¬Fits(m')` returns RequestTooLarge. Insufficient space returns NoCapacity, with the old input, page tables and slab ownership unchanged.

**Postconditions on success:**

- The slab plan of §3.5 is performed for `(d, ∅)`.
- `T'_h=T_h ++ suffix`, `c'_h=c_h` and `ρ'_h = L' + μ`; the old input prefix and the ticket queue are unchanged. Pending plans stay valid: their inputs lie in the old prefix and their page mappings in the old page tables.
- For every `c ∈ Cp`, the old page table remains a prefix of the new one; exactly `d_c` new distinct free pages are added, each with ref=1 and key=None, unkeyed free pages first as in C1. Pages already reserved at positions `[L, ρ_h)` are reused for the suffix; they are exclusive and unpublished (I16).
- State slots are unchanged.
- Existing KV, live state, published keys and other requests are unchanged; any cache identity the newly occupied pages had is correctly revoked.
- extend does not look up the prefix cache for the new suffix and does not copy shared pages. If the old tail block still has unused slots, it must be exclusive and unpublished in every paged class, and later writes may use those slots.

If the final sampled token does not need to be fed to the model again, the scheduler can record the output and release without calling extend. If extend fails, the caller must keep the external token and choose a strategy such as waiting or preemption; this module neither drops nor resamples it.

### C2b. extend_deferred(h) -> Result<LeaseView>

Purpose: under ZOS, append the position whose token the newest pending step will sample, so that the next step can be planned before that token reaches the host (D22). With speculation, the newest step may be a verify step, and the next step is then a continuation of it (D24).

**Calling phase:** h is valid and not stopped; `Q_h` is non-empty and `|Q_h| <= δ`; and the newest ticket t ends at the planned input end, `z_lo(t) = p_h = L̂_h`. t may have drafts or `propose`; its bonus position is then counted at its lowest place, `L̂_h`, and its true place is `L̂_h + σ` with `σ <= s_h`. A stopped lease returns InvalidPhase, checked first. A queue with `|Q_h| > δ` returns Busy, checked next. An empty queue or `p_h < L̂_h` returns InvalidPhase. With `δ = 0` the call never succeeds. By I17, `z_lo(t) = L̂_h` implies that t is not yet in `X_h`.

Let `L̂' = L̂_h + 1` and `m' = ceil((L̂'+μ)/B)`. Because `ρ_h <= L̂_h + μ`, `m' >= m_h`. Demand: `d_c = m' - m_h` for `c ∈ Cp`, at most `ceil((1 + δ·λ)/B)` (I16); `d_c = 0` for `c ∈ Cs`; `Prot = ∅`.

**Success if and only if:** in a valid phase with `Fits(m')`, extend_deferred succeeds if and only if `Cap(d, ∅)`. `¬Fits(m')` returns RequestTooLarge, and insufficient space returns NoCapacity. The state is unchanged on every error.

**Postconditions on success:**

- The slab plan of §3.5 is performed for `(d, ∅)`.
- `X'_h = X_h ++ [t]`, so `L̂'_h = L̂_h + 1`, and `ρ'_h = L̂' + μ`. `T_h`, `c_h`, `Q_h` and every pending plan are unchanged.
- For every `c ∈ Cp`, the old page table is a prefix of the new one, extended by `d_c` fresh exclusive unpublished pages as in C2. State slots are unchanged.
- The next `begin_write` on h may be a continuation of t (C3): its input is position `L̂_h`, and its plan names t as producer.

If extend_deferred fails, the caller does not plan the next step of this lease until t completes. finish_write then appends t's accepted drafts, and the caller appends the token t sampled with `extend`, and plans the next verify with the drafts t proposed as host-known drafts, as in v0.4.1.

### C3. begin_write(h, n, drafts, propose) -> Result<(Ticket, ExecutionPlan)>

Purpose: produce an immutable execution plan for one prefill chunk, one decode step, or one verify step, covering every class, and mark its resources as in flight.

`drafts` is `Known(D)`, a sequence of valid tokens with `|D| = k`, or `Deferred(k)`, the number of drafts a continuation takes from its producer's proposal (D24). `Known([])` is an ordinary chunk or decode step.

**Valid call:** h is valid and not stopped, `0 < n <= L̂_h - p_h`, and `k <= λ`. Moreover:
- If `Q_h` is empty: `drafts` is `Known(D)`; `k > 0` requires `c_h + n = L_h`; and `propose` requires `Cx ≠ ∅` and `c_h + n = L_h`. This is v0.4.1's rule.
- If `Q_h` is non-empty: `|Q_h| <= δ`, and `drafts` is not `Known(D)` with `k > 0` (D21).
  - When the interval reaches the deferred position, `p_h + n = L̂_h` with `X_h` non-empty, the ticket is a **continuation** of the newest pending ticket t: `n = 1`; `Deferred(k)` with `k > 0` requires that t has `propose`; and `propose` requires `Cx ≠ ∅`.
  - Otherwise the inputs `[p_h, p_h + n)` are known: every ticket in `Q_h` has `k = 0` and no `propose` (implied by `p_h < L̂_h` and I17), `drafts` is `Known([])`, and `propose` requires `Cx ≠ ∅` and `p_h + n = L_h`.

A stopped lease returns InvalidPhase, checked first. A queue that cannot take the ticket (`|Q_h| > δ`, or host-known drafts behind a pending ticket) returns Busy, checked next. No remaining input, an out-of-range n, `k > λ`, invalid draft tokens, drafts that do not follow the whole input, `Deferred` outside a continuation, deferred drafts from a producer without `propose`, or a misplaced `propose` return InvalidArgument. With `δ = 0` any pending ticket returns Busy, as in v0.4.1.

If the implementation runs out of fresh ticket ids, it returns IdentifierExhausted with the state unchanged; it must never wrap around and accept old tickets.

Let `lo = p_h`, `ℓ = n`, `s = s_h` for a continuation and `s = 0` otherwise, and `W = lo + s + ℓ + k`, plus `λ` in drafter classes with `propose`. By I16 (room to issue), `W <= L̂_h + s_h + λ + λ·[Cx ≠ ∅] <= ρ_h` whenever the call is valid. So begin_write never fails for capacity. A ticket with known inputs has `s = 0`; with an empty queue its start is `c_h` and its inputs are all known.

The coordinator does not check that `D` is what the drafter proposed. Acceptance is decided by the sampler against the target model's outputs, so a wrong `D` only lowers the acceptance count; it cannot corrupt any credited KV or state.

**Postconditions on success:**

- Returns a fresh ticket bound to h, `lo`, `s`, `ℓ`, `k`, the drafts and `propose`, with `producer = Some(t)` for a continuation of t.
- The plan is as in §3.4. For a ticket with known inputs, `input_ids = T_h[lo : lo + ℓ] ++ D` and `positions = [lo, ..., lo + ℓ + k - 1]`, exactly v0.4.1's plan. For a continuation, `input_ids` are placeholders, `positions` are those of the lowest outcome, and the executor resolves the shift σ, the input token and the drafts from the producer's device outputs (D24, E13). With `k > 0`, the sampler reads the outputs at the window's positions `[a + ℓ - 1, a + ℓ + k)`.
- For every `c ∈ Cp`: the plan lists `slot_c(h,j)` for every `j in [lo, W_c)`, distinct and within `[0, N·n_c·B)`, and the class's page mapping for `[0, W_c)`. Every listed page at a position `>= c_h` is exclusive and has no published key. The executor writes the window of `ℓ + k` slots starting at index σ (σ = 0 for known inputs). The prefix before the window start is valid when the window runs (I4, E13); the read dependencies of the window, including each draft's dependence on the drafts before it, are satisfied by the executor's causal computation semantics.
- For every `c ∈ Cx`: the forward writes drafter KV over the window from the target model's hidden states (E12). With `propose`, the window extends by `λ` slots for the proposal rows. After sampling, the executor runs the proposal forward over the bonus token and `λ-1` noise tokens, writes drafter KV at the λ positions starting at the bonus position, and passes the `λ` drafts to the next continuation on the device, or to the caller outside this module. Every listed page at a position `>= c_h` is exclusive and unpublished (I16).
- For every `c ∈ Cs`: the plan names `σ_h^c`, `init = (lo = 0)` and `num_drafts = k`. When `init` is false, once every earlier ticket in `Q_h` has been executed with its state rebuild for the acceptance count the device used, the slot holds the state after the tokens before the ticket's window; with an empty queue that is `T_h[0:a]` (I15, E11, E13). For a ticket that later becomes an orphan, those tokens may run past `T_h` (D25). The executor reads it, and must be able to leave in the same slot the state after the ticket's input and its first `acc` drafts for whichever acceptance count `acc <= k` it uses (E11). With `k = 0` this is v0.3's "the state after `T_h[0:z]`".
- The coordinator appends the ticket to `Q_h`, so `p'_h = lo + ℓ` and `s'_h = s_h + k`; slab ownership, page tables, slots, ref, F, key, Index, `T_h`, `X_h`, `ρ_h` and `c_h` are unchanged. "Submitted" must not be counted as "completed", and drafts are not part of `T_h`.

A plan is a data and metadata commitment; it does not prove the GPU has executed it. A CPU adapter must not recompute addresses with a different B or unit size, or modify the plan.

### C4. finish_write(ticket, completion) -> Result<ComputedFrontier>

Purpose: after a computation has really completed, advance the valid frontier, commit accepted drafts, and publish newly completed blocks.

**Protocol condition:** ticket is a currently valid pending ticket of this coordinator and the oldest ticket in its lease's `Q_h` (D21). An unknown, expired or reused ticket, one belonging to another coordinator, or one completed out of issue order returns InvalidTicket without changing state; an out-of-order ticket stays pending. `completion` carries the ticket, the acceptance count `n`, optionally the token `x` the ticket sampled after its input and accepted drafts, the accepted drafts `D[0:n]` for a continuation with `k > 0`, and the flag `stop`.
- An orphan (D25) accepts any completion: the other fields are ignored.
- Otherwise `n <= k` is required, and `n = 0` for `k = 0`. A continuation with `k > 0` requires exactly n valid draft tokens; for a ticket with known drafts, reported drafts are ignored. If the ticket heads `X_h` and `stop` is false, `x` is required; with `stop`, `x` is optional. If the ticket does not head `X_h`, `x` is ignored, with or without `stop`: no extend_deferred reserved its bonus position, and the caller keeps that token as output, as for the last token of a request in v0.4.1 (C2).
- A violation returns InvalidArgument without changing state; the ticket stays pending, so a corrected completion can still be delivered.

**External premise Completed(ticket):** the completion comes from the executor and confirms three things: the reads and writes for this ticket have finished in every class, including the proposal forward when the plan has `propose`, they used the planned inputs and addresses and the window resolved from the producer's outputs, and the new KV and state satisfy the executor spec, including the state rebuild for the acceptance count the device used (E11). Without `stop`, the reported `n`, `x` and drafts are the ones the device used (E13). How this fact is obtained from CUDA/NCCL is not proved by this module. A bool supplied arbitrarily by a caller must not be treated as proof of physical completion (E1). For a load ticket the premise is E14's instead: every copy of its plan has finished, byte for byte. No forward ran, so the loaded KV's provenance comes from the host units (I20), not from E2.

The acceptance count needs no assumption for this module's guarantees: every `n <= k` yields a valid state over `T'_h = T_h ++ D[0:n]`, because the KV at position `z + i` was computed from `T_h[0:z] ++ D[0:i+1] = T'_h[0:z+i+1]`. Whether `n` follows the rejection-sampling rule is the sampler's correctness, not the block manager's. With `stop`, n may be smaller than the count the device used, because the caller truncates at a stop token inside the accepted span (D25).

Let t be the ticket, h its lease, and, when t is not an orphan, `a = c_h` its start (exact, since t is the oldest), `z = a + ℓ`, D the plan's drafts or, for a continuation, the reported drafts, and n the acceptance count. (In C4, §3.3 and §7, `n` is the acceptance count; in C3 it is the input chunk length `ℓ`.)

**Postconditions on success, for an orphan:** the ticket is removed from the front of `Q_h` and consumed exactly once; nothing else changes. In particular `T_h`, `c_h`, every `V_c` and `W_c`, every key and every `Index_c` are unchanged. Returns `c_h`.

**Postconditions on success, otherwise:**

- `T'_h = T_h ++ D[0:n]`, followed by `x` if t heads `X_h` and `x` is given; t is removed from `X_h` if it heads it. `c'_h = z + n`; the pending ticket is consumed exactly once; page tables, slots and `ρ_h` are unchanged. So `L'_h <= ρ_h`, and when `n > 0`, or when t heads `X_h`, `c'_h` is `L'_h` or `L'_h - 1`.
- When t heads `X_h`, every position below `c'_h` was already in `T_h` or is an accepted draft (I17), so the KV credited, the keys computed and the blocks published by this call never depend on `x`. `x` enters a key only when a later ticket completes the block that holds it.
- The ticket is removed from the front of `Q_h`. Without `stop`, every later ticket of the lease has its `base` raised by n, so the next one starts exactly at `c'_h`; with `stop`, they become orphans (below). Their plans are unchanged.
- For every `c ∈ Cp`, in ghost `V_c`, the provenance of `[a, z+n)` matches `T'_h`; other valid slots are unchanged. Slots at the rejected positions `[z+n, z+k)` and the proposal rows gain no claim. This holds in drafter classes too.
- For every `c ∈ Cs`, `W_c[σ_h^c] = (Namespace, T'_h[0:z+n])` under E11 without `stop`, and `⊥` with `stop`.
- For every `c ∈ Cp` and every newly completed whole block i with `a<(i+1)B<=z+n`, `K(h,i)` is published on `M_h^c[i]` and `Index_c` updated, with keys computed over `T'_h`; partial blocks must not be published. `K(h,i)` is computed once per block, sequentially from the chain head (the key of the last published complete block, or `Seed(ns)`), and used for every paged class, target and drafter. The chain head can be kept as the key at block `floor(c_h/B)-1`, but that is an implementation detail.
- With `stop`: every later ticket of the lease becomes an orphan, `X'_h` is empty and `stopped'_h` holds (D25, I18). What was committed up to `c'_h` is kept and published as above.
- Slab ownership, existing read-only cache pages, ref, F and other requests' state are unchanged. When different pages of one class have the same key, the index keeps all candidates.
- For a load ticket, the reference it holds on each host source is dropped (`ref^H_c` decreases by one), and a source with no reference left returns to `F^H_c`. The sources stay published; nothing else in the host tier changes.
- Returns `c'_h`.

**Load tickets (D31).** A load ticket has `k = 0`, never heads `X_h` and is never an orphan, so the rules above already fix its completion: `n = 0` is required, a reported token or drafts are ignored, and `stop` is allowed. Without `stop` the result is that of a ticket with `n = 0`: `T'_h = T_h`, `c'_h = z = k*·B`, `V_c` of every slot of `[k_d·B, k*·B)` matches `T_h` in every paged class, and the blocks `[k_d, k*)` are published in every paged class under `K(h,i)`, computed over `T_h`. With `stop`, the same prefix is committed, the lease is stopped, and the ticket behind the load, if any, becomes an orphan: this is how a caller ends a request whose load is in flight. A load ticket's completion never fails (E4): the caller reports it only once the copies are done.

This version assumes writes always succeed (E4), so there is no "failed completion" branch and no abort; `finish_write` handles only successful completion. A verify that accepts no draft (`n = 0`) is a successful completion, and so is a completion with `stop`. An executor that cannot guarantee E4 must first stop the affected execution and prove that doing so is safe; that is a future extension.

### C5. release(h) -> Result<TokenSnapshot>

Purpose: release all of a lease's references when its request finishes or is preempted.

**Valid call:** h is valid and `Q_h` is empty, so `X_h` is empty too (I17). A stopped lease is released the same way once its orphans have completed. Any pending ticket, orphans and a load ticket included, returns Busy; an invalid handle returns InvalidHandle, and a repeated release must not decrement references a second time. Pending stores of h do not block release (D30).

**Postconditions on success:**

- Returns the full input snapshot held by the lease, including every accepted draft, so the caller can keep the request's logical state; the user's output sequence is not deleted or modified. Rejected drafts are not in it. For a stopped lease it ends at the committed prefix: drafts after the stop and anything an orphan produced are not in it, and neither is a final token sampled by a ticket that did not head `X_h`; the caller keeps that one as output.
- Removes h from Req, permanently invalidating h.
- For every `c ∈ Cp`, decrements `ref_c` exactly once for each g in the original page table, including the reserved pages past `L_h`. Pages whose count reaches 0 enter `F_c`; pages still referenced elsewhere, by another lease or by a pending store, do not. A page that only a store still references enters `F_c` when that store completes (C10).
- For every `c ∈ Cs`, `ref_c[σ_h^c]` drops to 0 and the slot enters `F_c` with `W_c = ⊥`.
- Published keys, every `Index_c` and KV are kept for later reuse; unfinished partial blocks still cannot be cache hits.
- Slab ownership is unchanged; a slab whose units all become free stays with its class and becomes reclaimable (D11).
- Other active leases' inputs, page tables, slots, valid frontiers and pending tickets are unchanged, and so are pending stores and the host tier. Release itself does not zero KV or state, does not evict active units, and does not decide scheduler state.

After release, the same business request can attach again with the returned T and obtain a new handle; this is the preemption recovery path. With `Cs ≠ ∅` it restarts from `c = 0` (D13). Draft proposals that were never verified are the caller's to drop or keep; the coordinator holds none. Under ZOS a finished request is released only after its last in-flight step completes. A caller that wants a released request's blocks to survive in the host tier calls begin_store before release; its pending stores keep the blocks' pages allocated, so a re-attach before they complete still hits them on the device.

### C6. inspect(h) -> Result<LeaseView> (read-only helper)

Returns the input length `L_h`, the deferred tail `X_h` and the planned input length `L̂_h`, the computed frontier `c_h`, the planned frontier `p_h`, the reach `ρ_h`, an immutable view of each paged class's page table (target and drafter), each state class's slot, the planned slack `s_h`, `stopped_h`, the pending queue `Q_h` with each ticket's kind (compute or load), start bound, slack, input length, draft count, proposal flag, producer and orphan flag, and this instance's B, λ, μ and δ. No side effects.

If the optional `slot_of(c, h, j)` is provided, it only guarantees the correct allocated token-slot index for `c ∈ Cp` and `0<=j<ρ_h`; only for `j<c_h` may it also claim that the slot's KV is valid. Invalid handles, classes or indices return explicit errors.

v0.8 does not require can_allocate/can_append. A preview may only be read-only advice or a plan bound to a state version; it cannot unconditionally guarantee that it will still be executable after later state changes. C8 is such advice, for the cache only.

### C7. arena() -> ArenaView (read-only helper)

Returns `owner[s]` for every slab, and `|F_c|` and `|R_c|` (with `Prot = ∅`) for every class, target, drafter and state. With a host tier it also returns `owner^H[s]` for every host slab, `|F^H_c|`, `|R^H_c|` and the number of keyed host units for every host class, and the number of pending stores. No side effects. It is observability for the scheduler, not a reservation.

### C8. probe(T, κ) -> Result<(cached_tokens, loaded_tokens)> (read-only helper)

Purpose: tell a scheduler where a request would resume before it attaches, and how much of that a load would copy (D26, D31).

**Valid input:** as C1: an empty T returns InvalidArgument, and T with `¬Fits(ceil((L+μ)/B))` returns RequestTooLarge.

**Result:** on valid input, `(k*·B, (k* - k_d)·B)`, with `k_d` and `k*` exactly as in C1 for `(T, κ)` over the current state. No side effects: every class's state, every host class's state, `Index_c`, `Index^H_c` and slab ownership in both arenas are unchanged (only the ghost hash log of E8 grows). So an attach of `(T, κ)` that follows with no call between them has exactly that device run and host run, whenever it succeeds. probe does not reserve, and its answer can go stale both ways: a call between them may revoke a key, in either arena, by fresh allocation or slab reclaim, so that the attach may hit or load less; or it may publish more of the prefix, on the device (`finish_write`) or in the host tier (`finish_store`), so that an attach with a larger `κ` may hit or load more, and a block probe counted as loaded may be a device hit instead. With probe's first number as `κ`, the attach never resumes past what probe reported. A scheduler that would rather recompute the host run than load it attaches right after probe with `κ = k*·B - loaded_tokens`, the device run. Without a host tier the second number is 0 and the first is v0.7's result (obligation 31).

### C9. begin_store(h, i0, i1) -> Result<(Option<(StoreId, StorePlan)>, Set<StoreId>)>

Purpose: copy complete blocks of a lease to the host tier, so that a later attach can load them after their device pages are gone (D30).

**Valid call:** h is valid, stopped or not, with or without pending tickets, and `0 <= i0 < i1 <= floor(c_h/B)`: every block in the range is complete, so it is published in every paged class (I5b) and its pages no longer change (I7). An invalid handle returns InvalidHandle, checked first; an empty range, or one that reaches a block that is not complete, returns InvalidArgument.

**Blocks to copy, protected copies, and the stores relied on.** From the pre-call state, for each `c ∈ Cp`:

\[
\begin{aligned}
J_c&=\{\, i\in[i_0,i_1) \mid Index^H_c[K(h,i)]=\varnothing \ \land\ \text{no pending store writes } K(h,i) \text{ in class } c \,\},\\
P_c&=\{\, g\in F^H_c \mid key^H_c[g]=K(h,i) \text{ for some } i\in[i_0,i_1)\setminus J_c \,\},\\
d^H_c&=|J_c|+|P_c|, \qquad Prot^H=\{\, \text{the host slab of } g \mid c\in Cp,\ g\in P_c \,\},
\end{aligned}
\]

and `relies_on` is the set of pending stores that write `K(h,i)` in some class for some `i ∈ [i0, i1)`. `J_c` holds the blocks to copy in class c; a block that a host class already holds, or that a pending store is writing there, is skipped in that class only, so the sets may differ between classes. `P_c` holds the free host copies of the skipped blocks: like the free cache hits attach reactivates, they count in the demand and their host slabs are protected, so this call neither takes them as fresh units nor reclaims them (D30). Host copies of blocks before `i0` are not protected.

**Result.** If every `J_c` is empty, begin_store returns `(None, relies_on)` and changes nothing; no store id is consumed. Otherwise:
- `Σ_{c ∈ Cp} ceil(|J_c| / n^H_c) > N_H`, so that the copy would not fit even an empty host arena, returns RequestTooLarge. Without a host tier (`N_H = 0`) this is every valid call.
- Otherwise, an exhausted store id space returns IdentifierExhausted.
- Otherwise begin_store succeeds if and only if `Cap^H(d^H, Prot^H)` holds, and returns NoCapacity when it does not. It must not return NoCapacity because of a poor donor or slab choice when a feasible host slab plan exists.

The state is unchanged on every error.

**Postconditions on success:**

- The host slab plan of §3.5 is performed for `(d^H, Prot^H)`.
- For each `c ∈ Cp` and `i ∈ J_c`, a distinct fresh host unit `g^H_{c,i}` is taken from `F^H_c \ P_c`: its old key, if any, is revoked and its `Index^H_c` entry removed, and it gets `ref^H_c = 1` and no key. A host unit with a key is taken only if every unkeyed free host unit of class c, after the host slab plan, is taken too. The units of `P_c` keep their keys.
- For each `c ∈ Cp` and `i ∈ J_c`, `ref_c[M_h^c[i]]` grows by one: a store reference (D30). Device slab ownership, every `F_c`, every device key and `Index_c`, every lease and every ticket are unchanged.
- So on return every block of `[i0, i1)` is, in every host class, either held or written by a pending store.
- Returns a fresh store id st, with `Stores[st]` holding the pairs `(i, K(h,i), M_h^c[i], g^H_{c,i})` for every `c ∈ Cp` and `i ∈ J_c`, its store plan (§3.4), and `relies_on`.

begin_store does not look at the device cache: it copies the lease's own pages, whether or not other pages hold the same keys. It holds no reference to the lease, so `release(h)` may follow at once (C5). Which blocks to store, and when, is the caller's policy; storing each block when `finish_write` completes it and storing the rest before release are both valid. A caller that wants the whole prefix in the host tier passes `i0 = 0`: blocks already held cost nothing but are protected for the call. The skipped blocks that another store is writing are in the host tier only once that store completes with `stored`. If a store in `relies_on` fails, those blocks are missing, and the caller can call begin_store again for the range while the lease still holds them (C10).

### C10. finish_store(st, stored) -> Result<()>

Purpose: after a store's copies have stopped, publish them, or drop them if the store failed or was cancelled, and return the store's device pages (D30).

**Protocol condition:** st is a pending store of this coordinator. An unknown, consumed or foreign store id returns InvalidTicket, the error for an id that names no pending ticket or store, and the state is unchanged. Stores complete in any order, independently of every lease and ticket.

**External premise:** E14: the executor has stopped every copy of st and will never touch its units again; with `stored = true`, every pair's copy finished, byte for byte. A cancelled store is reported with `stored = false` once the executor has dropped or drained its copies.

**Postconditions on success:**

- st is removed from `Stores`; it is consumed exactly once.
- For every pair `(i, K, g, g^H)` of st in class c, `ref_c[g]` decreases by one. A page that reaches 0 enters `F_c` with its key: it is a cached page, and a later attach can still hit it.
- With `stored = true`, every destination is published: `key^H_c[g^H] = K`, `Index^H_c[K] = {g^H}`, and `V^H_c` of `g^H`'s B slots holds class c's KV for the last block of `den(K)`'s prefix (I20, from I5 and E14). Its `ref^H_c` drops to 0, so it enters `F^H_c` as a host cache entry.
- With `stored = false`, every destination returns to `F^H_c` with no key, and its `V^H_c` is unconstrained. Nothing is published. A store that relied on st (C9) is not changed: the blocks it skipped because st was writing them are now missing from the host tier, and a later begin_store over them copies them again.
- Slab ownership in both arenas, every lease, every ticket, every device key and `Index_c`, and every other host unit are unchanged.

## 7. Edge cases that must be reviewed

| Scenario | Expected behavior |
|---|---|
| Empty input | attach returns InvalidArgument; state unchanged |
| Single-block input, or input of exactly B tokens | attach has k*=0; the last block still needs computing |
| Input of exactly 2B with both blocks cached (no state class) | Reuse at most the first block; must not mark the whole input as computed |
| Prefix hit on an active page | Add a reference, which can reduce the free units needed; that page must not be written |
| Prefix hit on a cached page with ref=0 | Reactivate it; this consumes one free-unit slot, and its slab is protected for this call |
| Same current-block tokens, different preceding context | The chained keys differ; must not reuse |
| Tail block not full (L not a multiple of B) | The block has no key and is not in any Index; no hit even with identical tokens |
| Tail block completed by extend, then finished | Published only then, in every paged class; a partial block is never published |
| Two requests attach the same T one after the other (no state class) | The second reuses published pages and adds references; both start computing from k*B |
| Two requests attach the same T, with a state class | Both attach with k*=0 and get distinct live slots; pages are published but not hit (D13) |
| Several candidates for one key | Prefer an active candidate, so a servable request is not wrongly rejected |
| Two paged classes, the prefix is cached in one but not the other | The device run `k_d` stops at the first position missing in any class; with a host tier, the host run may continue from there (D31) |
| Paged class needs 2 more pages, has 1 free, `FS = ∅`, no reclaimable slab anywhere | NoCapacity; must not allocate one page and leave a half-done state |
| `u_c` does not divide `S` | create returns ConfigError (A1) |
| `S = lcm(96 KiB, 640 KiB) = 1.875 MiB` | `n = 20` pages and `3` state slots per slab; unit g of each class is at `g·u_c` with no tail waste |
| attach of a hybrid lease when the state class has a free slot in an owned slab | No slab acquired for the state class |
| attach of a hybrid lease, state class full, `FS = ∅`, a paged slab with all pages ref=0 but keyed, paged class keeps `>= d` free outside it | Reclaim that slab: its keys and Index entries are revoked, and it becomes a state slab; success |
| Same as above, but the paged class's free units are spread over partly used slabs | NoCapacity, even if free bytes exceed `u_state` (D12) |
| A reclaimable slab holds the only free candidate for a hit position of this attach | Not reclaimed in this call (`Prot`) |
| `FS` non-empty and a reclaimable slab exists | The free slab is used; nothing is reclaimed |
| Release of the last lease using a slab | The slab stays owned and becomes reclaimable; keys are kept |
| attach, extend or extend_deferred needs fresh units in a class whose free units include unkeyed and cached ones | The unkeyed units are taken first. A cached unit is taken, and its key revoked, only if every unkeyed free unit of that class, after the slab plan, is taken too. Free slabs do not spare cached units: §3.5 rule 1 grants a slab only when `|F_c| < d_c`, and `F_c` counts cached units. A reclaimed slab loses its keys (rule 3) whatever unkeyed units its class keeps. Which cached unit goes first is not fixed (D9) |
| extend of a hybrid lease | State demand is 0; only paged classes may need units or slabs |
| attach of an input with `¬Fits(m)` | RequestTooLarge even on an empty arena, not NoCapacity |
| First plan of a lease (`a = 0`) with a state class | `init = true`; the executor initializes the slot before reading it (E10) |
| In-flight ticket not yet complete | release returns Busy, and so does extend when `δ = 0`, when the ticket has drafts or `propose`, or when the queue is full (C2 allows it only behind tickets with `k = 0` and no `propose`); its pages and slots cannot be reclaimed, so their slabs are not in any `R_c` |
| The same completion arrives twice | The second is InvalidTicket; the frontier and publication do not advance twice |
| An old handle or old ticket arrives after preemption | Rejected; it does not act on the new lease |
| B=512, execution position j=256, M[0]=0 | The slot must be 256; must not rely on Sequence's default B=256 |
| Many distinct prompts published, then their pages reused or slabs reclaimed (long-running churn) | Stored Index entries stay ≤ `|U_c|`; no entry survives for a key with no candidates, or for a unit outside `U_c` (I11, I13) |
| **Speculative decoding (v0.4)** | |
| `δ = 0`, `λ = 0`, `Cx = ∅`, `N_H = 0` | Every method behaves exactly as in v0.3, except that extend at `p_h < L_h` now succeeds (D27) and attach_capped, probe, begin_store and finish_store are new; `begin_write` with non-empty drafts or with `propose` returns InvalidArgument (obligation 18) |
| `Cx ≠ ∅` with `λ = 0` | create returns ConfigError |
| attach of `L = 2B - 1` with `λ = 3`, `B = 64`, no drafter class | Page tables cover `m^+ = ceil(130/64) = 3` blocks in every paged class, not 2; the demand counts 3; `Fits(3)` decides RequestTooLarge |
| attach where `Fits(ceil(L/B))` holds but `Fits(ceil((L+μ)/B))` fails | RequestTooLarge: the reservation is part of the lease |
| Verify ticket with `k = 4` drafts, all accepted (`n = 4`) | `T'_h = T_h ++ D`, `c'_h = L'_h = L_h + 4`; KV at all four draft positions is credited; `ρ_h` unchanged, so `ρ_h - L'_h = λ - 4` |
| Verify ticket with `k = 4`, `n = 0` | `T_h` and `c_h = L_h` as before the ticket; no draft position is credited; nothing is freed or published; a later ticket overwrites those slots |
| Verify ticket with `k = 4`, `n = 2`, where position `z + 1` completes block i | Block i is published under `K(h,i)` over `T'_h` (which includes the two accepted drafts); positions `z+2, z+3` are not credited |
| Verify ticket whose rejected drafts complete a block | The block is not published; no key is computed over a rejected token |
| Rejected drafts would complete a block whose tokens equal a cached block | No hit, no publication: keys are only computed over `T_h` |
| `begin_write` with drafts while `c_h + n < L_h` | InvalidArgument: drafts must follow the whole input |
| `begin_write` with more than `λ` drafts | InvalidArgument; no partial reservation is taken |
| `finish_write` with `n > k`, or `n > 0` on a ticket with `k = 0` | InvalidArgument; state unchanged; the ticket stays pending |
| Same completion delivered twice with different `n` | The second is InvalidTicket; `T_h` and `c_h` advance once, by the first `n` |
| A second verify right after a verify (any `n`), without the bonus-token extend | `c_h = L_h`, so `begin_write` returns InvalidArgument (no remaining input); the caller must `extend` with the bonus token first |
| `extend` with the bonus token after `n = λ` accepted drafts | Demand counts `ceil((L'+μ)/B) - m_h`, which can be 1 or more pages; on NoCapacity the lease keeps its accepted drafts and `c_h = L_h` |
| Hybrid lease (state class), verify with `k = 3`, `n = 1` | The plan names the single slot `σ_h^c`; after finish, `W_c[σ_h^c] = T_h ++ D[0:1]`; no second slot is ever allocated for the state class |
| Hybrid lease, a ticket that covers the whole prompt (`a = 0`, `z = L_h`) and carries `k > 0` drafts | Allowed; the plan has `init = true` and `num_drafts = k`; the executor initializes the slot, then E11 applies as for any verify |
| attach of `L` with `λ = 4`, `B = 64` and a drafter class | `μ = 8`: page tables cover `ceil((L + 8)/64)` blocks in every paged class, target and drafter |
| Verify with `k = 4`, `propose`, a drafter class, `n = 2` | The drafter classes get KV at `[a, z+4)` from the verify forward and proposal rows at `[z+2, z+2+λ)`. After finish, `c'_h = z + 2` in every paged class; no drafter slot at or past `z + 2` is credited |
| Next verify after the bonus-token extend | Starts at `a = z + 2`, the bonus position, and overwrites the proposal rows from there with drafter KV from target hidden states |
| Verify with `k = λ`, all accepted, `propose` | Proposal rows end at `z + 2λ = L_h + 2λ = ρ_h`; no allocation |
| `propose` without a drafter class, or with `c_h + n < L_h` | InvalidArgument |
| Target prefix cached, drafter classes not (or the reverse) | The device run `k_d` stops at the first block missing in any paged class; the host run, if any, needs the block in every host class too |
| Drafter classes and target classes compete for slabs | One `Cap` over all classes; a drafter slab whose pages are all `ref = 0` is reclaimable for a target class and vice versa |
| Release after rejected drafts | The returned snapshot contains no rejected token; reserved pages past `L_h` return to `F_c` unkeyed |
| **Zero-overhead scheduling (v0.5)** | |
| `δ = 0`, `N_H = 0` | Every method behaves exactly as in v0.4.1, except that extend at `p_h < L_h` now succeeds (D27) and attach_capped, probe, begin_store and finish_store are new; extend_deferred never succeeds; a second `begin_write` while a ticket is pending returns Busy (obligation 20) |
| create with `δ = 2` | ConfigError (§1.1) |
| `δ = 1`: decode ticket t pending with `z = L̂_h`, then `extend_deferred(h)` and `begin_write(h, 1)` | Two tickets in `Q_h`. The second starts at t's `z`; its only input is deferred and its plan names t as the producer. `T_h` and `c_h` are unchanged |
| `δ = 1`, a third `begin_write` while two tickets are pending | Busy |
| extend_deferred with an empty queue, or while the newest ticket ends before `L̂_h` | InvalidPhase |
| extend_deferred while the queue is full (`\|Q_h\| > δ`) | Busy |
| extend_deferred whose position starts a new block when no unit can be had | NoCapacity; state unchanged. The caller waits for t and then uses `extend` |
| `finish_write` of the second ticket before the first | InvalidTicket; both stay pending |
| `finish_write` of a ticket that heads `X_h`, without a token | InvalidArgument; the ticket stays pending |
| `finish_write` of the producer t with token x | `T'_h = T_h ++ [x]`, `X_h` loses t, `c'_h = z`. The consumer's plan is unchanged |
| release while any ticket is pending | Busy |
| EOS sampled by step n while step n+1 is pending, no drafts | `finish_write(n)` appends the EOS to `T_h`. The caller plans no further step and calls no extend_deferred. `finish_write(n+1)` ignores its token and sets `c_h = L_h`, and release then succeeds. If the EOS at position `L_h - 1` completes block i, block i is published under `K(h,i)` over the real EOS token |
| Known (golden) token while step n is pending | `extend(h, [g])` succeeds when `X_h` is empty and the queue has room (v0.5 and v0.6 also needed `p_h = L_h`; D27); the next ticket's inputs are all known |
| extend while `X_h` is non-empty | InvalidPhase when every pending ticket has `k = 0` and no `propose` and the queue has room: a known token cannot follow an unknown one. Busy when a pending ticket has drafts or `propose`, or the queue is full, because C2 checks Busy first |
| `begin_write` with host-known drafts (`Known(D)`, `k > 0`) while a ticket is pending | Busy: behind a pending ticket, drafts come only from that ticket's proposal on the device (D21) |
| A ticket with known inputs behind a ticket with `propose` | Not possible: the proposing ticket ends at the end of the input, and extend returns Busy while it is pending. Only a continuation can follow it, and the continuation overwrites its proposal rows in issue order |
| Prefill chunk pending, next chunk issued behind it (`δ >= 1`) | Allowed; the second chunk starts at the first's `z`, and all its inputs are known |
| A block's last position is deferred when the ticket that writes its KV is issued | The block is published only when the frontier passes it, after the producer's completion has appended the token (I17) |
| Another lease's attach needs a slab while a lease has two tickets pending | The pending tickets' units are referenced by their lease, so their slabs are not reclaimable |
| **ZOS with speculative decoding (v0.6)**, `B = 4`, `λ = 2`, one drafter class, `δ = 1`, `μ = 3λ = 6`, unless stated otherwise | |
| Lease with `L = 7`, `c_h = 6`, `ρ_h = 13`; verify `t1 = begin_write(h, 1, Known([d1, d2]), propose)` | Target slots for 6–8, drafter slots for 6–10; `p_h = 7`, `s_h = 2` |
| Then `extend_deferred(h)` | `X_h = [t1]`, `L̂_h = 8`, `ρ_h = 14`. The bonus is counted at 7; its true place is `7 + n1` |
| Then `t2 = begin_write(h, 1, Deferred(2), propose)` | A continuation of t1: `lo = 7`, `s = 2`, `ℓ = 1`, `k = 2`. Target slots for 7–11, drafter slots for 7–13, ending at `ρ_h = 14`; no allocation |
| The device runs t1 with n1 = 0, 1 or 2 | t2's window starts at `7 + n1`: target 7–9, 8–10 or 9–11; drafter up to 11, 12 or 13. Every window lies inside the listed slots |
| `finish_write(t1, n=1, x=x1)` | `T'_h = T_h ++ [d1, x1]`, `c'_h = 8`, `X_h` empty. Block 1 (positions 4–7) is published. t2 is the oldest, and its start is exactly 8 |
| t2's listed slot for 7 lies on block 1, which t1's completion published | Allowed: t2's window starts at 8. Listed slots below `c_h` are never written (I9) |
| Then `extend_deferred(h)` and `finish_write(t2, n=2, x=x2, drafts=[e1, e2])` | extend_deferred makes t2 the producer: `L̂_h = 10`, `ρ_h = 16`, no new page. The completion appends `e1, e2` at 9–10 and `x2` at 11, and sets `c_h = 11`. Block 2 (8–11) is not published until a later ticket writes 11. Without extend_deferred, t2 is not in `X_h`, `x2` is ignored, and the caller appends it with `extend` |
| `finish_write` of a continuation with `k > 0` without drafts, or with `\|drafts\| ≠ n` | InvalidArgument; the ticket stays pending |
| `begin_write(h, 1, Deferred(2))` behind a verify, without extend_deferred first | InvalidArgument: no remaining input (`p_h = L̂_h`) |
| `Deferred(k)` with `k > 0` behind a producer without `propose` | InvalidArgument: there are no device drafts. `Known([])` is allowed, a plain continuation |
| A continuation behind a verify whose drafts are all accepted (n1 = 2), with `propose` | Its proposal rows end at `7 + 2 + 1 + 2 + 2 = 14 = ρ_h`: `μ = 3λ` is tight |
| EOS at d1 while the device accepts both drafts (device n = 2) | `finish_write(t1, n=1, stop)`: `T'_h = T_h ++ [d1]`, `c'_h = 8`; t2 becomes an orphan, `X_h` is empty, the lease is stopped. t2 ran from 9, past the frontier, and its KV follows a context the coordinator does not hold |
| EOS as t1's bonus | `finish_write(t1, n=1, x=EOS, stop)` appends `d1, EOS`; t2 becomes an orphan |
| `finish_write` of an orphan | Accepted with any fields; `T_h`, `c_h`, keys and ghosts unchanged |
| begin_write, extend or extend_deferred on a stopped lease | InvalidPhase, also once its queue is empty |
| release of a stopped lease | Busy while an orphan is pending; afterwards succeeds and returns `T_h`, which ends at the committed prefix |
| `stop` with an empty queue behind the ticket (any `δ`) | The lease is stopped with no orphans; release succeeds at once |
| Hybrid lease, t2 a continuation of verify t1 | Both plans name `σ_h^c`. The executor rebuilds the state for t1's device count before t2 reads it (E11, E13). After `finish_write(t1)`, `W_c = T'_h[0:c'_h]`; after `finish_write(t2)`, `W_c = T''_h[0:c''_h]` |
| t1's proposal rows and t2's window overlap in a drafter class | t2 overwrites them in issue order with drafter KV from target hidden states; neither is credited before t2 completes |
| A continuation's input is the last position of block i | Block i is published only when the frontier passes it, after t1's completion appended the bonus token (I17) |
| extend_deferred behind a verify when `1 + λ > B` | Demand may exceed one page per paged class, at most `ceil((1 + δ·λ)/B)`; NoCapacity leaves the state unchanged and the caller waits for t1 |
| attach of `L` with `B = 64`, `λ = 4`, a drafter class, `δ = 1` | `μ = 12`: page tables cover `ceil((L + 12)/64)` blocks; `Fits` decides RequestTooLarge |
| `λ = 0` with `δ = 1`, `N_H = 0` | Every method behaves exactly as in v0.5, except that extend at `p_h < L_h` now succeeds (D27) and attach_capped, probe, begin_store and finish_store are new; every slack is 0 and every continuation is a deferred decode step (obligation 24) |
| **Hit limit, probe and extend (v0.7)**, `B = 4`, no state class and no host tier, unless stated otherwise | |
| attach of 12 tokens whose first two blocks are cached, with `κ = 0` | `k* = 0`: a cold lease of fresh pages, unkeyed ones first. No cached page is in `Prot`, so a cached page loses its key if this attach takes it as a fresh page, which free slabs do not prevent (the row on unkeyed and cached units above), or reclaims its slab for another class |
| Same, with `κ = 5`, `κ = 8` and `κ = 12` | `k* = 1`, `2` and `2`: the limit caps at `floor(κ/B)` blocks, and the input at `m - 1 = 2` |
| `attach(T)` | Exactly v0.6's attach: the limit `L` caps nothing |
| probe of the same 12 tokens with `κ = 12`, then attach with `κ = 12` | probe returns `(8, 0)` and changes nothing; the attach hits exactly 2 blocks and reports 8 |
| probe with an empty input, or one that cannot fit with its reservation | InvalidArgument, RequestTooLarge |
| probe on a configuration with a state class | `(0, 0)` (D13) |
| probe, then a call that takes a probed page as a fresh page, then attach | The attach may hit less than probe returned; a block still hits if another candidate holds its key. probe reserves nothing |
| probe, then a `finish_write` that publishes more of the prefix, then attach | With `κ = L` the attach may hit more than probe returned; with probe's first number as `κ` it hits at most that |
| extend with `c_h < L_h` and no pending ticket (`δ = 0`) | Succeeds (v0.6: InvalidPhase); `c_h` and the computed prefix are unchanged, and the next ticket starts at `c_h` with known inputs up to the new `L_h` |
| extend behind a pending ticket that covers part of the input (`δ = 1`, `k = 0`) | Succeeds; the pending plan is unchanged, and the next ticket starts at its end |
| extend while `X_h` is non-empty | Still InvalidPhase (or Busy, checked first): a known token cannot follow a deferred one |
| extend_deferred while the newest ticket ends before `L̂_h` | Still InvalidPhase |
| **Host tier (v0.8)**, `B = 4`, one paged class, no state class, `δ = 0`, `λ = 0`, and a host tier with room, unless stated otherwise | |
| create with `N_H > 0` and a paged `u_c` that does not divide `S_H` | ConfigError (A1^H) |
| `N_H = 0` | Every method behaves as in v0.7; begin_store returns RequestTooLarge on every valid range, and probe's second number is 0 (obligation 31) |
| A lease with `L = 10` and `c_h = 9`; `begin_store(h, 0, 2)` | Copies blocks 0 and 1 (positions 0–7) into two fresh host units, and `M_h[0]` and `M_h[1]` each gain a store reference. Nothing is published in the host tier yet |
| `begin_store(h, 0, 3)` with `c_h = 9` | InvalidArgument: block 2 (positions 8–11) is not complete |
| begin_store of blocks that the host tier holds, or that a pending store is writing | Skipped; when nothing is left, it returns no store and consumes no store id. The stores that are writing skipped blocks are returned in `relies_on` |
| The host class has 2 free units, both cached, holding `K(h,0)` and an unrelated key; `begin_store(h, 0, 3)` with `c_h = 12` | `J = {1, 2}` and block 0's copy is protected (`d^H = 3`). With no free or reclaimable host slab: NoCapacity, rather than evicting block 0's copy to store blocks 1 and 2, which no load could then reach |
| A store that relied on another store, which then fails | The skipped block is missing from the host tier; begin_store again over the range, while the lease holds the block, copies it |
| `release(h)` while its store is pending | Succeeds. `M_h[0]` and `M_h[1]` keep their store references and stay out of `F_c`; finish_store returns them to `F_c` as cached pages |
| Re-attach of the released request while its store is pending | Blocks 0 and 1 are device hits: the store keeps their pages allocated and published, and they count as referenced candidates (`ref > 0`), so sharing them consumes no free unit |
| `finish_store(st, true)` | Both destinations are published under `K(h,0)` and `K(h,1)`; the store references are dropped |
| `finish_store(st, false)` | Both destinations return to `F^H_c` unkeyed and nothing is published; the store references are dropped |
| finish_store of a consumed or unknown store id | InvalidTicket |
| begin_store on a stopped lease | Allowed: it copies blocks below the committed `c_h` |
| begin_store with the store id space exhausted, or attach that needs a load ticket with the ticket space exhausted | IdentifierExhausted; state unchanged |
| begin_store needs 2 host units, the host class has 1 free, `FS^H = ∅`, and no host slab is reclaimable | NoCapacity; no store reference is added and no host unit is taken |
| begin_store of more blocks than an empty host arena holds | RequestTooLarge |
| begin_store when a host class's free units include unkeyed and cached ones | Unkeyed units first; a cached unit's key is revoked only if every unkeyed free unit of that class, after the host slab plan, is taken too |
| Two paged classes; one host class needs a host slab, `FS^H = ∅`, and a slab of the other host class has only unreferenced units, some of them keyed and none protected by this call | Reclaimed if the other class keeps enough free units outside it; its host keys are revoked |
| A host slab with a unit that a pending load reads or a pending store writes | Not reclaimable; the unit is not free, so begin_store does not take it either |
| A device slab with a page that only a pending store references | Not reclaimable until the store completes |
| Two paged classes, and a block that one host class holds and the other does not | begin_store copies it in the other class only; attach loads it only once both host classes hold it |
| attach of 12 tokens with `κ = 12`: block 0 cached on the device, block 1 in the host tier only | `k_d = 1`, `k* = 2`: `c_h = 4`, a load ticket for positions 4–7 heads `Q_h`, `p_h = 8`, and attach returns 8. The demand and `Prot` are v0.7's for a hit of 1 block |
| `finish_write` of that load ticket | `c_h = 8` and `T_h` is unchanged; block 1 is published on the device under `K(h,1)`; the host source loses the load's reference and stays published |
| `finish_write` of a load ticket with `n > 0` | InvalidArgument (`k = 0`) |
| `finish_write` of a load ticket with `stop` | `c_h = 8` and the lease is stopped; with `δ = 1`, a ticket queued behind the load becomes an orphan |
| probe of the same 12 tokens with `κ = 12`, before that attach | `(8, 4)`, and nothing changes |
| The same attach with `κ = 4` | `k* = k_d = 1`: no load |
| Block 0 in the host tier only, block 1 in both arenas | `k_d = 0`, `k* = 2`: both blocks get fresh pages and are loaded. Block 1's device copy is not shared: its page would lie above `c_h = 0` (I16) |
| `L = 16`: block 0 on the device, block 1 nowhere, block 2 in the host tier | `k* = k_d = 1`: the host run must continue the device run |
| `begin_write`, `extend` or `extend_deferred` while the load is pending, `δ = 0` | Busy, as behind any pending ticket |
| `begin_write(h, 4)` while the load is pending, `δ = 1` | A ticket for positions 8–11 queues behind the load; the executor runs it after the copies (E13(1)) |
| While the load is pending, `δ = 1`: `begin_write` with host-known drafts, `begin_write` with `Deferred(k)`, `extend`, `extend_deferred` | Busy (D21); InvalidArgument (no deferred position); succeeds (the load has `k = 0` and no `propose`); InvalidPhase (the load ends at `k*·B < L̂_h`) |
| release while a load is pending | Busy |
| Two leases attach the same prompt while the first one's load is pending | Both load from the same host units, whose `ref^H` counts both loads. The first lease's loaded pages are not published until its load completes, so the second cannot share them |
| A configuration with a state class and a host tier | `k* = k_d = 0`: attach never loads. begin_store copies, but nothing hits until state checkpoints exist (D13) |

## 8. Mapping from upstream methods and intentional changes

| Upstream interface | Contract interface | Change |
|---|---|---|
| BlockManager constructor | create | Fixes the arena, the class table and B, checks A1, and validates the representation range |
| can_allocate + allocate | attach | One atomic operation across every class; does not depend on an externally supplied num_cached_blocks |
| Sequence.append_token + can_append + may_append | extend | Grows the input snapshot and capacity (including the draft reservation) atomically; needs a scheduler adapter |
| seq.num_scheduled_tokens and runner preparation | begin_write | Produces an address plan for every class consistent with the instance, including the drafter's proposal rows, and records in-flight protection |
| hash_blocks + updating num_cached_tokens | finish_write | Commits the frontier, accepted drafts, state provenance and cache publication together after completion |
| deallocate | release | Release while in flight is forbidden; invalidated handles prevent double release |
| compute_hash | Cache identity | Chained 256-bit digest, both identity and index key, shared by every paged class; enters via the collision-resistance assumption E8 (§9) |
| kvspec `layout()` → `PhysicalPlan.paged.stride` / `.state.stride` | `u_c` of a paged / state class | The planner still decides bytes inside a unit; this contract decides which unit |
| kvspec `plan()` pool counts (`slots = ceil(slot_ratio · max_num_seqs)`, rest to blocks) | slab arena | The static split between blocks and state slots is replaced by on-demand slabs |
| `get_num_state_slots(max_num_seqs)` | state class units on demand | No fixed slot count; a slot exists for each lease that holds one |
| `KVCacheManager._view` over `[num_blocks, stride]` / `[num_slots, stride]` buffers | one arena viewed as `[N·n_c, u_c]` per class | Valid by A1; the views alias the same arena but distinct units never overlap (arena disjointness) |
| kvspec `Static` pool | outside the arena | Non-goal (§1.1) |
| vLLM `KVCacheManager.allocate_slots(..., num_lookahead_tokens)` (`vllm/v1/core/kv_cache_manager.py`, slot count at lines 541–544) | the reach `ρ_h = L_h + μ` set by attach / extend (D18) | vLLM reserves lookahead slots on every scheduling step; this contract reserves them only when the input grows, so a verify or a completion never allocates |
| vLLM scheduler `request.num_computed_tokens -= num_rejected` (`vllm/v1/core/sched/scheduler.py:2205–2214`) | finish_write with acceptance count n | vLLM schedules drafts as computed and rolls the counter back; this contract never credits a draft until it is accepted, so there is nothing to roll back and no key over a rejected token |
| vLLM spec tokens scheduled with the last input token | begin_write with `drafts` | The verify plan carries the drafts explicitly and is bound to them; drafts are not part of `T_h` |
| vLLM draft proposers (`SpecDecodeBaseProposer.propose` in `vllm/v1/spec_decode/llm_base_proposer.py:511`) and their KV groups | drafter classes `Cx` on the shared frontier (D20) | Drafter KV shares the arena, `Cap` and the frontier. vLLM's EAGLE proposer re-feeds the verified tokens shifted by one (`set_inputs_first_pass`, input shift at lines 840–846), so its drafter KV at j depends on the token at j+1; that drafter is a non-goal (§1.1). The supported MTP drafter writes its KV from target hidden states in the verify forward and proposes in one further forward |
| vLLM Mamba `num_speculative_blocks = num_speculative_tokens` (`vllm/model_executor/layers/mamba/abstract.py:84–90`) | non-goal (§1.1) | Extra state blocks per draft token are not modelled; this contract keeps one state slot per lease |
| vLLM KDA RecoverSSM (`use_kda_recoverssm`, `vllm/config/vllm.py:3418–3430`): `_kda_recoverssm_verify_kernel` (`vllm/models/kimi_k3/nvidia/ops/recoverssm.py:63–223`) reads the checkpoint and saves per-token records; `_commit_kda_state_kernel` (lines 400–583) rebuilds the accepted state; `_compact_conv_state_kernel` (line 322) shifts the conv window | one state slot per lease, with the records inside the state unit (D19, E11) | The checkpoint `S_0` is the slot's content after `T_h[0:a]` (I15); the commit writes `S_{z-a+n}` back to the same slot. Record buffers are sized by `append_kda_recoverssm_record` (`vllm/model_executor/layers/mamba/mamba_utils.py:331–349`) for `1 + num_spec` positions; under this contract they are part of `u_c` |
| vLLM `RecoverSSMState.commit_step` (`vllm/v1/worker/gpu/model_states/recoverssm.py:38–66`) | the executor side of finish_write for a verify ticket | Runs the state commit with the accepted count before the block manager is told; E11 requires it to finish before the completion is reported (E1) |
| vLLM `AsyncScheduler` spec-token placeholders (`vllm/v1/core/sched/async_scheduler.py:18–50`), whose real ids are filled in the worker, and `num_output_placeholders` | `Deferred(k)` drafts and the continuation's placeholder `input_ids` | vLLM counts output placeholders per request; pageproof counts the slack `s_h` and binds the drafts only when the continuation completes |
| vLLM align-mode prefix caching of Mamba state at block boundaries (`boundary_state_idx`, `boundary_recovery_len` in `recoverssm.py`) | not used | this contract has no state checkpoints (D13), so no boundary state is stored; deferred with state hits (§10) |
| vLLM `OffloadingManager` (`vllm/v1/kv_offload/base.py:283–416`): `lookup`, `prepare_load` / `complete_load`, `prepare_store` / `complete_store` | attach's host run and load ticket; begin_store and finish_store (C1, C9, C10) | vLLM looks blocks up and loads them through a connector beside the block manager. Here the host tier belongs to the coordinator, a load is a ticket of the lease, and its completion is what credits the loaded positions. `complete_store(success=False)` is `finish_store(st, false)` |
| vLLM CPU offload `ref_cnt` (`vllm/v1/kv_offload/cpu/manager.py:209–254`): a chunk being loaded is not evictable, and a chunk being stored is not readable until `complete_store` | `ref^H_c`, I19 and I20 | The same protection, stated as an exact count in the invariant. A host unit is findable only once its store has completed |
| vLLM `prepare_store` skips chunks that are stored or being stored, and never evicts the offered keys to make room (`cpu/manager.py:256–339`) | begin_store's `J_c` and `P_c` (C9) | The same deduplication and the same protection, per host class: the protected copies count in the demand and their host slabs are not reclaimed, so `Cap^H` stays exact. Beyond unkeyed-first, which cached host unit a store evicts is not fixed (D9, D29) |
| vLLM's offloading scheduler lets a finished request's blocks be freed while their stores are in flight, and flushes the pending stores of any block it re-allocates (`request_finished` and the flush in `vllm/distributed/kv_transfer/kv_connector/v1/offloading/scheduler.py:2130–2170`, `1962–1974`) | store references (D30) | A page with a pending store stays allocated, so nothing waits on a store and nothing needs a flush. The cost is device memory held until the store completes (§10) |
| vLLM `kv_load_failure_policy` (`vllm/config/kv_transfer.py:88`) | E4 for load tickets | A load ticket must succeed; a failed load is outside the state machine (§1.1, §10) |

This is a new interface designed for a provable implementation; it cannot replace the old object without adaptation. In particular, `Sequence` may no longer hold an authoritative page table, state slot or cache frontier that can be modified independently. If a mirror is needed, it may only be exported from the core, and the adapter must be proved to use a consistent version.

## 9. Proofs the implementation must deliver

### 9.0 Main theorem and external assumptions

**Main theorem.** At every step of any valid trace, if the executor executes the plan returned by `begin_write`, with start bound `lo`, span `W` and class spans `W_c`, and writes the window that starts at the ticket's true start a, and executes every load and store plan by copying exactly its pairs (E14), then:

(a) for every paged class c, the plan's listed slots are exactly `slot_c(h,j)` (`j in [lo, W_c)`), distinct and within `[0, N·n_c·B)`, and the window is a run of `ℓ + k` of them (plus `λ` with `propose`) starting at index `a - lo <= s`; for every `c ∈ Cs`, the plan's slot is `σ_h^c`;
(b) for a ticket that is not an orphan, once every earlier ticket of the same lease in `Q_h` has completed (always true at issue when `δ = 0`), the ticket's start is `a = c_h`, every slot of `[0,a)` corresponds in ghost `V_c` to `(Namespace, T_h[0:j+1])`, and, for a plan with `a > 0`, `W_c[σ_h^c] = (Namespace, T_h[0:a])`. With `δ >= 1` a plan may run before those earlier tickets complete; E13 makes it read their slots only after they were written, and resolve its window from their device outputs. An orphan's window starts in `[c_h, lo + s]` (E13), and no provenance is claimed for what it reads or writes;
(c) after `finish_write` with acceptance count n of a ticket that is not an orphan, `T'_h = T_h ++ D[0:n]`, followed by `x` when the ticket heads `X_h`; every slot of `[a, z+n)` is updated to its prefix of `T'_h`; every state slot holds `(Namespace, T'_h[0:z+n])`, or `⊥` with `stop`; every newly published block i satisfies `den(key_c[M_h^c[i]]) = (Namespace, T'_h[0:(i+1)B])`; and no credited slot, key, published page or state provenance depends on a rejected draft, a tentative position, a proposal row, or an orphan's write. After `finish_write` of an orphan, `T_h`, `c_h`, every ghost, key and `Index_c` are unchanged;
(d) the bytes the window writes are disjoint from every published page, every shared page, every other lease's units, and the windows of every pending plan of another lease; the windows of one lease start, in issue order, where the previous ticket's credited prefix ends, and a later window overlaps an earlier ticket's writes only at its rejected rows and proposal rows (arena disjointness);
(e) `Valid(S)` is preserved, each method's frame conditions hold, and error paths satisfy the strong failure atomicity of §5 item 3;
(f) `begin_write` and `finish_write` change no device slab owner, no `F_c` and no `ref_c`, for every acceptance count; `finish_write` of a load ticket changes, in the host tier, only the references of its sources;
(g) every input of a pending plan is either in `T_h` or the bonus token of its producer, an older pending ticket of the same lease, and every draft of a continuation is a draft of that producer's proposal; once the producer and the continuation complete, `T_h` holds the tokens they reported, which by E13 are the tokens the plan consumed; and every position below `c_h` is in `T_h`;
(h) a stopped lease never gains a credited slot, key, published page or state provenance after the stop, and its returned snapshot is `T_h` at the stop;
(i) for a load ticket of lease h, the plan's pairs are exactly `(src_c[i], M_h^c[i])` for `c ∈ Cp` and `i ∈ [k_d, k*)`. Every source is a host unit with key `K(h,i)`, which no plan writes and which is neither taken nor reclaimed until the load completes; every destination is an exclusive unpublished page of h, which no other plan writes. After `finish_write` of the load, every slot of `[k_d·B, k*·B)` corresponds in `V_c` to `(Namespace, T_h[0:j+1])`, and every block i of `[k_d, k*)` is published with `den(key_c[M_h^c[i]]) = (Namespace, T_h[0:(i+1)B])`;
(j) for a store issued on lease h, the plan's pairs are exactly `(M_h^c[i], g^H)` for `c ∈ Cp` and `i ∈ J_c`. Every source is a published page with key `K(h,i)`, which no plan writes and which is neither reallocated nor reclaimed until the store completes, even after h is released; every destination is a host unit that only this store references. After `finish_store` with `stored`, every destination is published with `den(key^H_c[g^H]) = (Namespace, T_h[0:(i+1)B])`, for `T_h` at issue, and its `V^H_c` holds that block's KV; after a failed store nothing is published;
(k) `begin_store` changes no device slab owner, `F_c`, key or `Index_c`; `attach` and `finish_write` change no host slab owner and take no host unit; `finish_store` changes no slab owner in either arena; and in either arena no copy writes a unit that another pending plan or copy reads or writes, except between the tickets of one lease, which the executor applies in issue order (copy isolation, §4).

**External assumptions.** The following are not proved, but they must be listed and checked along the verified call chain. E8 is the only cryptographic assumption in this version. A1 is not an assumption: create checks it.

| ID | Assumption | Consequence if violated |
|---|---|---|
| E1 | Completion events are real: the executor confirms the reads and writes are done in every class and used the planned inputs and addresses | The frontier advances over unwritten or wrongly written KV or state |
| E2 | KV and state depend only on the prefix: values are independent of batch composition and chunking (within tolerance). For recurrent state this includes chunked versus step-by-step computation | The ghosts `V_c` of shared pages, or `W_c`, no longer hold |
| E3 | Calls are single-threaded and sequential (or serialized by the caller) | The invariants break under concurrency |
| E4 | Writes always succeed: every issued ticket, load tickets included, eventually completes successfully; no failed completion, silent drop, or process termination. A store is not a ticket: it may complete as failed (E14) | Pending never clears, and units stay occupied forever |
| E5 | The executor uses the planned slots, state slots, the instance's B and every `u_c`, and does not recompute addresses with other values. For a continuation, computing `slot_c(h, a + i)` from the plan's page mapping and B is allowed: it equals entry `σ + i` of `write_slots_c` | Writes to the wrong unit, slot or class |
| E6 | The Namespace is complete: the final field table covers weights, dtype, B, every class's kind, `u_c` and in-unit layout, rope/scaling, attention semantics and adapters, and the drafter when `Cx ≠ ∅`; v0.6 through v0.8 use a dummy byte string, and completeness is the caller's responsibility | Different semantics share keys, causing silent wrong reuse |
| E7 | `Canon`/`Enc` follow the §3.3 canonical encoding: fixed-width uint32 tokens, length-prefixed fields, fixed field order, domain separation | Structural collisions (probability 1) that E8 cannot cover |
| E8 | SHA-256 is collision resistant; the collision probability over `Q` key generations/comparisons during the deployment is `<= Q^2/2^257 + Q/2^256` | Wrong KV reuse across requests (a data leak under multi-tenancy) |
| E9 | The arena is one allocation of at least `N·S` bytes whose base is aligned to every class's required alignment (kvspec `Pool.align`), and every kernel addresses unit g of class c at `base + g·u_c` plus the kvspec region offset | Units of different classes alias, or kernels read misaligned or wrong bytes |
| E10 | When a plan has `init = true` for a state slot, the executor sets the slot to the model's initial state before reading it; it writes state only to the planned slot | A lease starts from another lease's leftover state |
| E11 | State rebuild in one slot: for a plan with `num_drafts = k` and a state class c, the executor reads the slot (the checkpoint, after the first a tokens), and before the ticket's completion is reported it leaves in the same slot the state after the ticket's input and its first `n_dev` drafts, where `n_dev` is the acceptance count the device used. A continuation reads that rebuilt state, so the rebuild must take `n_dev` on the device, in issue order (vLLM's `RecoverSSMState.commit_step` takes `num_accepted_tokens` as a device tensor, `vllm/v1/worker/gpu/model_states/recoverssm.py:38–44`). Without `stop`, `n_dev` is the reported n. Everything the rebuild needs (vLLM RecoverSSM's per-token corrections and key/gate records for `1 + λ` positions, the conv window widened by `λ`) lives inside the state unit, so `u_c` is sized for `λ`; it writes no other unit. With `k = 0` this is the v0.3 behaviour | The slot holds a state that includes rejected drafts or misses accepted ones, and every later step of the lease computes on a wrong state; or the records overflow into a neighbouring unit |
| E12 | Drafter executor, for every drafter class: (1) the drafter KV that a ticket's forward writes at position j is a function of the target model's hidden states at j, so it depends only on `T_h[0:j+1]`; this is E2 for drafter classes, and it excludes an input shift that reads the token at j+1; (2) with `propose`, the proposal forward writes only inside the plan's drafter write range, and only at positions `>= z + n`, where n is the acceptance count it reports. E6's Namespace covers the drafter and the target layers it reads | (1) Published or reactivated drafter pages carry KV of another prefix, and acceptance rates drop. (2) The proposal overwrites credited drafter KV. In both cases target KV and outputs are not affected, because acceptance is checked against the target model |
| E13 | ZOS executor: (1) it runs the tickets of one lease in issue order, so a ticket reads KV and state only after every earlier ticket of the lease has written them (one stream, or an equivalent dependency); (2) for a continuation, it resolves the shift `σ = a - lo`, the input token and the drafts from the producer's device outputs (its acceptance count, its bonus token, its proposal), and writes only the window those select from the plan (computing its slots from the plan's page mapping is allowed, E5); (3) the completion of a ticket without `stop` reports the acceptance count, bonus token and drafts the device used; with `stop` it reports a count no larger than the device's count, and `x`, if given, is the token the sampler emitted at position `z + n` (the accepted draft `D[n]` when n is below the device's count, the bonus token otherwise) | (1) A step reads KV or a state slot that is not yet written. (2) A continuation writes at the wrong positions or computes on inputs the coordinator never records. (3) The coordinator appends tokens different from the ones the model consumed, so `T_h`, the credited KV and every later key disagree; or, with an over-reported count under `stop`, an orphan's window lies below the frontier and overwrites credited KV |
| E14 | Copy executor (v0.8): (1) the completion of a load ticket, or of a store, is reported only after every copy of its plan has stopped, and the executor never touches the plan's units after that; (2) a load, and a store completed with `stored`, copied each pair's `u_c` bytes verbatim, from the planned source unit to the planned destination unit of the same class, and wrote nothing else; a store completed without `stored` may have written its destinations but nothing else; (3) E13(1) covers load tickets: a ticket queued behind a load reads the loaded pages only after the load's copies have finished; (4) every store is eventually completed, with or without `stored` | (1) A unit is reused while a copy still reads or writes it. (2) The frontier advances over pages that do not hold the loaded KV, or a host entry holds bytes of another block, and every later load of it is wrong. (3) The next step reads KV that is not there yet. (4) Device pages and host units stay referenced forever |
| E15 | Host arena (v0.8): the host arena is one allocation of at least `N_H·S_H` bytes that the copy engine can read and write (page-locked if the engine needs it), aligned to every paged class's required alignment, and the copy engine addresses host unit g of class c at `base^H + g·u_c`, with class c's in-unit layout. E6's Namespace covers the host copies like the device pages | Copies land in the wrong place, alias another class's units, or change meaning between the arenas |

### 9.1 Proof obligations

1. **Initialization:** Valid holds after a successful create, and create returns ConfigError exactly in the cases listed in C0.
2. **Per-method preservation:** for every real method body, prove that Valid is preserved, together with the functional, error and frame conditions of C0–C10 and C2b, including the orphan and stopped-lease cases of C4 and its load tickets.
3. **Allocation sufficiency:** attach's k*, `r_c`, `d_c` and `Prot` match their definitions; with correct candidate choice, `Cap` guarantees success.
4. **Addressing and isolation:** slot range per class, no aliasing within a request, no conflicts between pending writes, distinct live slots, and shared pages are never written.
5. **Cache soundness:**
   - the canonical chained-key implementation (`Canon`/`Enc`/`Tag`/domain separation) is consistent with every `Index_c` in both directions;
   - the publication condition is correct in every paged class;
   - a page's identity is revoked before it is written for a new use, whether by fresh allocation or slab reclaim;
   - the chain lemma (§3.3) is proved in the ideal hash model, with E8 as the only cryptographic assumption for the concrete instance.
6. **Protocol correctness:** handle, ticket and store-id invalidation, single consumption of completions (including completions with different acceptance counts, and store completions), and in-flight units are never reclaimed, in either arena. Prove that the executor-interface premises hold along the verified call chain, or list them as explicit external assumptions (E1, E2, E5, E9, E10, E11, E12, E13, E14, E15).
7. **Termination and representation:** all loops terminate; machine-integer, array and set operations are safe; a verifier UNKNOWN or timeout is not a pass.
8. **Deployment link:** run the verified implementation or its trusted compiled output. A hand-rewritten version does not automatically inherit the proof. The digest implementation and the canonical `Canon`/`Enc` must match the proof's definitions byte for byte.
9. **Bounded metadata:** prove that every method preserves I11 (with I11a), so metadata stays O(Σ_c N·n_c + Σ_{c ∈ Cp} N_H·n^H_c) for traces of any length.
10. **Arena disjointness:** prove the theorem of §4 from A1 and I12, and that every unit address in a plan lies in `[0, N·S)`.
11. **Capacity exactness:** `Cap(d, Prot)` holds iff a slab plan following §3.5 rules 1–4 exists; the implementation acquires exactly `need_c` slabs per class, uses `FS` before reclaiming, never reclaims a slab in `Prot` or with a referenced unit, and never takes units from a slab it gave up in the same call.
12. **Reclaim correctness:** reclaiming a slab preserves I3, I8, I11 and I13, revokes every key in it, and changes nothing outside that slab's units and `owner`.
13. **Cross-class atomicity:** on every error path of attach, extend, extend_deferred and begin_store, slab ownership in both arenas and every class's state are unchanged; on success, no lease has resources in some classes but not others (I1, I14), and a store copies every block of every `J_c`, never a part of them (C9).
14. **Refinement of v0.2.1:** with `|Cp| = 1`, `Cs = ∅` and `N_H = 0`, every public method's observable behavior (results, errors, k*, cached tokens, plans up to page renaming) equals v0.2.1 with `P = N·n_c`, treating units of free slabs as unkeyed free pages. This lets the v0.2.1 proofs be reused for the paged class. Since v0.7 this holds for the methods v0.2.1 has, with attach as `attach(T)`, except one: extend at `p_h < L_h`, which v0.2.1 rejected with InvalidPhase, now succeeds (D27, obligation 28).
15. **Draft reservation:** every method preserves I16; attach and extend compute the demands of C1/C2 from `m^+` and `m'`, and `Cap` remains exact for them (obligation 11 with the new demands); `begin_write` and `finish_write` never change slab ownership, `F_c` or `ref_c`, and a valid `begin_write` never fails for capacity.
16. **Partial commit:** for every acceptance count `n <= k`, `finish_write` establishes I4, I5, I5b, I6 and I15 over `T'_h = T_h ++ D[0:n]`; `T'_h` extends `T_h`; `c_h` and `L_h` never decrease; no key is computed over a token outside `T'_h`; and a rejected or invalid count leaves the state unchanged.
17. **Drafter classes:** drafter classes are in lockstep with the other paged classes (same leases, inputs, frontier, reach and page-table lengths); with `propose`, the drafter write range `[a, w + λ)` lies inside the reservation and on exclusive unpublished pages; no proposal row is credited; every drafter write is disjoint from every unit of another class (obligation 10).
18. **Refinement of v0.3:** with `δ = 0`, `λ = 0`, `Cx = ∅` and `N_H = 0`, and completions without `stop`, every public method's observable behavior (results, errors, k*, cached tokens, plans up to page renaming, arena views) equals v0.3, with `drafts` empty and `n = 0`. This lets the v0.3 proofs be reused, and is proved before obligations 15–17. Since v0.7 this holds for the methods v0.3 has, with attach as `attach(T)`, except one: extend at `p_h < L_h`, which v0.3 rejected with InvalidPhase, now succeeds (D27, obligation 28).
19. **Executor premises for spec decoding:** E11 and E12 enter the proof only as the ghost updates of `finish_write` (W after a verify; V and publication in drafter classes). No other method body may depend on them, and the plan exposes `num_drafts` to state classes and `propose` to drafter classes so that E11 and E12 can be checked by an executor contract.
20. **Refinement of v0.4.1:** with `δ = 0`, `N_H = 0` and completions without `stop`, every public method's observable behavior equals v0.4.1: extend_deferred never succeeds, `X_h` is empty, `p_h = c_h` at every issue, every slack is 0, and a second ticket returns Busy. This lets the v0.4.1 proofs be reused, and is proved before obligations 21–23. Since v0.7 this holds for the methods v0.4.1 has, with attach as `attach(T)`, except one: extend at `p_h < L_h`, which v0.4.1 rejected with InvalidPhase, now succeeds (D27, obligation 28).
21. **Pipelined tickets:** every method preserves the queue invariants of §3.4 and I9 with queues of at most `δ + 1` tickets: issue order, contiguity, the queue shape of D21, and in-order completion. `extend`, `extend_deferred` and `finish_write` with later tickets pending keep every pending plan valid (known inputs in the unchanged prefix, each deferred input bound exactly once to its producer's token, page mappings in the page tables) and every listed slot at or past `c_h` on an exclusive, unpublished page.
22. **Deferred tail:** every method preserves I17. extend_deferred has the demands of C2b, and `Cap` stays exact for it. `finish_write` binds exactly one token per producer, exactly once, at position `L_h + n`, after the producer's n accepted drafts, or none with `stop` and no token. `T_h` only grows, no key is computed over a deferred position, and I4, I5, I5b and I15 hold over `T_h` unchanged while deferred positions exist.
23. **Executor premise for ZOS:** E13 enters the proof only as the ghost updates of `finish_write` for a ticket that had earlier tickets in its queue or deferred inputs, and as the fact that an orphan's window lies at or past `c_h`. No other method body depends on it, and the plan exposes `producer`, `lo` and `slack` so that E13 can be checked by an executor contract.
24. **Refinement of v0.5:** with `λ = 0`, `N_H = 0` and completions without `stop`, every public method's observable behavior equals v0.5: every slack is 0, every continuation has `k = 0` and is v0.5's deferred decode step, `Deferred(k)` with `k > 0` returns InvalidArgument, and plans equal v0.5's plans with `producer` in place of `deferred`. This lets the v0.5 proofs be reused, and is proved before obligations 25–27. Since v0.7 this holds for the methods v0.5 has, with attach as `attach(T)`, except one: extend at `p_h < L_h`, which v0.5 rejected with InvalidPhase, now succeeds (D27, obligation 28).
25. **Bounded start and reservation:** every method preserves the §3.4 relations of `lo`, `s` and `base`, and I16. A valid begin_write's span fits the reach for every acceptance count of the older pending tickets, so begin_write never fails for capacity; finish_write without `stop` sets the next ticket's start to exactly `c'_h`, and with `stop` every orphan's window starts in `[c'_h, lo + s]`.
26. **Overlapping windows:** for every acceptance count of every older pending ticket, a continuation's window lies inside its listed slots and at or past the producer's credited prefix, on exclusive unpublished pages. Its writes may overlap the producer's rejected rows and proposal rows, and never a credited slot or a published page.
27. **Stop and orphans:** every method preserves I18. finish_write with `stop` credits and publishes exactly the committed prefix, orphans every younger ticket, empties `X_h`, and sets `W_c = ⊥`; finish_write of an orphan changes only `Q_h` and `Pending`; begin_write, extend and extend_deferred return InvalidPhase on a stopped lease; release succeeds on a stopped lease once its queue is empty and returns `T_h` as committed.
28. **Refinement of v0.6:** with `N_H = 0`, `attach(T)` equals `attach_capped(T, L)` and has v0.6's C1 contract; the limit caps nothing because `ceil(L/B) <= floor(L/B) + 1`. extend accepts every call v0.6's extend accepted, with the same result; it also accepts calls with `p_h < L_h`, which v0.6 rejected with InvalidPhase.
29. **Hit limit and probe (D26):** attach with a limit has C1's contract with `k_d` and `k*` capped at `floor(κ/B)`, including the success-iff-`Cap` condition for the demand and `Prot` of the device run `k_d`; probe returns `(k*·B, (k* - k_d)·B)` for the same `(T, κ)` over the current state, changes no state of any class in either arena, no index, slab owner or id counter, and errs exactly as attach's input checks do.
30. **Extend before compute (D27):** extend with `p_h < L_h` preserves Valid, I9, I16 and I17: pending plans stay valid, the reach becomes `L' + μ`, and the room-to-issue clause of I16 holds because pending tickets have no drafts (`s_h = 0`).
31. **Refinement of v0.7:** with `N_H = 0`, every public method's observable behavior equals v0.7: attach's `k*` is `k_d`, v0.7's `k*`, and attach never issues a load ticket; probe's first number is v0.7's result and its second is 0; begin_store returns InvalidHandle, InvalidArgument or RequestTooLarge, so no store id is ever issued, and finish_store returns InvalidTicket. This lets the v0.7 proofs be reused, and is proved before obligations 32–37.
32. **Host tier (D28, D29):** every method preserves I12 and I13 for the host arena, I19 and I20. `Cap^H(d^H, Prot^H)` holds iff a host slab plan following §3.5 rules 1–4 exists, and begin_store acquires exactly `need^H_c` host slabs per class, free host slabs first, and never reclaims a host slab in `Prot^H` (obligation 11 for the host arena). Reclaiming a host slab preserves I19, I20 and I11 and revokes every key in it (obligation 12). begin_store takes unkeyed free host units before keyed ones.
33. **Store references (D30):** every method preserves I2 with store references, I6 and I21. begin_store's `J_c`, `P_c`, `relies_on`, results and errors are as in C9, and a valid call fails only as listed there. On success it takes no unit of `P_c`, so every block of its range is, in every host class, held or written by a pending store. While a store is pending, none of its source pages is taken as a fresh page, reclaimed or written, also after its lease is released. finish_store with `stored` publishes exactly the store's pairs, without `stored` none, and in both cases drops exactly the store's references in both arenas.
34. **Load tickets (D31):** attach computes `k_d` and `k*` as defined in C1, and succeeds iff `Cap(d, Prot)` holds for the demand and `Prot` of the device run, given the identifier conditions. The load ticket heads `Q_h` and preserves I9, I16, I17 and I22. `finish_write` of a load ticket establishes I4, I5, I5b and I6 over `[k_d·B, k*·B)` from I20 and E14, publishes exactly the blocks `[k_d, k*)`, and drops exactly the load's host references. probe returns `(k*·B, (k* - k_d)·B)` for the same `(T, κ)` and changes nothing.
35. **Copy isolation:** the theorem of §4. In either arena, no pending plan or copy writes a unit that another pending plan or copy reads or writes, except between the tickets of one lease, a load ticket included, which E13(1) orders. Every host address in a load or store plan lies in `[0, N_H·S_H)`, and every device address in `[0, N·S)`.
36. **Bounded metadata with a host tier:** every method preserves I11 with its host bounds: pending stores at most the number of host units, store pairs at most `N·n_c` per class, host index entries at most `|U^H_c|`, and reference counts at most `|dom(Req)| + 1` in both arenas.
37. **Executor premises for offload:** E14 and E15 enter the proof only as the ghost updates of `finish_write` for a load ticket (`V_c` of the loaded slots) and of `finish_store` with `stored` (`V^H_c` of its destinations). No other method body depends on them, and load and store plans list every source and destination unit, so that E14 can be checked by an executor contract.

### 9.2 Trusted base

1. E8 (SHA-256 collision resistance and the ε bound);
2. E6 (Namespace completeness) and E7 (canonical encoding): design obligations, not probabilistic assumptions;
3. trusted compiled output (§9.1 item 8);
4. E1/E2/E5/E9/E10/E11/E12/E13/E14/E15 (executor, copy engine and arena interface). E3/E4 are deployment assumptions (single thread, writes always succeed) and do not enter the method-body proofs.

Auxiliary lemmas, loop invariants and data structures may be designed by the agent. But new assumes, axioms, skipped function bodies, or weakened pre/postconditions must not be used to pass off a proof as complete. E1–E15 are explicitly listed external assumptions and must not become a loophole for new assumes.

v0.8 is to be implemented and proved in these steps, each keeping the behaviour with `N_H = 0` equal to v0.7 (obligation 31): (1) the host arena with one host class, as a `Manager` without leases whose references come from copies in flight, plus store references in the paged classes, begin_store and finish_store; (2) several host classes and the host slab plan; (3) the host run in attach and probe, load tickets and their completion; (4) the Python facade. Runtime tests are to cover the v0.8 rows of §7, and a randomised test is to run stores, loads, releases and re-attaches against a simulated copy engine that checks every copy's units. The copy engine itself belongs to the executor (E14) and is outside this contract.

v0.7 capped attach's hit run at the caller's limit, dropped `p_h = L_h` from extend's phase and added probe, each proved with the v0.6 lemmas generalised to a limit (`joint_kl`, `lemma_joint_kl`), plus a lemma that the limit `L` caps nothing; `pageproof-client` proves from the public specs that probe's answer is what the next attach takes. v0.3 was implemented and proved in these steps: the slab arena with one paged class and obligation 14; several paged classes with per-class Index and `Cap`; state classes and cross-class atomicity; the ticket/completion protocol across classes and the Python runner adapter. v0.4.1, v0.5 and v0.6 were implemented and proved the same way, one verified step at a time ([pageproof-rs#7](https://github.com/UranusSeven/pageproof-rs/pull/7)): (1) `λ`, `μ` and the reach `ρ_h` with the new attach/extend demands; (2) verify tickets and partial commit, with state classes taking `num_drafts`; (3) drafter classes and proposal rows; (4) queues of at most `δ + 1` tickets with in-order completion, and `extend` while tickets are pending; (5) `X_h`, extend_deferred and binding in `finish_write`; (6) the `lo`, `s` and `base` fields, continuations behind a verify ticket and `Deferred(k)` drafts; (7) `stop` and orphans; (8) the Python facade. Runtime tests in `crates/pageproof-core/tests` exercise the §7 table. `zos_fuzz.rs` there holds the randomised runtime tests this plan also called for: ZOS depth 1 against depth 0, and ZOS with speculation against plain decoding. Over random request mixes and a simulated executor, `δ = 1` produces the same token streams, release snapshots and published blocks as `δ = 0`, except where it binds a final EOS through `X_h` (§7). Speculation with clean and noisy drafts commits the same tokens as plain decoding. Every step checks the bounds, the isolation of pending tickets, each continuation's window against `slot_of`, and the KV and state each ticket reads. They are runtime checks, not proof obligations. Each step keeps the same external functional goals; properties left for later must not be counted as proved.

## 10. Decided and open

Decided in v0.2:

- Keys are chained 256-bit digests: the chain starts at `Seed(ns)` and appends each block's tokens; the digest is both identity and index key. Tail blocks have no key. Identity exactness rests on the explicit probabilistic assumption E8 (§3.3, D4).
- The invariant keeps the ghost `den` so that "which prefix a key describes" can be stated; the concrete layer stores only a 32-byte digest per page, with no intern table and no GC (§3.2, I5).
- `Canon`/`Enc` use the §3.3 canonical encoding; `Tag` is the scheme version; digests are 256-bit and never truncated.
- Single-threaded (E3), and writes always succeed (E4). Spec-decode, offload and multi-threading are non-goals (§1.1).
- `Pending` stores no `table_ver`; the derived invariants of §3.4 replace it.
- D2/D3 continue: attach reserves for the full input and recomputes the last block. D6/D7's atomic interfaces and explicit in-flight protection are unchanged.

Added in v0.2.1:

- I11 (bounded metadata) with I11a (distinct last pages); I8 tightened so that an empty candidate set has no stored entry.

Decided in v0.3:

- One slab arena per coordinator; slab size and unit sizes are user-chosen with A1 `u_c | S`, checked at create; `S = lcm` is the smallest choice (D10).
- Paged and state unit classes; paged classes keep v0.2.1 semantics on dynamic unit universes and share B and the key chain (D15).
- State classes hold one exclusive live slot per lease; no state keys, checkpoints or hits, so `k* = 0` when a state class exists (D13).
- Slabs are acquired on demand, free slabs first; a slab whose units all have `ref = 0` is reclaimable even if keyed, and reclaim revokes its keys; release never returns slabs (D11).
- Capacity is the exact predicate `Cap` over per-class free units and slabs; fragmentation is part of the contract (D12).
- A coordinator makes multi-class operations atomic and owns a single frontier and ticket per lease (D14).
- Spec-decode rollback, including state rollback rows and copies, remains a non-goal.

Decided in v0.4:

- Speculative decoding with linear draft chains of at most `λ` tokens, fixed at create (D16).
- Drafts are carried by the verify ticket, not by `T_h`; finish_write appends the accepted prefix and credits its KV; rejected drafts never enter `T_h`, any key or any publication; there is no truncate (D17).
- Every lease reserves `λ` positions past its input at attach and extend; tickets and completions never allocate or free (D18, I16).
- One state slot per lease; the executor rebuilds the accepted state in place, as vLLM's KDA RecoverSSM does (D19, E11). Extra state copies per draft remain a non-goal.
- Draft paged classes share the arena, `Cap` and the key chain, with their own frontier and `begin_draft`; draft KV at tentative positions is never credited (D14, D20, E12).
- One pending ticket per lease across both tracks, stated as a ticket queue `Q_h` of length at most `Q = 1` whose invariants allow the lease to grow while a ticket is live, so that v0.5 can raise `Q`.

Decided in v0.4.1:

- One frontier for every class again: drafter classes are paged classes on `c_h`, and the draft track, `e_h` and `begin_draft` are removed (D14, D20).
- A ticket at the end of the input may carry a proposal; the drafter classes' write range grows by `λ`, and proposal rows are never credited (D20, E12).
- The reservation is `μ = 2λ` with drafter classes (D18).

Decided in v0.5:

- ZOS depth `δ ∈ {0, 1}` fixed at create; ticket queues of at most `δ + 1` per lease; completion in issue order per lease (D21). `δ >= 2` is rejected because of EOS (D23).
- A token not yet on the host is a position of the deferred tail after `T_h`, appended by extend_deferred and bound by its producer's completion (D22, I17).
- No separate publication rule: keys and I4–I5b are unchanged (D23).
- Verify tickets and tickets with a proposal are never pipelined (superseded in v0.6: a continuation may follow them, D24).


Decided in v0.6:

- ZOS combined with speculative decoding for `δ = 1`: a continuation may follow a verify ticket or a ticket with `propose`. Its start is bounded by `lo` and the slack `s`; its input and drafts come from the producer's device outputs (D24).
- The plan lists the slots of every position a ticket can write; the executor selects the window, or computes the same slots from the plan's page mapping (E5).
- The reservation covers the longest outcome: `μ = (δ + 1)·λ`, plus `λ` with drafter classes. `begin_write` and `finish_write` never allocate (D18).
- A continuation's completion reports its accepted drafts (D22).
- `stop` commits a prefix of what the device accepted, orphans younger tickets and makes the lease terminal (D25, I18).
- Host-known drafts still need an empty queue, and `propose` still needs a drafter class.

Decided in v0.7:

- attach takes a hit limit from its caller, and probe answers where a request would resume without attaching; `attach(T)` is unchanged (D26).
- extend appends known tokens whether or not every earlier position is computed or ticketed; extend_deferred keeps its phase (D27).
- A scheduler that only reports which positions have executed, rather than issuing tickets, can still drive a coordinator: it credits those positions with issued-and-completed tickets, and releases a finished lease only once no in-flight step can read its pages. Neither needs a new primitive.

Decided in v0.8:

- A host tier: a second slab arena in host memory, owned by the coordinator, with one host class per paged class, the same unit size, and the same cache, capacity and reclaim rules. Host classes keep no leases and no frontier (D28, D29).
- Stores copy complete blocks of a lease into fresh host units and hold store references on their source pages until they complete, so release never waits for a store and the executor needs no ordering rule for stores. A store may fail, and then publishes nothing (D30).
- Loads are tickets: attach continues the device hit run with the host run, under the same hit limit, and the load ticket's completion credits and publishes it (D31).
- Host classes mirror only the paged classes. State snapshots in the host tier wait for state checkpoints.

Still open (to be decided in a later version):

- Tree drafts: a compaction step in the plan that moves the accepted path's KV into the slots of `[z, z+n)`, and how it interacts with I6 and I16.
- ZOS depth `δ >= 2`: stop and orphans (D25) cover the EOS case, but chains of continuations need the bounded start restated with several unknown acceptance counts, and the reservation grows by `λ` per extra step. Also open is whether to keep making a stopped lease terminal, or let it continue after the orphans drain.
- Device draft proposers with no KV in the arena (a device n-gram proposer), so that `propose` would not need `Cx ≠ ∅`.
- Allocate-then-return reservation instead of the static reach of D18, which would need `begin_write` to allocate and `finish_write` to free.
- Dynamic `λ` per lease or per step (vLLM's dynamic speculative length), versus the fixed reservation of D18.
- Whether to keep the reservation for leases that are not speculating, or let attach/extend take a per-call `λ_h <= λ`.
- Drafter classes with a different `B` from the target, and drafters with recurrent state.
- A second track for drafters that compute accepted KV in a separate forward (v0.4's draft track), if such a drafter is ever needed.
- State checkpoints at block boundaries during a verify (vLLM align mode's `boundary_state_idx`), once state hits exist.
- A Namespace field table that ties drafter classes to the target model they read hidden states from (E12).
- State checkpoints and joint prefix hits: checkpoint units keyed by `K(h,i)` at grain boundaries (DeepInfer stores state only at multiples of `KVSTORE_GRAIN`), the `on_hit` modes `restore` / `replay` / `empty`, the copy from checkpoint to live slot in the plan, and the joint `k*` rule.
- Guidance on slab size when the LCM of unit sizes is large: how much padding of `u_c` (kvspec `stride_align`) is acceptable.
- Several paged classes with different B (e.g. different lifetimes), and how hits align across them.
- Reclaim policy among reclaimable slabs (e.g. fewest keyed pages first), and whether an explicit trim operation that returns idle slabs is useful.
- The real Namespace field table (E6), its alignment with `Engine.store_identity()`, and how it encodes the kvspec plan of every class.
- Whether to share identity with `prefix_keys` in `shell/offload.py`. Sharing requires aligning the Tag, the namespace fields and `grain == B`; otherwise the contract should state explicitly that there are two separate schemes.
- Importing KV from outside this coordinator (adopt), which a disaggregated decode instance needs: its first step resumes past its local cached prefix, and the positions between are loaded from another instance or a shared store. A v0.8 load ticket whose sources lie outside the host tier is one candidate.
- State checkpoints in the host tier: host state classes, and joint device, host and state hits (with the state checkpoints above).
- Write-back: storing a cached page that no lease holds before a fresh allocation or a reclaim revokes it, so eviction from the device arena moves blocks to the host tier instead of losing them.
- Returning a stored page at release and making later writers of it wait for the store, as vLLM's offloading scheduler does, instead of store references: fewer device pages held, at the price of an ordering assumption on the executor.
- Failed loads: with no ticket queued behind it, a failed load could leave `c_h = k_d·B` and the loaded positions to recompute (vLLM's `kv_load_failure_policy = "recompute"`).
- Host hits at extend, so that a lease built by chunked attach keeps host hits past its first chunk.
- A host tier shared by several coordinators, and tiers beyond host memory (local disk, remote stores), with their own capacity and failure rules.
- Host eviction order beyond unkeyed-first (LRU, frequency-based admission), and whether begin_store should refresh the recency of the host copies it skips.
- Windowed lifetimes (sliding, tumbling, rings), several state versions per lease, and keys that cover a layer's token shift, which hybrid layouts need.
- Evicting a cached page on request: a reset of the cache must wait until no lease lives and no store is pending.
- Static caches inside the arena.

One more explicit boundary: the proofs this contract requires cover resources, provenance, addresses and protocol. Whether the GPU actually completed according to plan, and whether the KV and state values are numerically correct, need a separate executor contract. That boundary cannot be treated as proved just by assigning values to the ghosts `V_c` and `W_c`.
