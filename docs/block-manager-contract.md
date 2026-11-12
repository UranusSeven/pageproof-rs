# Block Manager Functional Contract v0.4 (draft)

Status: specification draft for review. v0.4 is **not yet implemented**. This repository implements and verifies v0.3 (`Coordinator`); `SPEC_NOTES.md` maps each v0.3 clause to its proof. With `λ = 0` and no draft class, v0.4 is meant to behave exactly like v0.3 (§9.1 obligation 18), so the v0.3 proofs are the base for v0.4.
Date: 2026-11-12 (v0.3: 2026-11-04; v0.2.1: 2026-11-03; v0.2: 2026-11-02; v0.1: 2026-11-01).
Reference code: nano-vLLM `bb823b3e06983d71485a8e1f23715ebd87d98ef8`: `block_manager.py`, `sequence.py`, `scheduler.py`; `prefix_keys` in `shell/offload.py` (the existing implementation of chained keys).
Layout reference: DeepInfer `0d0a93ff09c99af7a8521f230e16507bf3e00dda`: `deepinfer/kv_spec/kvspec.py` (`LogicalSpec`, `layout`, `PhysicalPlan`), `deepinfer/kv_spec/deepseek_v4.py`, `deepinfer/worker/kv_cache_views.py`.
Speculative-decoding reference: vLLM `9d61ade7f657833df27e43c4561455523c78c8fb`: `vllm/models/kimi_k3/nvidia/ops/recoverssm.py` (`_kda_recoverssm_verify_kernel`, `_commit_kda_state_kernel`, `_compact_conv_state_kernel`), `vllm/model_executor/layers/mamba/abstract.py` (`num_speculative_blocks`), `vllm/model_executor/layers/mamba/mamba_utils.py` (`append_kda_recoverssm_record`), `vllm/v1/worker/gpu/model_states/recoverssm.py` (`RecoverSSMState.commit_step`).

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

- **Slab arena.** Owns one contiguous device arena of `N` slabs of `S` bytes. It gives slabs to unit classes and reclaims them. It never moves or compacts a slab.
- **Unit-class managers.** Each class `c` cuts its slabs into units of `u_c` bytes. A paged class manages KV pages with the v0.2.1 semantics (page tables, prefix reuse, publication). A state class manages one fixed-size live state slot per lease. Paged classes belong to the target model (`Cp`) or to the draft model (`Cd`); state classes belong to the target model.
- **Coordinator.** Owns leases, inputs, the frontiers of both tracks, the draft reservation and tickets. It turns each public operation into an all-or-nothing change across the arena and every class.

This module is responsible for: slab ownership, physical unit allocation in every class, request page tables and state slots, whole-block prefix reuse in paged classes (keyed by chained digests), capacity growth including the draft reservation, the computed frontier of each track, unit protection during execution, committing accepted drafts, cache publication, and reference release.

Choosing draft tokens and deciding acceptance (rejection sampling) belong to the executor and the sampler. The block manager only records the drafts a verify ticket feeds and the acceptance count its completion reports. It never sees the tokens a draft ticket proposes.

The following semantics belong to other modules: choosing which requests to schedule each step, prefill/decode priority, token budget, EOS and max_tokens, the model's context limit, the byte layout inside a unit (the KV spec planner, e.g. DeepInfer's `kvspec.layout`), numerical correctness of the model, and GPU kernels and communication. The block manager does not modify this business state.

The module guarantees that the page tables, state slots and plans it outputs conform to this contract; the external executor must execute according to the plan. The correctness guarantees hold only given a fixed KV namespace, valid external completion events, and a correct executor.

One coordinator serves one model configuration and owns its arena. External code cannot bypass it to overwrite completed KV, write a live state slot, or reuse a unit. Several coordinators need separate arenas; sharing one arena across coordinators is out of scope.

### 1.1 Explicit non-goals and write assumption for v0.4

v0.4 supports speculative decoding with **linear draft chains**: a verify ticket feeds the last input token followed by up to `λ` drafts, and its completion accepts a prefix of them. Rejected drafts never enter `T_h`, so no truncate primitive is needed (D17). The following capabilities are still not in this draft's state machine. Callers must handle them separately and must not treat them as proved properties:

- Tree drafts (EAGLE-2, Medusa trees): the accepted path would sit in non-contiguous slots, which needs a KV compaction step in the plan.
- More than one state slot per lease for rollback (vLLM's default path, which keeps `num_speculative_tokens` extra state blocks per request, or kvspec `State.copies > 1`). v0.4 keeps exactly one slot and relies on the executor to rebuild the accepted state inside it (D19, E11). A state executor that cannot do that must run with `λ = 0`.
- Overlapped speculative scheduling: issuing the next draft or verify ticket of a lease before the previous acceptance count is known. A lease still has at most one pending ticket (I9).
- Zero-overhead scheduling (ZOS, microgravity `async_depth = 1`): issuing step t+1 of a lease before step t's sampled token reaches the host. It needs `Q >= 2` and a token that is not yet known; v0.5 adds both on top of this version's ticket queue ([pageproof-rs#2](https://github.com/UranusSeven/pageproof-rs/issues/2)).
- Draft-model state classes (a draft model with recurrent layers). Draft classes are paged only.
- State cache hits: there are no state checkpoints. A state slot is never keyed, published or shared, so a configuration with a state class never reuses a prefix (D13). kvspec's `on_hit` (`restore` / `replay` / `empty`) is ignored by v0.3 and v0.4.
- External KV import (adopt) for offload/store: the only way to advance `c_h` is the executor's completion event for a ticket. The `restore_prefix` path needs additional primitives.
- Static caches shared by all requests (kvspec `Static`, e.g. sink tokens): allocated by the caller outside the arena.
- Slab compaction, defragmentation, or moving a live unit.
- Multi-threaded concurrent calls: see the single-thread assumption E3 in §5.

This version **assumes writes always succeed** (E4): every issued ticket eventually completes successfully, with no failed completion, silent drop, or process termination. There is therefore no abort path, and no promise of progress under GPU faults (see C4). Rejecting drafts is not an abort: the completion is successful and reports how many drafts were accepted.

Until these primitives exist, an adapter must not claim to cover every feature of the existing scheduler (in particular tree `spec_decode` and `store`).

## 2. Design decisions adopted in this version

| ID | Draft default | Rationale or cost |
|---|---|---|
| D1 | Each coordinator fixes `N`, `S`, the class table, `B` and the KV namespace; there is no globally mutable block size | Multiple processes or instances do not depend on one implicit global value |
| D2 | attach reserves pages in every paged class for all current input tokens, and one slot in every state class | Keeps upstream's eager allocation; chunked prefill only advances the computed frontier |
| D3 | Reuse only a contiguous prefix of completed whole blocks; attach always leaves the last logical block for recomputation. With a state class present, `k* = 0` (D13) | Keeps upstream's convention for computing the first output; the last block is excluded even when the input length is an exact multiple of B |
| D4 | Cache hits are decided by chained 256-bit digest identity; the digest is also the index key | The key is a chain `H(parent, block)`, O(1) per block. Identity exactness rests on "SHA-256 is collision resistant" as an explicit probabilistic assumption (E8). No 64-bit practical hash, and no per-candidate exact comparison |
| D5 | Complete prefixes may be shared read-only; units being written must be exclusive; no COW in this version | Writes the boundary between sharing and writing into the spec. A live state slot is written in place but is always exclusive, so it is consistent with D5 |
| D6 | The core interface uses atomic `attach` / `extend` that check capacity and mutate together, across all classes | Avoids relying on possibly stale can_allocate/can_append results, and avoids a lease that got pages but no state slot |
| D7 | `begin_write` / `finish_write` make in-flight work explicit; in-flight requests cannot extend or release | Protects units through a metadata protocol; whether the GPU actually completed remains the executor's responsibility |
| D8 | Keep every published cache entry until its page is reused or its slab is reclaimed; lookup is complete and the hit prefix is the longest | An explicit cache-functionality promise, stronger than upstream's single-valued hash index. Slab reclaim happens only when free slabs do not suffice (D11) |
| D9 | Free-unit choice, eviction order, reclaimed-slab choice, and page choice among equal keys are not fixed; when a referenced hit candidate exists, it is preferred | Leaves room for optimization and ensures no spurious failure when resources suffice |
| D10 | Memory is one arena of `N` slabs of `S` bytes. Unit class `c` has unit size `u_c` with `u_c \| S` (A1, checked at create); `S = lcm_c u_c` is the smallest valid choice and the recommended default. Unit `g` of class `c` occupies bytes `[g·u_c, (g+1)·u_c)` | Each class sees the arena as a regular `[N·n_c, u_c]` array, so block-table kernels that compute `base + id·stride` work unchanged, and a slab has no tail waste. Cost: when the `u_c` share few factors the LCM is large; pad unit sizes (kvspec `stride_align`) to keep `S` reasonable |
| D11 | Slabs are acquired on demand, free slabs first. A slab whose units all have `ref = 0` is reclaimable even if some are keyed; reclaiming revokes those keys. Release never returns a slab; slabs never move | Keeps cached pages as long as possible and lets a class whose pages are all idle give memory to another class. Cost: reclaiming loses cache entries |
| D12 | Capacity is exact per class plus slabs (`Cap`, §3.5). Free units of one class never serve another class unless a whole slab is reclaimed | Keeps success-iff-capacity provable. Fragmentation is part of the contract: free bytes spread over partly used slabs do not count for another class |
| D13 | A state class holds exactly one exclusive live slot per lease, updated in place, never keyed, published or shared. There are no state cache hits in v0.3 or v0.4 | A page-prefix hit is useless without the matching recurrent state, so a configuration with a state class attaches at `c = 0`. Checkpoints and joint hits are deferred (§10) |
| D14 | The coordinator owns handles, tickets, `T_h`, the frontiers, the reach `ρ_h` and `Pending`. Classes form two **tracks**: the target track `Cp ∪ Cs` with frontier `c_h`, and the draft track `Cd` with frontier `e_h`. One frontier covers every class of its track; one ticket's plan covers every class of one track (v0.3: one frontier for all classes) | Multi-class operations are atomic, and frontiers cannot diverge inside a track. The two models compute the same positions in different tickets: after a verify accepts n drafts and the bonus token is appended, the target track needs only the bonus position while the draft track must recompute `n + 1` positions (D20), so a single frontier cannot describe both |
| D15 | All paged classes of a coordinator, target and draft, share `B` and one key chain per lease; each paged class has its own `Index` | The executor computes all classes of a track for the same positions, so they complete the same blocks together. Different `B` per paged class is deferred |
| D16 | Speculative decoding uses linear draft chains of at most `λ` tokens, with `λ >= 0` fixed at create. A **verify ticket** is a target ticket whose input reaches the end of `T_h`, followed by `k <= λ` drafts. Its completion reports the accepted count `n <= k` | The accepted drafts are a prefix of the written positions, so their KV is already in the right slots and no copy is needed. Trees are deferred (§1.1) |
| D17 | Drafts are not part of `T_h` until accepted. `finish_write` appends exactly the accepted drafts to `T_h` and sets `c_h` past them. Rejected drafts never enter `T_h`, any key, or any published page | No truncate primitive, and no published state can ever depend on a rejected token. The bonus token sampled after the last accepted position is appended by the caller with `extend`, as in v0.3 |
| D18 | Every lease reserves `λ` positions past the input: its page table in every paged class covers the reach `ρ_h = L_h + λ` set by the last attach or extend. `begin_write`, `begin_draft` and `finish_write` never allocate, and a rejection never frees | A verify never fails for capacity and a completion never fails, which keeps E4. Cost: at most `ceil(λ/B)` extra pages per paged class per lease, held even when the lease is not speculating; with `B = 64` and `λ <= 64` that is one page |
| D19 | A state class keeps exactly one slot per lease when `λ > 0`. A verify ticket's plan names that slot, and the executor leaves in it the state after the accepted prefix. How it does so (checkpoint plus per-token records, recomputation, or extra copies inside the unit) is the executor's business (E11) | Matches vLLM's KDA RecoverSSM path for Kimi K3: verify reads the checkpoint `S_0` without writing it back and saves per-token records; commit rebuilds `S_n` in closed form from `S_0` and the first `n` records. Records cost about `3·head_dim` elements per head per token against `head_dim²` for a full state. The records and the widened conv window live inside the state unit, so `u_c` grows with `λ`, but the slot count stays at one |
| D20 | Draft paged classes `Cd` (possibly empty) hold the draft model's KV in the same arena. A **draft ticket** (`begin_draft`) writes the draft track for input positions `[e_h, z)` and, when it proposes `k >= 1` tokens, for `k - 1` tentative positions after `z = L_h`. Its completion advances `e_h` to `z` only. Draft KV at tentative positions is never credited, even when the verify accepts those tokens: the next draft ticket recomputes them as input | Draft and target pages share slabs, `Cap` and reclaim, so neither model needs a static split. Not crediting tentative draft KV is required for EAGLE-style drafters, whose KV at a position depends on whether the input hidden state came from the target or from the drafter; vLLM's proposer re-feeds the accepted tokens with target hidden states for the same reason. Cost: up to `λ` recomputed draft positions per step. The block manager never sees the proposed tokens |

D1–D20 are proposed semantics, not claims that upstream already satisfies them. D4, D6–D8, D10–D14 and D16–D20 in particular require changes to the implementation and interface; this draft does not promise function-by-function compatibility with the old API.

## 3. Abstract state

### 3.1 Fixed configuration

- `N >= 1`: number of slabs, `SlabId = {0,...,N-1}`.
- `S >= 1`: bytes per slab.
- `Classes = Cp ∪ Cd ∪ Cs`: a finite, disjoint, ordered set of unit classes. `Cp` (target paged classes) is non-empty; `Cd` (draft paged classes) and `Cs` (state classes) may be empty. Write `Cpd = Cp ∪ Cd` for all paged classes. The **target track** is `Cp ∪ Cs`; the **draft track** is `Cd` (D14).
- For each class `c`: unit size `u_c >= 1` bytes, with **base assumption A1: `u_c | S`**. Let `n_c = S / u_c >= 1` (units per slab). The unit ids of class `c` are `{0,...,N·n_c - 1}`; unit `g` lies in slab `slab_c(g) = floor(g / n_c)`, and `units_c(s) = [s·n_c, (s+1)·n_c)`.
- `B >= 1`: token slots per unit of every paged class, target and draft (D15).
- `λ >= 0`: the maximum number of draft tokens per ticket (D16). `Cd ≠ ∅` requires `λ >= 1`. With `λ = 0` and `Cd = ∅` the configuration is a v0.3 configuration. For a state class, `u_c` must already include whatever the executor needs to rebuild the state after a partial acceptance of up to `λ` drafts (per-token records, the widened conv window); this is part of E11, not checked by create.
- `Namespace`: the configuration identity that decides cache reusability, an opaque byte string. The final field table should cover model and weight version, adapters, positional encoding/scaling, attention semantics (including sliding window), B, and, for every class, its kind, `u_c` and in-unit layout (the kvspec `LogicalSpec` and `PhysicalPlan` regions). It should align with `Engine.store_identity()`. v0.4 still uses a dummy (an implementation may pass a fixed string such as `"dummy-v0.4"`); when `Cd ≠ ∅` it must also cover the draft model (E12). Completeness remains the caller's obligation (E6); the field table is deferred.
- `Token`: the type of valid token ids; sequences are finite and 0-indexed.

**Addressing.** Unit `g` of class `c` occupies arena bytes `[g·u_c, (g+1)·u_c)`. By A1 this range lies inside slab `slab_c(g)`'s bytes `[s·S, (s+1)·S)`, so a class's units are exactly the arena viewed as a `[N·n_c, u_c]` array. Inside a unit, the kvspec plan decides where each layer's region lies. For a paged class, `u_c` is the plan's paged-pool stride for `block_tokens = B`; for a state class it is the state-pool stride. Arena base alignment is E9.

**Capacity of a request size.** Let `Fits(m) ⇔ Σ_{c ∈ Cpd} ceil(m / n_c) + |Cs| <= N`. This is whether a lease with `m` blocks in every paged class fits in an otherwise empty arena. A lease's block count includes its draft reservation (D18, §3.3).

The abstract spec uses mathematical integers. A concrete implementation must prove that machine-integer arithmetic on slab ids, unit ids, lengths, reaches `L + λ`, counts and byte addresses does not overflow (in particular `N·S` bytes and `N·n_c·B` token slots), and must reject unrepresentable configurations at construction. Other limits, such as CUDA's current requirement that B be a multiple of some value and its int32 slot limit (now on `N·n_c·B` per paged class), must be added explicitly by the corresponding implementation or adapter, never silently ignored.

### 3.2 Mutable state

| Symbol | Meaning |
|---|---|
| `owner[s]` | The class that owns slab s, or `Free` |
| `FS` | `{s | owner[s] = Free}`, the free slabs |
| `U_c` | Derived: `{g | owner[slab_c(g)] = c}`, the units class c currently owns |
| `Req[h]` | An attached lease: the input sequence `T_h` (never modified in place; it only grows, by `extend` and by accepted drafts), the target frontier `c_h`, the draft frontier `e_h`, the reach `ρ_h`, for each `c ∈ Cpd` a page table `M_h^c`, for each `c ∈ Cs` a live slot `σ_h^c`, and the queue `Q_h` of its pending tickets in issue order, with `|Q_h| <= Q` and `Q = 1` in v0.4 |
| `p_h` | Derived: the planned frontier of the target track, the `z` of the newest target ticket in `Q_h`, or `c_h` when `Q_h` holds none. With `Q = 1`, a target ticket is issued only when `Q_h` is empty, so it starts at `p_h = c_h` |
| `ρ_h` | The reach of lease h: the number of token positions its page tables cover. Set to `L_h + λ` by attach and extend, unchanged by every other method (D18) |
| `e_h` | Draft frontier: the length of the contiguous prefix whose draft-model KV is valid in every `c ∈ Cd`. When `Cd = ∅` it is not stored; read `e_h` as `c_h` wherever it appears |
| `ref_c[g]` | How many active leases reference unit g of class c |
| `F_c` | Units of class c that are owned and referenced by no lease; for paged classes this includes free cache pages that still hold reusable data |
| `key_c[g]` | Paged classes only: page g's reusable cache identity (a chained 256-bit digest), or None |
| `Index_c[K]` | Paged classes only: all candidate pages of class c whose published key is K |
| `Pending[t]` | A submitted but not yet completed computation: the lease, its track, original frontier `a`, input end `z`, the draft part, and execution plan `plan` (§3.4) |
| `V_c` | Paged classes (target and draft): ghost KV-provenance marker; records the Namespace and full causal token prefix of each token slot of class c. The prefix may run past `T_h` for a slot written at a tentative position |
| `W_c` | State classes: ghost marker; `W_c[g]` is `(Namespace, τ)` when unit g holds the state after prefix τ, or `⊥` |
| `den` | Ghost used by the proof: a partial function from digest to `(Namespace, full causal prefix)`; it gives chained keys their meaning |

The domain of `den` is exactly the chain outputs `{Seed(ns)} ∪ {K(h,i)}`. It is injective in the ideal model, and E8 covers this for the concrete instance. It is not part of the executable state.

Request handles and execution tickets use distinct types that cannot be confused, and are bound to the coordinator and to their generation. An invalidated handle or ticket can never become valid again on a later object. If a concrete implementation's counter space is exhausted, it must safely reject new operations and never wrap around and reuse ids.

A request in this draft means a block-manager lease, not the scheduler's WAITING/RUNNING/FINISHED state. The scheduler still manages its business requests; releasing a lease does not delete the user request or its output.

### 3.3 Semantic conventions

Let `L_h = |T_h|` and `m_h = ceil(ρ_h/B)`, the number of blocks the page tables cover. In v0.3, `ρ_h = L_h`; in v0.4, `L_h <= ρ_h <= L_h + λ` (I16).

Page-table entry `M_h^c[i]` is the page of logical block i in paged class c. The token-slot index of position j in class c is:

\[
slot_c(h,j)=M^c_h[\lfloor j/B\rfloor]\cdot B+(j\bmod B).
\]

It is defined for `0 <= j < ρ_h` and lies in `[0, N·n_c·B)`. The bytes a slot occupies follow from the unit address `M_h^c[floor(j/B)]·u_c` and the kvspec regions; this contract fixes only the unit.

`c_h` is the length of the contiguous computed prefix of the target track, shared by every class in `Cp ∪ Cs` (D14): positions `[0,c_h)` have valid KV in every target paged class, `[c_h,L_h)` are not all done, and every live state slot of h holds the state after `T_h[0:c_h]` (I15). `e_h` is the same for the draft track: positions `[0,e_h)` have valid draft-model KV in every `c ∈ Cd`. Both satisfy `c_h, e_h <= L_h`. Reserved capacity does not mean the KV is valid, and positions in `[L_h, ρ_h)` never count as computed in either track.

**Draft chains (D16).** A ticket of either track covers an **input interval** `[a,z)` with `0 < z - a` and `z <= L_h`, and a **draft count** `k` with `0 <= k <= λ`. `k > 0` is allowed only when `z = L_h`, so drafts always follow the whole input.

- A **target ticket** (`begin_write`) has `a = p_h` (which is `c_h` whenever `Q_h` is empty, always the case at issue in v0.4) and carries draft tokens `D` with `|D| = k`, chosen by the caller. It feeds `T_h[a:z] ++ D` at positions `[a, z+k)`, so its **write end** is `w = z + k`. With `k > 0` it is a **verify ticket**: the model's outputs at positions `[z-1, z+k)` are what the sampler checks the drafts against.
- A **draft ticket** (`begin_draft`, only when `Cd ≠ ∅`) has `a = e_h`. It feeds `T_h[a:z]` and, when `k > 0`, generates `k` proposals autoregressively, feeding the first `k - 1` of them at positions `[z, z+k-1)`. Its write end is `w = z + max(k-1, 0)`. The block manager does not see the proposals.
- Every ticket has `w <= ρ_h`. Positions `[L_h, w)` are **tentative**: their slots are written, but no frontier is credited for them by the ticket that wrote them.

**Acceptance (D17).** The completion of a target ticket reports `n` with `0 <= n <= k`, the number of leading drafts the sampler accepted. Committing it sets `T'_h = T_h ++ D[0:n]` and `c'_h = z + n`. The KV the ticket wrote at positions `[z, z+n)` is then KV of `T'_h`, so it is credited. Slots of the rejected positions `[z+n, z+k)` keep whatever the executor wrote and are rewritten by later tickets. The bonus token the sampler draws at position `z + n` (the model's output after the last accepted draft) is not part of the ticket; the caller appends it with `extend`. A draft ticket's completion always reports `n = 0` and sets `e'_h = z`.

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

`K(h,i)` is defined only for complete blocks, `(i+1)B <= L_h`; an incomplete tail block has no key and is never published. Tokens at tentative positions are not in `T_h`, so no key is ever computed over a draft before it is accepted, and never over a rejected draft. A key means the full causal prefix `(Namespace, T_h[0:(i+1)B])`, given by the ghost `den`; the chained construction is only its O(1) representation. Any difference in an earlier block must change every later key. The chain guarantees this; "current-block tokens only", "token hash only" or "same length" are all insufficient.

In the ideal hash model (`H` injective) the chain lemma holds:

\[
K(h,i)=K(h',i') \iff ns=ns' \land i=i' \land T_h[0:(i+1)B]=T_h'[0:(i+1)B].
\]

For the concrete instance (SHA-256) the equivalence holds with probability `>= 1 - \epsilon`, `\epsilon <= Q^2/2^{257} + Q/2^{256}`, where `Q` is the number of key generations and comparisons during the deployment (E8). `den` is injective on chain outputs (ideal model), and E8 likewise covers the concrete instance; hence `den(K(h,i)) = (Namespace, T_h[0:(i+1)B])` is the meaning of a key.

A key lives as long as its page stays published: the digest is stored on the page, and the `Index_c` entry is removed when the key is revoked, either because the page is chosen as a new writable page or because its slab is reclaimed. There is no intern table, ancestor chain, or GC. A page that is released but not reused keeps its key (C5), so total metadata is O(owned units) digests (made precise by I11). The chain head (the key of the last published complete block, or `Seed(ns)`) lets `finish_write` compute the keys of new blocks incrementally; it is an implementation detail.

In v0.3 and v0.4, keys are still computed and published when `Cs ≠ ∅`, even though no lease of such a configuration can hit them (D13). This keeps the paged-class semantics identical to v0.2.1 and prepares for state checkpoints. Draft classes use the same chain: block i of a draft class is published under `K(h,i)` in `Index_c` once `(i+1)B <= e_h`.

### 3.4 Representation of Index and Pending

**Index.** For each `c ∈ Cpd`, `Index_c : Map<Key, Set<UnitId>>`, with `Index_c[K] = {g | key_c[g] = K}` (I8).
- It is the inverse relation of `key_c` and covers only published pages. `F_c` contains both published pages (still findable through `Index_c`) and unpublished ones; `key_c[g]` tells them apart.
- One key may map to several pages of the class. At each hit position, `attach` prefers a candidate with `ref > 0`; otherwise it reactivates a candidate with `ref = 0`.
- Entries are removed when `key_c` is revoked (C1/C2 fresh allocation, slab reclaim, I7). `release` does not remove entries (C5).
- The total number of entries is ≤ `|U_c|`, and a key whose candidate set becomes empty keeps no stored entry (I11).

**Pending.** `Pending : Map<TicketId, PendingRec>`. `dom(Pending)` corresponds both ways to the queues `Q_h` (I9):

```
PendingRec = {
  lease  : Handle,          // h
  track  : Target | Draft,
  a      : Nat,             // p_h (Target) or e_h (Draft) when the ticket was issued
  z      : Nat,             // end of the input interval, z <= L_h
  k      : Nat,             // draft count, k <= λ; k > 0 only if z = L_h
  drafts : Seq<Token>,      // Target: D with |D| = k. Draft: empty
  plan   : ExecutionPlan,   // the immutable plan returned by begin_write / begin_draft
}
```

Let `w` be the write end of §3.3. A **target plan** contains at least `ticket`, `h`, `B`, `input_ids = T_h[a:z] ++ D`, `positions = [a..w-1]`, `num_drafts = k`; for each `c ∈ Cp`, `write_slots_c = [slot_c(h,j) | j in [a,w)]` and the page mapping of class c for `[0,w)`; for each `c ∈ Cs`, the live slot `σ_h^c` and `init = (a = 0)`. A **draft plan** contains `ticket`, `h`, `B`, `input_ids = T_h[a:z]`, `positions = [a..z-1]`, `num_proposals = k`; for each `c ∈ Cd`, `write_slots_c = [slot_c(h,j) | j in [a,w)]` and the page mapping of class c for `[0,w)`. A plan names only the classes of its track.

**Ticket queue.** `Q_h` lists the pending tickets of lease h in issue order. `Q >= 1` is the largest queue length; v0.4 fixes `Q = 1`, so `Q_h` is empty or holds one ticket, exactly v0.3's optional pending ticket. The rules below are stated for a queue so that a later version can raise `Q` without restating them (v0.5 does, for zero-overhead scheduling).

Calls are single-threaded (E3). While a ticket is live, the lease may only grow: `T_h` may only be appended to, every `M_h^c` may only gain entries at its end, `ρ_h` may not decrease, and every `σ_h^c` is unchanged. In v0.4, `extend` and `release` are forbidden while `Q_h` is non-empty (I9), so with `Q = 1` nothing about the lease changes until the ticket completes. A plan's inputs and page mapping stay valid because they lie in the prefix that cannot change, so no version number is needed. Derived invariant, where `T_h^t`, `M_h^{c,t}` and `ρ_h^t` are the values when t was issued:

```
t ∈ Q_h  ⇔  t ∈ dom(Pending) ∧ Pending[t].lease = h
t ∈ dom(Pending)  ⇒  T_h^t ⊑ T_h  ∧  M_h^{c,t} ⊑ M_h^c  ∧  ρ_h^t <= ρ_h  ∧  σ_h^c unchanged since t was issued
t is the oldest target ticket in Q_h  ⇒  Pending[t].a = c_h
t is the oldest draft ticket in Q_h   ⇒  Pending[t].a = e_h
t is a later target ticket in Q_h     ⇒  Pending[t].a = Pending[t'].z for the target ticket t' issued just before it
                                         (never true while Q = 1)
```

`⊑` is "is a prefix of". With `Q = 1` every pending ticket is the oldest of its track, the prefix relations are equalities, and these lines say exactly what v0.3 says: `a` equals the frontier, and `T_h`, `ρ_h`, both frontiers, `M_h^c` and `σ_h^c` are unchanged.

`finish_write` accepts only `t ∈ dom(Pending)` with a matching binding and an acceptance count `n <= Pending[t].k` (with `n = 0` for a draft ticket). Atomically, for a target ticket it removes the entry, removes t from `Q_h`, appends `D[0:n]` to `T_h`, sets `c_h = z + n`, updates the ghosts `V_c` and `W_c`, publishes the newly completed blocks in every target paged class, and updates their `Index_c`. For a draft ticket it does the same with `e_h = z`, the draft classes, and no change to `T_h`. A completion event is consumed only once.

### 3.5 Slab plan and the capacity predicate

`attach` and `extend` are the only operations that change slab ownership. Each computes a **demand** `d_c >= 0` per class (the number of units of class c it will take from `F_c`, counting reactivated cache hits) and a set of **protected slabs** `Prot` that it must not reclaim. Then, from the pre-call state:

\[
\begin{aligned}
need_c &= \lceil \max(0,\ d_c - |F_c|) / n_c \rceil\\
R_c &= \{ s \mid owner[s]=c \land s \notin Prot \land \forall g \in units_c(s):\ ref_c[g] = 0 \}\\
give_c &= \begin{cases} \min(|R_c|,\ \lfloor (|F_c| - d_c)/n_c \rfloor) & \text{if } |F_c| \ge d_c\\ 0 & \text{otherwise}\end{cases}\\
Cap(d, Prot) &\iff \textstyle\sum_c need_c \le |FS| + \sum_c give_c.
\end{aligned}
\]

`R_c` is the set of reclaimable slabs of class c. Keyed pages do not block reclaim (D11); referenced units do. A pending ticket's units are referenced by its lease (I2, I9), so in-flight units are never reclaimed. `give_c` is how many whole slabs class c can give up while keeping `d_c` free units outside them.

**Slab plan.** On success the operation performs exactly this, before allocating units:

1. Each class c receives exactly `need_c` slabs; no other class receives one.
2. Slabs come from `FS` first. Only if `|FS| < Σ need_c`, exactly `Σ need_c - |FS|` slabs are reclaimed, each from some `R_{c'}` with class `c'` giving up at most `give_{c'}` slabs. Which donors and slabs are chosen is not fixed (D9).
3. Reclaiming slab s from class `c'` revokes `key_{c'}[g]` for every `g ∈ units_{c'}(s)`, removes those units from `Index_{c'}` and `F_{c'}`, and sets `W_{c'}[g] = ⊥` and `V_{c'}` of their token slots to unconstrained. Then `owner[s]` changes to the receiving class. The units of a received slab enter `F_c` with `ref_c = 0`, `key_c = None` (paged) and `W_c = ⊥` (state).
4. Units are then allocated from `F_c` as the operation specifies. A class never takes units from a slab given up in the same call.

A class with a deficit (`|F_c| < d_c`) never gives up a slab: giving up `n_c` free units would raise `need_c` by exactly one, a net loss. So `Cap` is exactly "a slab plan following rules 1–4 exists" (§9.1 obligation 11).

**Lemma (refines v0.2.1 capacity).** With one class c and `Prot = ∅`, `Cap(d, ∅) ⇔ d <= |F_c| + n_c·|FS|`. That equals v0.2.1's `|F| >= d` when units in free slabs are counted as unkeyed free pages.

**Draft reservation (D18).** `Cap`, `need_c`, `R_c` and `give_c` are unchanged; they range over every class, including `Cd`. Only the demands change: attach and extend size every paged class's page table for the new reach `ρ' = L' + λ`, where `L'` is the input length after the call, so a paged class's demand counts `ceil(ρ'/B)` blocks instead of `ceil(L'/B)` (C1, C2). No other method changes slab ownership or any `F_c`. In particular `begin_write`, `begin_draft` and `finish_write` never allocate, whatever the acceptance count. With `λ = 0` every demand equals its v0.3 value.

## 4. Global invariant Valid(S)

The following properties hold after construction and on return from every public method. Each invariant stated for pages, `ref`, `key`, `F`, `Index`, `V` holds separately in every paged class `c ∈ Cpd`, with `PageId` replaced by `U_c`. Where an invariant names "the frontier of c", it means `c_h` for `c ∈ Cp ∪ Cs` and `e_h` for `c ∈ Cd`; write `f_h^c` for it.

**I1 Unit domain and page tables.** All unit ids of class c are in `U_c`. Each active lease's page table in every paged class has no duplicates; `L_h >= 1`, `Fits(m_h)` with `m_h = ceil(ρ_h/B)`, and `|M_h^c| = m_h` for every `c ∈ Cpd`.

**I2 Exact references.** For every class c and unit g:

\[
ref_c[g]=|\{h\in dom(Req): g\in set(M^c_h)\}| \quad (c \in Cpd), \qquad ref_c[g]=|\{h\in dom(Req): \sigma^c_h = g\}| \quad (c \in Cs).
\]

Negative counts, missing references and extra references are all forbidden. The count is the number of lease references. A pending ticket protects its units because its lease cannot be released, not by inflating this count.

**I3 Exact free set.** `g ∈ F_c ⇔ g ∈ U_c ∧ ref_c[g] = 0`. A referenced unit is never reallocated as a writable unit. Free only means reclaimable; it must not be read as "the data is gone" or "zeroed".

**I4 Valid frontiers.** `0 <= c_h <= L_h` and `0 <= e_h <= L_h`. For every `c ∈ Cpd` and `j < f_h^c`, `V_c[slot_c(h,j)]` corresponds to `Namespace, T_h[0:j+1]`. No claim is made about slots at positions `>= f_h^c`, in particular tentative positions and rejected drafts. This is a KV provenance property; floating-point numerical correctness is the executor's external spec.

**I5 Published cache is genuine.** When `key_c[g] != None`, there exist `q >= 1` and a prefix `τ` of length `qB` such that `den(key_c[g]) = (ns, τ)` and page g of class c holds valid KV for the last complete block of `τ`. A key identifies one definite logical block position and context.

For any active lease h that references a published page g of class c, if `M_h^c[i]=g` then also `key_c[g]=K(h,i)` and `f_h^c >= (i+1)B`. This applies to pages with ref=1 too, so a request never writes over one of its own published pages as if it were an uncomputed tail.

**I5b Complete implies published.** For every active lease h, `c ∈ Cpd` and `i < m_h`, if `(i+1)B <= f_h^c` then `key_c[M_h^c[i]] = K(h,i)`. I5 only gives "published ⇒ correct"; I5b gives the converse. This makes D8's "lookup is complete" a property of the state, rather than a conclusion that needs replaying history.

**I6 Shared means read-only.** If `ref_c[g]>1`, then `c ∈ Cpd` and g has a published key. For every referencing lease h, that key equals `K(h,i)` for g's position i in h, and `f_h^c >= (i+1)B`. So no referencing lease ever writes to g as if it were an uncomputed tail.

**I7 No overwrite after publication.** A page with a non-empty key must not be overwritten in place by any write plan. A new round of writes may start only once `ref_c[g]=0` and the key and index entry have been revoked, either because the page was chosen as a new page or because its slab was reclaimed and given out again.

**I8 Index consistent both ways.** `Index_c[K] = {g | key_c[g]=K}`. Invalidated pages are not found; published candidates whose page was not reused and whose slab was not reclaimed are found. Under E8, equal digests are treated as equal prefixes, so candidates in `Index_c[K]` need no token-by-token comparison. A key whose candidate set is empty has no stored entry in the concrete representation (I11).

**I9 In-flight protection.** Each active lease has a queue `Q_h` of at most `Q` pending tickets (`Q = 1` in v0.4), and the queues and the Pending table correspond both ways.
- A ticket is bound to a real lease, a track, an input snapshot, the interval `[a,z)` and the draft count `k`, with `0 < z-a`, `z <= L_h`, `k <= λ`, `k > 0 ⇒ z = L_h`, and write end `w <= ρ_h`. A target ticket starts where the target track's earlier tickets end: `a = c_h` for the oldest target ticket in `Q_h`, and `a` = the previous target ticket's `z` for a later one. A draft ticket has `a = e_h`. A draft ticket exists only when `Cd ≠ ∅`.
- The units it needs, in every class of its track, stay referenced until completion.
- Every pending write plan lies within the valid slot range of each class of its track and inside the lease's page tables (`w <= ρ_h`), and its write pages are exclusive and unpublished; its state slots are the lease's own live slots.
- Tickets of different leases have disjoint write slots in every class and different state slots. Tickets of one lease and one track write disjoint, consecutive intervals in issue order and share that lease's state slots; the executor applies them in issue order (with `Q = 1` there is never more than one).
- While a ticket is live, the lease only grows (`T_h`, every `M_h^c` and `ρ_h` only extend, every `σ_h^c` is unchanged), and `a` is as stated above (derived invariant, see §3.4). With `Q = 1` and v0.4's methods, nothing about the lease changes until the ticket completes.

**I10 Immutable configuration.** N, S, the class table (`Cp`, `Cd`, `Cs`, every `u_c`), B, `λ` and Namespace do not change during the coordinator's lifetime; all addresses in execution plans are computed with this instance's values.

**I11 Bounded metadata.** The element count of every metadata container is bounded by the fixed configuration, independent of how many operations have been performed:

- `|dom(Req)| <= N · min_c n_c`;
- `|dom(Pending)| <= Q · |dom(Req)|` (at most `Q` tickets per lease, I9; `Q = 1` in v0.4);
- per paged class, the number of stored `Index_c` entries, however the representation groups keys, is at most `|{g | key_c[g] != None}| <= |U_c| <= N·n_c`; an entry exists only for a non-empty candidate set;
- for every lease and `c ∈ Cpd`, `|M_h^c| <= N·n_c`, and `Fits(m_h)` bounds `ρ_h`, hence `L_h <= ρ_h`;
- the drafts stored in a pending ticket number at most `λ`;
- per-unit state (`ref_c`, `key_c`, membership in `F_c`) has exactly `N·n_c` slots per class, and `owner` has exactly N.

**I11a Distinct last pages and slots** (supporting fact). For distinct active leases `h != h'` and every `c ∈ Cpd`, `M_h^c[m_h-1] != M_{h'}^c[m_{h'}-1]`. A lease's last page is always a fresh page taken from `F_c`: attach takes it fresh because `k* <= ceil(L_h/B)-1 <= m_h-1`, and extend either adds fresh pages or keeps the old last page. Page-table entries never change afterwards. For every `c ∈ Cs`, `σ_h^c != σ_{h'}^c` by I2 and I14. So `|dom(Req)| <= |U_c| <= N·n_c` for every class.

I11 bounds element counts. Total token storage is therefore at most `|dom(Req)| · max{L | Fits(ceil(L/B))}` tokens plus `λ` drafts per pending ticket, because each lease keeps its full input. Whether byte-level memory is bounded additionally depends on the runtime's containers using memory proportional to their peak element count, which is outside the proof.

**I12 Slab ownership.** `owner : SlabId -> Classes ∪ {Free}` is total, and `FS = {s | owner[s] = Free}`. Every slab has exactly one owner or is free.

**I13 Confinement.** For every class c and unit `g ∉ U_c`: `ref_c[g] = 0`, `g ∉ F_c`, and (paged) `key_c[g] = None` and g is in no `Index_c` entry, or (state) `W_c[g] = ⊥`. Every page-table entry, live slot, key, Index candidate and pending write of class c lies in `U_c`.

**I14 Live state slots.** For every `c ∈ Cs` and active lease h, `σ_h^c ∈ U_c` and `ref_c[σ_h^c] = 1`. Distinct leases have distinct slots. A state class has no keys and no Index.

**I15 State provenance.** For every `c ∈ Cs` and active lease h: if `c_h > 0` then `W_c[σ_h^c] = (Namespace, T_h[0:c_h])`. If `c_h = 0`, no claim is made about the slot's contents; the next plan carries `init` (C3, E10). With `λ > 0` this still names one slot per lease: after a verify ticket the slot holds the state after the accepted prefix, never after a rejected draft (D19, E11). Per-token records and other scratch bytes that the executor keeps inside the unit carry no provenance.

**I16 Draft reservation.** For every active lease h, `L_h <= ρ_h <= L_h + λ`, and `c_h < L_h ⇒ ρ_h = L_h + λ`. (attach and extend set `ρ_h = L_h + λ`; the only other change to `L_h` is a verify commit, which leaves `c_h = L_h`.) So a target ticket with `k <= λ` drafts always fits its reservation. Every page that covers a position `j >= L_h` is exclusive (`ref_c = 1`) and unpublished in every `c ∈ Cpd`. With `λ = 0`, `ρ_h = L_h` and I16 is trivial.

Exclusivity of the reserved pages follows from I5 and I6: a published or shared page at block i of h has `(i+1)B <= f_h^c <= L_h`, so it covers no position `>= L_h`. I16 states it so that no ticket needs to check it. Accepted drafts consume the reservation: after a verify accepts n drafts, `ρ_h - L_h` drops by n, and the next attach or extend restores it to `λ`.

**Arena disjointness** (theorem, from A1 and I12). For any two distinct pairs `(c,g) ≠ (c',g')` with `g ∈ U_c` and `g' ∈ U_{c'}`, the byte ranges `[g·u_c, (g+1)·u_c)` and `[g'·u_{c'}, (g'+1)·u_{c'})` are disjoint. Within one class, distinct ids are disjoint. Across classes, the units lie in different slabs (I12) and each unit lies inside its own slab (A1). Together with I6, I9, I14 and I16, this gives: no planned write, including a write at a tentative position, touches a published page, a shared page, another lease's state slot, another lease's reservation, or another class's unit. In particular draft-class writes never alias target-class KV.

## 5. General method conventions

A real implementation must encapsulate its internal state: external code may update it only through the verified methods. `Valid(S)` must not be treated as a condition that an arbitrary external Python caller will always respect voluntarily.

Every method must satisfy:

1. If the entry state is Valid, the state on normal return is also Valid.
2. The method terminates on every finite valid input, with no out-of-bounds access, counter overflow, or unspecified state change.
3. Declared error results are strongly failure-atomic: `S'=S`, including slab ownership, every class's page tables, slots, reference counts and index, frontiers, pending tickets, and id-allocation state.
4. The inputs, page tables, state slots, frontiers and pending tickets of uninvolved leases stay unchanged; existing KV referenced by multiple leases and the live state of other leases must not change. The only changes to units not referenced by the calling lease are the slab-plan steps of §3.5.
5. Externally observable outputs satisfy each method's functional postcondition, not merely "the state is still valid".

These failure-atomicity requirements cover the specified input, capacity and phase errors. Process termination, runtime OOM and hardware faults are outside this version's state-machine promises.

This draft assumes methods are called sequentially on one thread (or serialized by the caller), and claims no multi-threaded linearizability (E3). Computing a chained key is a pure function and modifies no state. `owner` and every `Index_c` change only on successful methods. So the strong failure atomicity of item 3 covers slab ownership, page tables, slots, references, every `Index_c` and id-allocation state, with no separate key-store state to cover.

## 6. API contracts

### C0. create(N, S, classes, B, λ, Namespace) -> Result<Coordinator>

`classes` is an ordered list of `(kind ∈ {Paged, DraftPaged, State}, u_c)`. `Paged` classes form `Cp`, `DraftPaged` classes form `Cd`, `State` classes form `Cs`.

**Success:** the configuration is fixed; every slab is free; Req, Pending and every `Index_c` are empty; every unit of every class has ref=0, key=None and `W = ⊥`; every `U_c` and `F_c` is empty; Valid holds.

**Failure:** return an explicit ConfigError and produce no usable coordinator if `N`, `S` or `B` is non-positive; there is no target paged class; some `u_c` is non-positive; **some `u_c` does not divide `S` (A1)**; `Cd ≠ ∅` and `λ = 0`; `¬Fits(ceil((1+λ)/B))`, so that not even a one-token lease could attach; or the configuration cannot be safely represented in machine integers (including `N·S`, `N·n_c·B` and `L + λ` for every `L` with `Fits(ceil(L/B))`).

With `λ = 0` and `Cd = ∅`, C0–C7 below reduce to their v0.3 text (obligation 18).

### C1. attach(T) -> Result<(Handle, cached_tokens, LeaseView)>

Purpose: handle a request for the first time, or re-acquire resources from the retained full input after a request was preempted and released.

**Valid input:** T is a non-empty sequence of valid tokens with `Fits(ceil((L+λ)/B))`, and its Namespace is this coordinator's fixed configuration. An input that is too large, including its draft reservation, returns RequestTooLarge; an invalid or empty sequence returns InvalidArgument.

**Exact definition of prefix and capacity:** let `m=ceil(L/B)` be the input's block count and `m^+ = ceil((L+λ)/B)` the reserved block count (D18). Computed from the pre-call state:

\[
k^*=\begin{cases}0 & \text{if } Cs \ne \varnothing,\\ \max\{k\in[0,m-1]\mid\forall c\in Cpd,\ \forall i<k,\ Index_c[K(h,i)]\ne\varnothing\} & \text{otherwise.}\end{cases}
\]

`K(h,i)` is computed incrementally along the §3.3 chain, starting from `Seed(ns)`. The tail block has no key, so the upper bound `m-1` agrees with "the last block is recomputed". The first case is D13: there are no state checkpoints, so no prefix can be resumed. (A future version replaces it with "and a state checkpoint at `kB` exists".) The hit is joint over target and draft classes, so both frontiers start at `k*B`: a prefix cached for the target model but not the draft model is not a hit.

For `c ∈ Cpd`, let `r_c` be the number of the k* prefix positions that have at least one candidate in `Index_c` with `ref>0`. Demand and protected slabs:

\[
\begin{aligned}
d_c &= m^+-r_c \quad (c\in Cpd), \qquad d_c = 1 \quad (c \in Cs),\\
Prot &= \{ slab_c(g) \mid c\in Cpd,\ i<k^*,\ \text{no candidate of } Index_c[K(h,i)] \text{ has } ref>0,\ g\in Index_c[K(h,i)] \}.
\end{aligned}
\]

`Prot` holds the slabs of the free candidates this call may reactivate. It depends only on the pre-call state and T, so a call never reclaims a cache entry it is about to hit. With `Cs ≠ ∅`, `k* = 0` and `Prot = ∅`.

**Success if and only if:** for valid input with the handle space not exhausted, attach must succeed when `Cap(d, Prot)` holds and must return NoCapacity otherwise. It must not return NoCapacity because of a poor candidate, donor or slab choice when a feasible plan exists. When the handle space is exhausted it returns `IdentifierExhausted` (consistent with C3), and the state is unchanged.

**Postconditions on success:**

- The slab plan of §3.5 is performed for `(d, Prot)`.
- Returns a fresh valid handle h with `T_h=T`, `c_h=k^*B`, `e_h = k^*B` (when `Cd ≠ ∅`), `ρ_h = L + λ`, no pending ticket, `|M_h^c| = m^+` for every `c ∈ Cpd`, and one live slot `σ_h^c` for every `c ∈ Cs`.
- For `c ∈ Cpd` and `i<k*`, the page-table entry is chosen from the corresponding pre-call `Index_c`. If a referenced candidate exists it is chosen; otherwise a free cached candidate is reactivated.
- For `c ∈ Cpd` and `i>=k*`, distinct free pages of class c are allocated, including the reserved blocks `[m, m^+)`; these pages must not overwrite the cache-hit pages chosen in this call.
- For `c ∈ Cs`, `σ_h^c` is a fresh unit taken from `F_c`, with `ref_c = 1`; its contents are unconstrained (`W_c = ⊥`).
- Every old reference count increases by exactly one for each new page-table entry or slot that refers to it. Units taken from `F_c` are removed from it.
- The old keys of pages newly allocated as writable are revoked, and their `Index_c` entries correctly removed. Hit pages' keys and KV are unchanged.
- Other active leases' contents, valid KV and live state are unchanged. The returned LeaseView is an immutable snapshot; later extend calls do not change a view already returned.

The demand formula distinguishes reusing an active page from reusing a free cache page: the former saves one free-unit slot, the latter still consumes one. Finding a cache hit does not mean no physical capacity is needed.

attach does not implicitly preempt other requests, does not evict referenced units, and does not advance GPU computation. Which free page or slab is evicted is not part of this contract, except that reclaim happens only when free slabs do not suffice.

### C2. extend(h, suffix) -> Result<LeaseView>

Purpose: append the tokens that need computing next to a lease, and atomically reserve their capacity.

**Calling phase:** h is valid, has no pending ticket, and `c_h=L_h`, i.e. the current input is fully computed by the target track. The draft track need not be caught up. Returns InvalidPhase if the input is not fully computed, and Busy if a ticket is in flight. suffix is non-empty with valid tokens; the existing prefix may not be modified.

After a verify, this is how the caller appends the bonus token sampled after the last accepted draft (D17).

Let the old length be L, the old block count `m = m_h = ceil(ρ_h/B)`, `L'=L+|suffix|`, and `m'=ceil((L'+λ)/B)`. Because `ρ_h <= L + λ < L' + λ`, `m' >= m`. Demand: `d_c = m'-m` for `c ∈ Cpd`, `d_c = 0` for `c ∈ Cs`; `Prot = ∅`.

**Success if and only if:** in a valid phase with `Fits(m')`, extend succeeds if and only if `Cap(d, ∅)`. `¬Fits(m')` returns RequestTooLarge. Insufficient space returns NoCapacity, with the old input, page tables and slab ownership unchanged.

**Postconditions on success:**

- The slab plan of §3.5 is performed for `(d, ∅)`.
- `T'_h=T_h ++ suffix`, `c'_h=c_h`, `e'_h = e_h` and `ρ'_h = L' + λ`; the old input prefix is unchanged.
- For every `c ∈ Cpd`, the old page table remains a prefix of the new one; exactly `d_c` new distinct free pages are added, each with ref=1 and key=None. Pages already reserved at positions `[L, ρ_h)` are reused for the suffix; they are exclusive and unpublished (I16).
- State slots are unchanged.
- Existing KV, live state, published keys and other requests are unchanged; any cache identity the newly occupied pages had is correctly revoked.
- extend does not look up the prefix cache for the new suffix and does not copy shared pages. If the old tail block still has unused slots, it must be exclusive and unpublished in every paged class, and later writes may use those slots.

If the final sampled token does not need to be fed to the model again, the scheduler can record the output and release without calling extend. If extend fails, the caller must keep the external token and choose a strategy such as waiting or preemption; this module neither drops nor resamples it.

### C3. begin_write(h, n, drafts) -> Result<(Ticket, ExecutionPlan)>

Purpose: produce an immutable target-track execution plan for one prefill chunk, one decode step, or one verify step, covering every class of the target track, and mark its resources as in flight.

**Valid call:** h is valid, has no pending ticket, `0<n<=L_h-c_h`, and `drafts` is a sequence of valid tokens with `|drafts| = k <= λ`, where `k > 0` requires `c_h + n = L_h`. No remaining input, an out-of-range n, `k > λ`, invalid draft tokens, or drafts that do not follow the whole input return InvalidArgument; an existing pending ticket returns Busy. `drafts` is empty for an ordinary chunk or decode step.

If the implementation runs out of fresh ticket ids, it returns IdentifierExhausted with the state unchanged; it must never wrap around and accept old tickets.

Let `a=p_h` (here `c_h`, because `Q_h` is empty), `z=a+n`, `D = drafts` and `w = z + k`. By I16, `w <= ρ_h` whenever the call is valid, so begin_write never fails for capacity.

When `Cd ≠ ∅`, the coordinator does not check that `D` is what the draft model proposed. Acceptance is decided by the sampler against the target model's outputs, so a wrong `D` only lowers the acceptance count; it cannot corrupt any credited KV or state.

**Postconditions on success:**

- Returns a fresh target ticket bound to h, the input snapshot, the interval `[a,z)` and the drafts `D`.
- `input_ids=T_h[a:z] ++ D`, `positions=[a,...,w-1]` and `num_drafts = k`. With `k > 0`, the sampler reads the outputs at positions `[z-1, w)`.
- For every `c ∈ Cp`: the write slot for each position j in `[a,w)` is exactly `slot_c(h,j)`. There are `n + k` slots, distinct and within `[0, N·n_c·B)`, and every write page is exclusive and has no published key. The plan lists the class's page mapping for the needed context `[0,w)`. The old prefix `[0,a)` is already valid; the read dependencies of the new interval, including each draft's dependence on the drafts before it, are satisfied by the executor's causal computation semantics.
- For every `c ∈ Cs`: the plan names `σ_h^c`, `init = (a = 0)` and `num_drafts = k`. When `init` is false, the slot holds the state after `T_h[0:a]` (I15). The executor reads it, and must be able to leave in the same slot the state after `T_h[0:z] ++ D[0:acc]` for whichever acceptance count `acc <= k` the completion later reports (E11). With `k = 0` this is v0.3's "the state after `T_h[0:z]`".
- The coordinator records the pending ticket; slab ownership, page tables, slots, ref, F, key, Index, `T_h`, `ρ_h` and both frontiers are unchanged. "Submitted" must not be counted as "completed", and drafts are not part of `T_h`.

A plan is a data and metadata commitment; it does not prove the GPU has executed it. A CPU adapter must not recompute addresses with a different B or unit size, or modify the plan.

### C3b. begin_draft(h, n, k) -> Result<(Ticket, DraftPlan)>

Purpose: produce an immutable draft-track plan that catches the draft model up on `T_h` and lets it propose up to `k` tokens. Present only when `Cd ≠ ∅`; otherwise the method returns InvalidArgument.

**Valid call:** h is valid, has no pending ticket, `0 < n <= L_h - e_h`, `0 <= k <= λ`, `k > 0` requires `e_h + n = L_h`, and the write end `w = e_h + n + max(k-1, 0)` satisfies `w <= ρ_h`. Violations return InvalidArgument; a pending ticket returns Busy; ticket-id exhaustion returns IdentifierExhausted. The bound `w <= ρ_h` always holds once the lease has been extended with the bonus token after its last verify (I16); it can fail only when the caller drafts before that extend.

Let `a = e_h` and `z = a + n`.

**Postconditions on success:**

- Returns a fresh draft ticket bound to h, the input snapshot, the interval `[a,z)` and `k`.
- `input_ids = T_h[a:z]`, `positions = [a,...,z-1]` and `num_proposals = k`. The proposals themselves are generated by the executor and returned to the caller outside this module.
- For every `c ∈ Cd`: the write slot for each position j in `[a,w)` is exactly `slot_c(h,j)`, with the same range, distinctness, exclusivity and no-published-key guarantees as C3, and the page mapping of the class for `[0,w)`. Positions `[z, w)` are tentative: they hold KV for the draft model's own proposals.
- The plan names no target class and no state slot. Target pages, `c_h`, state slots, `T_h`, `ρ_h`, slab ownership, ref, F, key and Index are unchanged.

### C4. finish_write(ticket, completion) -> Result<ComputedFrontier>

Purpose: after a computation has really completed, advance the valid frontier of the ticket's track, commit accepted drafts, and publish newly completed blocks.

**Protocol condition:** ticket is a currently valid pending ticket of this coordinator. An unknown, expired or reused ticket, or one belonging to another coordinator, returns InvalidTicket without changing state. `completion` carries the ticket and the acceptance count `n`. For a target ticket with `k` drafts, `n <= k` is required; for a draft ticket or a ticket with `k = 0`, `n = 0` is required. A violation returns InvalidArgument without changing state; the ticket stays pending, so a corrected completion can still be delivered.

**External premise Completed(ticket):** the completion comes from the executor and confirms three things: the reads and writes for this ticket have finished in every class of its track, they used the planned inputs and addresses, and the new KV and state satisfy the executor spec, including the state rebuild for the reported `n` (E11). How this fact is obtained from CUDA/NCCL is not proved by this module. A bool supplied arbitrarily by a caller must not be treated as proof of physical completion (E1).

The acceptance count needs no assumption for this module's guarantees: every `n <= k` yields a valid state over `T'_h = T_h ++ D[0:n]`, because the KV at position `z + i` was computed from `T_h[0:z] ++ D[0:i+1] = T'_h[0:z+i+1]`. Whether `n` follows the rejection-sampling rule is the sampler's correctness, not the block manager's.

Let `(a, z, k, D)` be the ticket's record and `n` the acceptance count. (In C4, §3.3 and §7, `n` is the acceptance count; in C3 and C3b it is the input chunk length `z - a`.)

**Postconditions on success, target ticket:**

- For the bound lease h, `T'_h = T_h ++ D[0:n]` and `c'_h = z + n`; the pending ticket is consumed exactly once; page tables, slots, `ρ_h` and `e_h` are unchanged. So `L'_h = L_h + n <= ρ_h`, and when `n > 0`, `c'_h = L'_h`.
- For every `c ∈ Cp`, in ghost `V_c`, the provenance of `[a, z+n)` matches `T'_h`; other valid slots are unchanged. Slots at the rejected positions `[z+n, z+k)` gain no claim.
- For every `c ∈ Cs`, `W_c[σ_h^c] = (Namespace, T'_h[0:z+n])`, under E11.
- For every `c ∈ Cp` and every newly completed whole block i with `a<(i+1)B<=z+n`, `K(h,i)` is published on `M_h^c[i]` and `Index_c` updated, with keys computed over `T'_h`; partial blocks must not be published. `K(h,i)` is computed once per block, sequentially from the chain head (the key of the last published complete block, or `Seed(ns)`), and used for every target paged class. The chain head can be kept as the key at block `floor(c_h/B)-1`, but that is an implementation detail.
- Slab ownership, existing read-only cache pages, ref, F, draft classes and other requests' state are unchanged. When different pages of one class have the same key, the index keeps all candidates.
- Returns `c'_h`.

**Postconditions on success, draft ticket:**

- `e'_h = z`; `T_h`, `c_h`, `ρ_h`, page tables and slots are unchanged; the ticket is consumed exactly once.
- For every `c ∈ Cd`, `V_c` on `[a, z)` matches `T_h`; tentative slots `[z, w)` gain no claim, even if a later verify accepts the tokens they were computed from (D20).
- For every `c ∈ Cd` and every newly completed whole block i with `a < (i+1)B <= z`, `K(h,i)` is published on `M_h^c[i]` and `Index_c` updated.
- Target classes, state slots, slab ownership, ref and F are unchanged. Returns `e'_h`.

This version assumes writes always succeed (E4), so there is no "failed completion" branch and no abort; `finish_write` handles only successful completion. A verify that accepts no draft (`n = 0`) is a successful completion. An executor that cannot guarantee E4 must first stop the affected execution and prove that doing so is safe; that is a future extension.

### C5. release(h) -> Result<TokenSnapshot>

Purpose: release all of a lease's references when its request finishes or is preempted.

**Valid call:** h is valid and has no pending ticket. A pending ticket returns Busy; an invalid handle returns InvalidHandle, and a repeated release must not decrement references a second time.

**Postconditions on success:**

- Returns the full input snapshot held by the lease, including every accepted draft, so the caller can keep the request's logical state; the user's output sequence is not deleted or modified. Rejected drafts are not in it.
- Removes h from Req, permanently invalidating h.
- For every `c ∈ Cpd`, decrements `ref_c` exactly once for each g in the original page table, including the reserved pages past `L_h`. Pages whose count reaches 0 enter `F_c`; pages still referenced elsewhere do not.
- For every `c ∈ Cs`, `ref_c[σ_h^c]` drops to 0 and the slot enters `F_c` with `W_c = ⊥`.
- Published keys, every `Index_c` and KV are kept for later reuse; unfinished partial blocks still cannot be cache hits.
- Slab ownership is unchanged; a slab whose units all become free stays with its class and becomes reclaimable (D11).
- Other active leases' inputs, page tables, slots, valid frontiers and pending tickets are unchanged. Release itself does not zero KV or state, does not evict active units, and does not decide scheduler state.

After release, the same business request can attach again with the returned T and obtain a new handle; this is the preemption recovery path. With `Cs ≠ ∅` it restarts from `c = 0` (D13). Draft proposals that were never verified are the caller's to drop or keep; the coordinator holds none.

### C6. inspect(h) -> Result<LeaseView> (read-only helper)

Returns the input length, the target frontier `c_h`, the draft frontier `e_h` (when `Cd ≠ ∅`), the reach `ρ_h`, an immutable view of each paged class's page table (target and draft), each state class's slot, the pending queue `Q_h` with each ticket's track, interval and draft count, and this instance's B and λ. No side effects.

If the optional `slot_of(c, h, j)` is provided, it only guarantees the correct allocated token-slot index for `c ∈ Cpd` and `0<=j<ρ_h`; only for `j<f_h^c` may it also claim that the slot's KV is valid. Invalid handles, classes or indices return explicit errors.

v0.4 does not require can_allocate/can_append. If a preview is added later, it may only be read-only advice or a plan bound to a state version; it cannot unconditionally guarantee that it will still be executable after later state changes.

### C7. arena() -> ArenaView (read-only helper)

Returns `owner[s]` for every slab, and `|F_c|` and `|R_c|` (with `Prot = ∅`) for every class, target, draft and state. No side effects. It is observability for the scheduler, not a reservation.

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
| Two paged classes, the prefix is cached in one but not the other | k* stops at the first position missing in any class |
| Paged class needs 2 more pages, has 1 free, `FS = ∅`, no reclaimable slab anywhere | NoCapacity; must not allocate one page and leave a half-done state |
| `u_c` does not divide `S` | create returns ConfigError (A1) |
| `S = lcm(96 KiB, 640 KiB) = 1.875 MiB` | `n = 20` pages and `3` state slots per slab; unit g of each class is at `g·u_c` with no tail waste |
| attach of a hybrid lease when the state class has a free slot in an owned slab | No slab acquired for the state class |
| attach of a hybrid lease, state class full, `FS = ∅`, a paged slab with all pages ref=0 but keyed, paged class keeps `>= d` free outside it | Reclaim that slab: its keys and Index entries are revoked, and it becomes a state slab; success |
| Same as above, but the paged class's free units are spread over partly used slabs | NoCapacity, even if free bytes exceed `u_state` (D12) |
| A reclaimable slab holds the only free candidate for a hit position of this attach | Not reclaimed in this call (`Prot`) |
| `FS` non-empty and a reclaimable slab exists | The free slab is used; nothing is reclaimed |
| Release of the last lease using a slab | The slab stays owned and becomes reclaimable; keys are kept |
| extend of a hybrid lease | State demand is 0; only paged classes may need units or slabs |
| attach of an input with `¬Fits(m)` | RequestTooLarge even on an empty arena, not NoCapacity |
| First plan of a lease (`a = 0`) with a state class | `init = true`; the executor initializes the slot before reading it (E10) |
| In-flight ticket not yet complete | release/extend return Busy; its pages and slots cannot be reclaimed, so their slabs are not in any `R_c` |
| The same completion arrives twice | The second is InvalidTicket; the frontier and publication do not advance twice |
| An old handle or old ticket arrives after preemption | Rejected; it does not act on the new lease |
| B=512, execution position j=256, M[0]=0 | The slot must be 256; must not rely on Sequence's default B=256 |
| Many distinct prompts published, then their pages reused or slabs reclaimed (long-running churn) | Stored Index entries stay ≤ `|U_c|`; no entry survives for a key with no candidates, or for a unit outside `U_c` (I11, I13) |
| **Speculative decoding (v0.4)** | |
| `λ = 0`, `Cd = ∅` | Every method behaves exactly as in v0.3; `begin_write` with non-empty drafts returns InvalidArgument; `begin_draft` returns InvalidArgument (obligation 18) |
| `Cd ≠ ∅` with `λ = 0` | create returns ConfigError |
| attach of `L = 2B - 1` with `λ = 3`, `B = 64` | Page tables cover `m^+ = ceil(130/64) = 3` blocks in every paged class, not 2; the demand counts 3; `Fits(3)` decides RequestTooLarge |
| attach where `Fits(ceil(L/B))` holds but `Fits(ceil((L+λ)/B))` fails | RequestTooLarge: the reservation is part of the lease |
| Verify ticket with `k = 4` drafts, all accepted (`n = 4`) | `T'_h = T_h ++ D`, `c'_h = L'_h = L_h + 4`; KV at all four draft positions is credited; `ρ_h` unchanged, so `ρ_h - L'_h = λ - 4` |
| Verify ticket with `k = 4`, `n = 0` | `T_h` and `c_h = L_h` as before the ticket; no draft position is credited; nothing is freed or published; a later ticket overwrites those slots |
| Verify ticket with `k = 4`, `n = 2`, where position `z + 1` completes block i | Block i is published under `K(h,i)` over `T'_h` (which includes the two accepted drafts); positions `z+2, z+3` are not credited |
| Verify ticket whose rejected drafts complete a block | The block is not published; no key is computed over a rejected token |
| Rejected drafts would complete a block whose tokens equal a cached block | No hit, no publication: keys are only computed over `T_h` |
| `begin_write` with drafts while `c_h + n < L_h` | InvalidArgument: drafts must follow the whole input |
| `begin_write` with more than `λ` drafts | InvalidArgument; no partial reservation is taken |
| `finish_write` with `n > k`, or `n > 0` on a draft ticket | InvalidArgument; state unchanged; the ticket stays pending |
| Same completion delivered twice with different `n` | The second is InvalidTicket; `T_h` and `c_h` advance once, by the first `n` |
| A second verify right after a verify (any `n`), without the bonus-token extend | `c_h = L_h`, so `begin_write` returns InvalidArgument (no remaining input); the caller must `extend` with the bonus token first |
| `extend` with the bonus token after `n = λ` accepted drafts | Demand counts `ceil((L'+λ)/B) - m_h`, which can be 1 or more pages; on NoCapacity the lease keeps its accepted drafts and `c_h = L_h` |
| Hybrid lease (state class), verify with `k = 3`, `n = 1` | The plan names the single slot `σ_h^c`; after finish, `W_c[σ_h^c] = T_h ++ D[0:1]`; no second slot is ever allocated for the state class |
| Hybrid lease, a ticket that covers the whole prompt (`a = 0`, `z = L_h`) and carries `k > 0` drafts | Allowed; the plan has `init = true` and `num_drafts = k`; the executor initializes the slot, then E11 applies as for any verify |
| Draft ticket with `k = 4` | Writes draft classes at `[e_h, L_h + 3)`; `e'_h = L_h`; tentative draft KV at `[L_h, L_h+3)` is never credited |
| Verify accepts n drafts, bonus token extended, next draft ticket | `e_h = L_h - n - 1` (behind by the accepted drafts and the bonus token); the draft ticket re-feeds `T_h[e_h:L_h]`, so it is never credited from tentative draft KV (D20) |
| Draft ticket with `k > 0` before the bonus-token extend | Allowed only if `w <= ρ_h`; otherwise InvalidArgument |
| Draft ticket pending, then `begin_write` on the same lease | Busy: one pending ticket per lease across both tracks |
| Target prefix cached, draft classes not (or the reverse) | `k*` stops at the first block missing in any class of `Cpd`, as for two target classes |
| Draft classes and target classes compete for slabs | One `Cap` over all classes; a draft slab whose pages are all `ref = 0` is reclaimable for a target class and vice versa |
| Release with a pending draft ticket | Busy, as for a target ticket |
| Release after rejected drafts | The returned snapshot contains no rejected token; reserved pages past `L_h` return to `F_c` unkeyed |

## 8. Mapping from upstream methods and intentional changes

| Upstream interface | Draft interface | Change |
|---|---|---|
| BlockManager constructor | create | Fixes the arena, the class table and B, checks A1, and validates the representation range |
| can_allocate + allocate | attach | One atomic operation across every class; does not depend on an externally supplied num_cached_blocks |
| Sequence.append_token + can_append + may_append | extend | Grows the input snapshot and capacity (including the draft reservation) atomically; needs a scheduler adapter |
| seq.num_scheduled_tokens and runner preparation | begin_write / begin_draft | Produces an address plan for every class of one track consistent with the instance, and records in-flight protection |
| hash_blocks + updating num_cached_tokens | finish_write | Commits the frontier, accepted drafts, state provenance and cache publication together after completion |
| deallocate | release | Release while in flight is forbidden; invalidated handles prevent double release |
| compute_hash | Cache identity | Chained 256-bit digest, both identity and index key, shared by every paged class; enters via the collision-resistance assumption E8 (§9) |
| kvspec `layout()` → `PhysicalPlan.paged.stride` / `.state.stride` | `u_c` of a paged / state class | The planner still decides bytes inside a unit; this contract decides which unit |
| kvspec `plan()` pool counts (`slots = ceil(slot_ratio · max_num_seqs)`, rest to blocks) | slab arena | The static split between blocks and state slots is replaced by on-demand slabs |
| `get_num_state_slots(max_num_seqs)` | state class units on demand | No fixed slot count; a slot exists for each lease that holds one |
| `KVCacheManager._view` over `[num_blocks, stride]` / `[num_slots, stride]` buffers | one arena viewed as `[N·n_c, u_c]` per class | Valid by A1; the views alias the same arena but distinct units never overlap (arena disjointness) |
| kvspec `Static` pool | outside the arena | Non-goal (§1.1) |
| vLLM `KVCacheManager.allocate_slots(..., num_lookahead_tokens)` (`vllm/v1/core/kv_cache_manager.py`, slot count at lines 541–544) | the reach `ρ_h = L_h + λ` set by attach / extend (D18) | vLLM reserves lookahead slots on every scheduling step; v0.4 reserves them only when the input grows, so a verify or a completion never allocates |
| vLLM scheduler `request.num_computed_tokens -= num_rejected` (`vllm/v1/core/sched/scheduler.py:2205–2214`) | finish_write with acceptance count n | vLLM schedules drafts as computed and rolls the counter back; v0.4 never credits a draft until it is accepted, so there is nothing to roll back and no key over a rejected token |
| vLLM spec tokens scheduled with the last input token | begin_write with `drafts` | The verify plan carries the drafts explicitly and is bound to them; drafts are not part of `T_h` |
| vLLM draft proposers (`SpecDecodeBaseProposer.propose` in `vllm/v1/spec_decode/llm_base_proposer.py:511`) and their KV groups | draft paged classes `Cd`, begin_draft (D20) | Draft KV shares the arena and `Cap`. The proposer's first pass re-feeds the target-verified tokens with the target's hidden states (`set_inputs_first_pass`, input shift at lines 840–846), which matches D20's rule that tentative draft KV is never credited |
| vLLM Mamba `num_speculative_blocks = num_speculative_tokens` (`vllm/model_executor/layers/mamba/abstract.py:84–90`) | non-goal (§1.1) | Extra state blocks per draft token are not modelled; v0.4 keeps one state slot per lease |
| vLLM KDA RecoverSSM (`use_kda_recoverssm`, `vllm/config/vllm.py:3418–3430`): `_kda_recoverssm_verify_kernel` (`vllm/models/kimi_k3/nvidia/ops/recoverssm.py:63–223`) reads the checkpoint and saves per-token records; `_commit_kda_state_kernel` (lines 400–583) rebuilds the accepted state; `_compact_conv_state_kernel` (line 322) shifts the conv window | one state slot per lease, with the records inside the state unit (D19, E11) | The checkpoint `S_0` is the slot's content after `T_h[0:a]` (I15); the commit writes `S_{z-a+n}` back to the same slot. Record buffers are sized by `append_kda_recoverssm_record` (`vllm/model_executor/layers/mamba/mamba_utils.py:331–349`) for `1 + num_spec` positions; under this contract they are part of `u_c` |
| vLLM `RecoverSSMState.commit_step` (`vllm/v1/worker/gpu/model_states/recoverssm.py:38–66`) | the executor side of finish_write for a verify ticket | Runs the state commit with the accepted count before the block manager is told; E11 requires it to finish before the completion is reported (E1) |
| vLLM align-mode prefix caching of Mamba state at block boundaries (`boundary_state_idx`, `boundary_recovery_len` in `recoverssm.py`) | not used | v0.4 has no state checkpoints (D13), so no boundary state is stored; deferred with state hits (§10) |

This is a new interface designed for a provable implementation; it cannot replace the old object without adaptation. In particular, `Sequence` may no longer hold an authoritative page table, state slot or cache frontier that can be modified independently. If a mirror is needed, it may only be exported from the core, and the adapter must be proved to use a consistent version.

## 9. Proofs the implementation must deliver

### 9.0 Main theorem and external assumptions

**Main theorem.** At every step of any valid trace, if the executor executes the plan returned by `begin_write` or `begin_draft`, with write end `w` and the classes of its track, then:

(a) for every paged class c of the track, the plan's write slots are exactly `slot_c(h,j)` (`j in [a,w)`), distinct and within `[0, N·n_c·B)`; for every `c ∈ Cs` (target plans only), the plan's slot is `σ_h^c`;
(b) once every earlier ticket of the same lease and track in `Q_h` has completed (always, when `Q = 1`), every slot of `[0,a)` corresponds in ghost `V_c` to `(Namespace, T_h[0:j+1])`, and, for a target plan with `a > 0`, `W_c[σ_h^c] = (Namespace, T_h[0:a])`;
(c) after `finish_write` with acceptance count n, `T'_h = T_h ++ D[0:n]`; every slot of `[a, z+n)` is updated to its prefix of `T'_h`; every state slot holds `(Namespace, T'_h[0:z+n])`; every newly published block i satisfies `den(key_c[M_h^c[i]]) = (Namespace, T'_h[0:(i+1)B])`; and no credited slot, key, published page or state provenance depends on a rejected draft or on a tentative draft-track position;
(d) the bytes the plan writes are disjoint from every published page, every shared page, every other lease's units, every unit of the other track, and the writes of every pending plan of another lease; the plans of one lease and track write disjoint consecutive intervals (arena disjointness);
(e) `Valid(S)` is preserved, each method's frame conditions hold, and error paths satisfy the strong failure atomicity of §5 item 3;
(f) `begin_write`, `begin_draft` and `finish_write` change no slab owner, no `F_c` and no reference count, for every acceptance count.

**External assumptions.** The following are not proved, but they must be listed and checked along the verified call chain. E8 is the only cryptographic assumption in this version. A1 is not an assumption: create checks it.

| ID | Assumption | Consequence if violated |
|---|---|---|
| E1 | Completion events are real: the executor confirms the reads and writes are done in every class and used the planned inputs and addresses | The frontier advances over unwritten or wrongly written KV or state |
| E2 | KV and state depend only on the prefix: values are independent of batch composition and chunking (within tolerance). For recurrent state this includes chunked versus step-by-step computation | The ghosts `V_c` of shared pages, or `W_c`, no longer hold |
| E3 | Calls are single-threaded and sequential (or serialized by the caller) | The invariants break under concurrency |
| E4 | Writes always succeed: every issued ticket eventually completes successfully; no failed completion, silent drop, or process termination | Pending never clears, and units stay occupied forever |
| E5 | The executor uses the planned slots, state slots, the instance's B and every `u_c`, and does not recompute addresses | Writes to the wrong unit, slot or class |
| E6 | The Namespace is complete: the final field table covers weights, dtype, B, every class's kind, `u_c` and in-unit layout, rope/scaling, attention semantics and adapters, and the draft model when `Cd ≠ ∅`; v0.4 uses a dummy byte string, and completeness is the caller's responsibility | Different semantics share keys, causing silent wrong reuse |
| E7 | `Canon`/`Enc` follow the §3.3 canonical encoding: fixed-width uint32 tokens, length-prefixed fields, fixed field order, domain separation | Structural collisions (probability 1) that E8 cannot cover |
| E8 | SHA-256 is collision resistant; the collision probability over `Q` key generations/comparisons during the deployment is `<= Q^2/2^257 + Q/2^256` | Wrong KV reuse across requests (a data leak under multi-tenancy) |
| E9 | The arena is one allocation of at least `N·S` bytes whose base is aligned to every class's required alignment (kvspec `Pool.align`), and every kernel addresses unit g of class c at `base + g·u_c` plus the kvspec region offset | Units of different classes alias, or kernels read misaligned or wrong bytes |
| E10 | When a plan has `init = true` for a state slot, the executor sets the slot to the model's initial state before reading it; it writes state only to the planned slot | A lease starts from another lease's leftover state |
| E11 | State rebuild in one slot: for a target plan with `num_drafts = k` and a state class c, the executor reads the slot (the checkpoint, after `T_h[0:a]`), and before it reports completion with count n it leaves in the same slot the state after `T_h[0:z] ++ D[0:n]`. Everything it needs for that (vLLM RecoverSSM's per-token corrections and key/gate records for `1 + λ` positions, the conv window widened by `λ`) lives inside the state unit, so `u_c` is sized for `λ`; it writes no other unit. With `k = 0` this is the v0.3 behaviour | The slot holds a state that includes rejected drafts or misses accepted ones, and every later step of the lease computes on a wrong state; or the records overflow into a neighbouring unit |
| E12 | Draft-track KV depends only on the prefix: the draft model's KV at position j, computed from inputs that are all in `T_h`, depends only on `T_h[0:j+1]` (and on the target model, for drafters that read target hidden states, such as EAGLE). E2 holds for draft classes, and E6's Namespace covers the draft model, its unit layout, and the target model it reads from | Shared or reactivated draft pages carry KV of another prefix or another draft configuration; acceptance rates drop. Target KV and outputs are not affected, because acceptance is checked against the target model |

### 9.1 Proof obligations

1. **Initialization:** Valid holds after a successful create, and create returns ConfigError exactly in the cases listed in C0.
2. **Per-method preservation:** for every real method body, prove that Valid is preserved, together with the functional, error and frame conditions of C0–C7 and C3b.
3. **Allocation sufficiency:** attach's k*, `r_c`, `d_c` and `Prot` match their definitions; with correct candidate choice, `Cap` guarantees success.
4. **Addressing and isolation:** slot range per class, no aliasing within a request, no conflicts between pending writes, distinct live slots, and shared pages are never written.
5. **Cache soundness:**
   - the canonical chained-key implementation (`Canon`/`Enc`/`Tag`/domain separation) is consistent with every `Index_c` in both directions;
   - the publication condition is correct in every paged class;
   - a page's identity is revoked before it is written for a new use, whether by fresh allocation or slab reclaim;
   - the chain lemma (§3.3) is proved in the ideal hash model, with E8 as the only cryptographic assumption for the concrete instance.
6. **Protocol correctness:** handle/ticket invalidation, single consumption of completions (including completions with different acceptance counts), and in-flight units are never reclaimed. Prove that the executor-interface premises hold along the verified call chain, or list them as explicit external assumptions (E1, E2, E5, E9, E10, E11, E12).
7. **Termination and representation:** all loops terminate; machine-integer, array and set operations are safe; a verifier UNKNOWN or timeout is not a pass.
8. **Deployment link:** run the verified implementation or its trusted compiled output. A hand-rewritten version does not automatically inherit the proof. The digest implementation and the canonical `Canon`/`Enc` must match the proof's definitions byte for byte.
9. **Bounded metadata:** prove that every method preserves I11 (with I11a), so metadata stays O(Σ_c N·n_c) for traces of any length.
10. **Arena disjointness:** prove the theorem of §4 from A1 and I12, and that every unit address in a plan lies in `[0, N·S)`.
11. **Capacity exactness:** `Cap(d, Prot)` holds iff a slab plan following §3.5 rules 1–4 exists; the implementation acquires exactly `need_c` slabs per class, uses `FS` before reclaiming, never reclaims a slab in `Prot` or with a referenced unit, and never takes units from a slab it gave up in the same call.
12. **Reclaim correctness:** reclaiming a slab preserves I3, I8, I11 and I13, revokes every key in it, and changes nothing outside that slab's units and `owner`.
13. **Cross-class atomicity:** on every error path of attach and extend, slab ownership and every class's state are unchanged; on success, no lease has resources in some classes but not others (I1, I14).
14. **Refinement of v0.2.1:** with `|Cp| = 1` and `Cs = ∅`, every public method's observable behavior (results, errors, k*, cached tokens, plans up to page renaming) equals v0.2.1 with `P = N·n_c`, treating units of free slabs as unkeyed free pages. This lets the v0.2.1 proofs be reused for the paged class.
15. **Draft reservation:** every method preserves I16; attach and extend compute the demands of C1/C2 from `m^+` and `m'`, and `Cap` remains exact for them (obligation 11 with the new demands); `begin_write`, `begin_draft` and `finish_write` never change slab ownership, `F_c` or `ref_c`, and a valid `begin_write` never fails for capacity.
16. **Partial commit:** for every acceptance count `n <= k`, `finish_write` establishes I4, I5, I5b, I6 and I15 over `T'_h = T_h ++ D[0:n]`; `T'_h` extends `T_h`; `c_h` and `L_h` never decrease; no key is computed over a token outside `T'_h`; and a rejected or invalid count leaves the state unchanged.
17. **Two tracks:** target classes and draft classes are each in lockstep (same leases, inputs, reach and page-table lengths in every paged class); `e_h <= L_h`; a lease has at most one pending ticket across both tracks; a draft plan names no target class and no state slot, and a target plan names no draft class; every write of one track is disjoint from every unit of the other (obligation 10).
18. **Refinement of v0.3:** with `λ = 0` and `Cd = ∅`, every public method's observable behavior (results, errors, k*, cached tokens, plans up to page renaming, arena views) equals v0.3, with `drafts` empty and `n = 0`. This lets the v0.3 proofs be reused, and is proved before obligations 15–17.
19. **Executor premises for spec decoding:** E11 and E12 enter the proof only as the ghost updates of `finish_write` (W after a verify; V and publication in draft classes). No other method body may depend on them, and the plan exposes `num_drafts` to state classes so that E11 can be checked by an executor contract.

### 9.2 Trusted base

1. E8 (SHA-256 collision resistance and the ε bound);
2. E6 (Namespace completeness) and E7 (canonical encoding): design obligations, not probabilistic assumptions;
3. trusted compiled output (§9.1 item 8);
4. E1/E2/E5/E9/E10/E11/E12 (executor and arena interface). E3/E4 are deployment assumptions (single thread, writes always succeed) and do not enter the method-body proofs.

Auxiliary lemmas, loop invariants and data structures may be designed by the agent. But new assumes, axioms, skipped function bodies, or weakened pre/postconditions must not be used to pass off a proof as complete. E1–E12 are explicitly listed external assumptions and must not become a loophole for new assumes.

v0.3 was implemented and proved in these steps: the slab arena with one paged class and obligation 14; several paged classes with per-class Index and `Cap`; state classes and cross-class atomicity; the ticket/completion protocol across classes and the Python runner adapter. v0.4 continues in these steps: (1) `λ` and the reach `ρ_h` with the new attach/extend demands, `drafts = []` and `n = 0` everywhere, and obligation 18; (2) verify tickets and partial commit on target paged classes (obligations 15, 16); (3) state classes with `num_drafts` and the E11 ghost update; (4) draft classes, `e_h` and `begin_draft` (obligation 17); (5) the Python facade. Each step keeps the same external functional goals; deferred properties must not be counted as proved.

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

Still open (must be decided in a later version or before implementation):

- Tree drafts: a compaction step in the plan that moves the accepted path's KV into the slots of `[z, z+n)`, and how it interacts with I6 and I16.
- Overlapped scheduling: issuing the draft ticket for step t+1 before the verify of step t completes (vLLM async scheduling), which needs either two pending tickets per lease or a ticket that depends on another.
- Dynamic `λ` per lease or per step (vLLM's dynamic speculative length), versus the fixed reservation of D18.
- Whether to keep the reservation for leases that are not speculating, or let attach/extend take a per-call `λ_h <= λ`.
- Draft classes with a different `B` from the target, and draft models with recurrent state.
- State checkpoints at block boundaries during a verify (vLLM align mode's `boundary_state_idx`), once state hits exist.
- A Namespace field table that ties draft classes to the target model they read hidden states from (E12).

- State checkpoints and joint prefix hits: checkpoint units keyed by `K(h,i)` at grain boundaries (DeepInfer stores state only at multiples of `KVSTORE_GRAIN`), the `on_hit` modes `restore` / `replay` / `empty`, the copy from checkpoint to live slot in the plan, and the joint `k*` rule.
- Guidance on slab size when the LCM of unit sizes is large: how much padding of `u_c` (kvspec `stride_align`) is acceptable.
- Several paged classes with different B (e.g. different lifetimes), and how hits align across them.
- Reclaim policy among reclaimable slabs (e.g. fewest keyed pages first), and whether an explicit trim operation that returns idle slabs is useful.
- The real Namespace field table (E6), its alignment with `Engine.store_identity()`, and how it encodes the kvspec plan of every class.
- Whether to share identity with `prefix_keys` in `shell/offload.py`. Sharing requires aligning the Tag, the namespace fields and `grain == B`; otherwise the contract should state explicitly that there are two separate schemes.
- Primitives for offload (`adopt`).
- Static caches inside the arena.
- The verification toolchain and repository name (outside this document).

One more explicit boundary: this draft proves resources, provenance, addresses and protocol. Whether the GPU actually completed according to plan, and whether the KV and state values are numerically correct, need a separate executor contract. That boundary cannot be treated as proved just by assigning values to the ghosts `V_c` and `W_c`.
