# Block Manager Functional Contract v0.3 (draft)

Status: specification draft for review. v0.3 is implemented and verified in this repository (`Coordinator`); `SPEC_NOTES.md` maps each clause to its proof and lists the deviations. The v0.2.1 `Manager` remains as the paged-class building block (§9.1 obligation 14).
Date: 2026-11-04 (v0.2.1: 2026-11-03; v0.2: 2026-11-02; v0.1: 2026-11-01).
Reference code: nano-vLLM `bb823b3e06983d71485a8e1f23715ebd87d98ef8`: `block_manager.py`, `sequence.py`, `scheduler.py`; `prefix_keys` in `shell/offload.py` (the existing implementation of chained keys).
Layout reference: DeepInfer `0d0a93ff09c99af7a8521f230e16507bf3e00dda`: `deepinfer/kv_spec/kvspec.py` (`LogicalSpec`, `layout`, `PhysicalPlan`), `deepinfer/kv_spec/deepseek_v4.py`, `deepinfer/worker/kv_cache_views.py`.

Changes in v0.3 relative to v0.2.1:
- Physical memory becomes a slab arena: `N` slabs of `S` bytes, each free or owned by exactly one unit class. Several managers share it, replacing the "separate pools per manager" rule of §1 (D10–D12, §3.1, §3.5).
- Unit classes have their own unit size. Paged classes keep the v0.2.1 page semantics. State classes hold one fixed-size, in-place recurrent state slot per lease (D13).
- Base assumption A1: every unit size divides the slab size (`S = lcm` of the unit sizes is the smallest choice). It is checked at create, and it makes unit addressing `g·u_c` valid for existing block-table kernels (§3.1).
- A slab whose units all have `ref = 0` is reclaimable even when its pages are still keyed; reclaiming revokes those keys (D11). Capacity becomes the exact per-class-plus-slab predicate `Cap` (§3.5).
- A coordinator owns handles, tickets, inputs and the frontier, and makes every multi-class operation atomic (D14). One ticket's plan covers every class.
- No state cache hits in v0.3: a lease of a configuration with a state class always attaches with `k* = 0` (D13, §6 C1). Spec-decode rollback stays a non-goal.
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
- **Unit-class managers.** Each class `c` cuts its slabs into units of `u_c` bytes. A paged class manages KV pages with the v0.2.1 semantics (page tables, prefix reuse, publication). A state class manages one fixed-size live state slot per lease.
- **Coordinator.** Owns leases, inputs, the computed frontier and tickets. It turns each public operation into an all-or-nothing change across the arena and every class.

This module is responsible for: slab ownership, physical unit allocation in every class, request page tables and state slots, whole-block prefix reuse in paged classes (keyed by chained digests), capacity growth, the computed frontier, unit protection during execution, cache publication, and reference release.

The following semantics belong to other modules: choosing which requests to schedule each step, prefill/decode priority, token budget, EOS and max_tokens, the model's context limit, the byte layout inside a unit (the KV spec planner, e.g. DeepInfer's `kvspec.layout`), numerical correctness of the model, and GPU kernels and communication. The block manager does not modify this business state.

The module guarantees that the page tables, state slots and plans it outputs conform to this contract; the external executor must execute according to the plan. The correctness guarantees hold only given a fixed KV namespace, valid external completion events, and a correct executor.

One coordinator serves one model configuration and owns its arena. External code cannot bypass it to overwrite completed KV, write a live state slot, or reuse a unit. Several coordinators need separate arenas; sharing one arena across coordinators is out of scope.

### 1.1 Explicit non-goals and write assumption for v0.3

The following capabilities are not in this draft's state machine. Callers must handle them separately and must not treat them as proved properties:

- Partial commit for speculative decoding, and truncation of rejected drafts: `finish_write` only advances the frontier to the ticket's `z`, and `extend` only appends, so tokens of a rejected draft cannot be removed from `T_h`. This includes state rollback: rollback rows of a window ring and extra state copies (kvspec `Window.rows` beyond the window, `State.copies > 1`) are bytes inside a state unit, and this contract gives them no semantics. The existing shell's `spec_decode` (`docs/spec/shell.md` §1.9) needs additional primitives.
- State cache hits: there are no state checkpoints. A state slot is never keyed, published or shared, so a configuration with a state class never reuses a prefix (D13). kvspec's `on_hit` (`restore` / `replay` / `empty`) is ignored by v0.3.
- External KV import (adopt) for offload/store: the only way to advance `c_h` is the executor's completion event for a ticket. The `restore_prefix` path needs additional primitives.
- Static caches shared by all requests (kvspec `Static`, e.g. sink tokens): allocated by the caller outside the arena.
- Slab compaction, defragmentation, or moving a live unit.
- Multi-threaded concurrent calls: see the single-thread assumption E3 in §5.

This version **assumes writes always succeed** (E4): every issued ticket eventually completes successfully, with no failed completion, silent drop, or process termination. There is therefore no abort/rollback path, and no promise of progress under GPU faults (see C4).

Until these primitives exist, an adapter must not claim to cover every feature of the existing scheduler (in particular `spec_decode` and `store`).

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
| D13 | A state class holds exactly one exclusive live slot per lease, updated in place, never keyed, published or shared. There are no state cache hits in v0.3 | A page-prefix hit is useless without the matching recurrent state, so a configuration with a state class attaches at `c = 0`. Checkpoints and joint hits are deferred (§10) |
| D14 | The coordinator owns handles, tickets, `T_h`, `c_h` and `Pending`; one frontier per lease covers every class; one ticket's plan covers every class | Multi-class operations are atomic, and frontiers cannot diverge between classes |
| D15 | All paged classes of a coordinator share `B` and one key chain per lease; each paged class has its own `Index` | The executor computes all classes for the same positions, so they complete the same blocks together. Different `B` per paged class is deferred |

D1–D15 are proposed semantics, not claims that upstream already satisfies them. D4, D6–D8 and D10–D14 in particular require changes to the implementation and interface; this draft does not promise function-by-function compatibility with the old API.

## 3. Abstract state

### 3.1 Fixed configuration

- `N >= 1`: number of slabs, `SlabId = {0,...,N-1}`.
- `S >= 1`: bytes per slab.
- `Classes = Cp ∪ Cs`: a finite, disjoint, ordered set of unit classes. `Cp` (paged classes) is non-empty; `Cs` (state classes) may be empty.
- For each class `c`: unit size `u_c >= 1` bytes, with **base assumption A1: `u_c | S`**. Let `n_c = S / u_c >= 1` (units per slab). The unit ids of class `c` are `{0,...,N·n_c - 1}`; unit `g` lies in slab `slab_c(g) = floor(g / n_c)`, and `units_c(s) = [s·n_c, (s+1)·n_c)`.
- `B >= 1`: token slots per unit of every paged class (D15).
- `Namespace`: the configuration identity that decides cache reusability, an opaque byte string. The final field table should cover model and weight version, adapters, positional encoding/scaling, attention semantics (including sliding window), B, and, for every class, its kind, `u_c` and in-unit layout (the kvspec `LogicalSpec` and `PhysicalPlan` regions). It should align with `Engine.store_identity()`. v0.3 still uses a dummy (an implementation may pass a fixed string such as `"dummy-v0.3"`). Completeness remains the caller's obligation (E6); the field table is deferred.
- `Token`: the type of valid token ids; sequences are finite and 0-indexed.

**Addressing.** Unit `g` of class `c` occupies arena bytes `[g·u_c, (g+1)·u_c)`. By A1 this range lies inside slab `slab_c(g)`'s bytes `[s·S, (s+1)·S)`, so a class's units are exactly the arena viewed as a `[N·n_c, u_c]` array. Inside a unit, the kvspec plan decides where each layer's region lies. For a paged class, `u_c` is the plan's paged-pool stride for `block_tokens = B`; for a state class it is the state-pool stride. Arena base alignment is E9.

**Capacity of a request size.** Let `Fits(m) ⇔ Σ_{c ∈ Cp} ceil(m / n_c) + |Cs| <= N`. This is whether a lease with `m` blocks fits in an otherwise empty arena.

The abstract spec uses mathematical integers. A concrete implementation must prove that machine-integer arithmetic on slab ids, unit ids, lengths, counts and byte addresses does not overflow (in particular `N·S` bytes and `N·n_c·B` token slots), and must reject unrepresentable configurations at construction. Other limits, such as CUDA's current requirement that B be a multiple of some value and its int32 slot limit (now on `N·n_c·B` per paged class), must be added explicitly by the corresponding implementation or adapter, never silently ignored.

### 3.2 Mutable state

| Symbol | Meaning |
|---|---|
| `owner[s]` | The class that owns slab s, or `Free` |
| `FS` | `{s | owner[s] = Free}`, the free slabs |
| `U_c` | Derived: `{g | owner[slab_c(g)] = c}`, the units class c currently owns |
| `Req[h]` | An attached lease: the input sequence `T_h` (never modified in place), computed frontier `c_h`, for each `c ∈ Cp` a page table `M_h^c`, for each `c ∈ Cs` a live slot `σ_h^c`, and an optional pending ticket |
| `ref_c[g]` | How many active leases reference unit g of class c |
| `F_c` | Units of class c that are owned and referenced by no lease; for paged classes this includes free cache pages that still hold reusable data |
| `key_c[g]` | Paged classes only: page g's reusable cache identity (a chained 256-bit digest), or None |
| `Index_c[K]` | Paged classes only: all candidate pages of class c whose published key is K |
| `Pending[t]` | A submitted but not yet completed computation: the lease, original frontier `a`, interval end `z`, and execution plan `plan` |
| `V_c` | Paged classes: ghost KV-provenance marker; records the Namespace and full causal token prefix of each token slot of class c |
| `W_c` | State classes: ghost marker; `W_c[g]` is `(Namespace, τ)` when unit g holds the state after prefix τ, or `⊥` |
| `den` | Ghost used by the proof: a partial function from digest to `(Namespace, full causal prefix)`; it gives chained keys their meaning |

The domain of `den` is exactly the chain outputs `{Seed(ns)} ∪ {K(h,i)}`. It is injective in the ideal model, and E8 covers this for the concrete instance. It is not part of the executable state.

Request handles and execution tickets use distinct types that cannot be confused, and are bound to the coordinator and to their generation. An invalidated handle or ticket can never become valid again on a later object. If a concrete implementation's counter space is exhausted, it must safely reject new operations and never wrap around and reuse ids.

A request in this draft means a block-manager lease, not the scheduler's WAITING/RUNNING/FINISHED state. The scheduler still manages its business requests; releasing a lease does not delete the user request or its output.

### 3.3 Semantic conventions

Let `L_h = |T_h|` and `m_h = ceil(L_h/B)`.

Page-table entry `M_h^c[i]` is the page of logical block i in paged class c. The token-slot index of position j in class c is:

\[
slot_c(h,j)=M^c_h[\lfloor j/B\rfloor]\cdot B+(j\bmod B).
\]

It lies in `[0, N·n_c·B)`. The bytes a slot occupies follow from the unit address `M_h^c[floor(j/B)]·u_c` and the kvspec regions; this contract fixes only the unit.

`c_h` is the length of the contiguous computed prefix, shared by every class (D14): positions `[0,c_h)` have valid KV in every paged class, `[c_h,L_h)` are not all done, and every live state slot of h holds the state after `T_h[0:c_h]` (I15). Reserved capacity does not mean the KV is valid.

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

`K(h,i)` is defined only for complete blocks, `(i+1)B <= L_h`; an incomplete tail block has no key and is never published. A key means the full causal prefix `(Namespace, T_h[0:(i+1)B])`, given by the ghost `den`; the chained construction is only its O(1) representation. Any difference in an earlier block must change every later key. The chain guarantees this; "current-block tokens only", "token hash only" or "same length" are all insufficient.

In the ideal hash model (`H` injective) the chain lemma holds:

\[
K(h,i)=K(h',i') \iff ns=ns' \land i=i' \land T_h[0:(i+1)B]=T_h'[0:(i+1)B].
\]

For the concrete instance (SHA-256) the equivalence holds with probability `>= 1 - \epsilon`, `\epsilon <= Q^2/2^{257} + Q/2^{256}`, where `Q` is the number of key generations and comparisons during the deployment (E8). `den` is injective on chain outputs (ideal model), and E8 likewise covers the concrete instance; hence `den(K(h,i)) = (Namespace, T_h[0:(i+1)B])` is the meaning of a key.

A key lives as long as its page stays published: the digest is stored on the page, and the `Index_c` entry is removed when the key is revoked, either because the page is chosen as a new writable page or because its slab is reclaimed. There is no intern table, ancestor chain, or GC. A page that is released but not reused keeps its key (C5), so total metadata is O(owned units) digests (made precise by I11). The chain head (the key of the last published complete block, or `Seed(ns)`) lets `finish_write` compute the keys of new blocks incrementally; it is an implementation detail.

In v0.3, keys are still computed and published when `Cs ≠ ∅`, even though no lease of such a configuration can hit them (D13). This keeps the paged-class semantics identical to v0.2.1 and prepares for state checkpoints.

### 3.4 Representation of Index and Pending

**Index.** For each `c ∈ Cp`, `Index_c : Map<Key, Set<UnitId>>`, with `Index_c[K] = {g | key_c[g] = K}` (I8).
- It is the inverse relation of `key_c` and covers only published pages. `F_c` contains both published pages (still findable through `Index_c`) and unpublished ones; `key_c[g]` tells them apart.
- One key may map to several pages of the class. At each hit position, `attach` prefers a candidate with `ref > 0`; otherwise it reactivates a candidate with `ref = 0`.
- Entries are removed when `key_c` is revoked (C1/C2 fresh allocation, slab reclaim, I7). `release` does not remove entries (C5).
- The total number of entries is ≤ `|U_c|`, and a key whose candidate set becomes empty keeps no stored entry (I11).

**Pending.** `Pending : Map<TicketId, PendingRec>`. `dom(Pending)` corresponds both ways to `Req[·].pending` (I9):

```
PendingRec = {
  lease : Handle,          // h
  a     : Nat,             // c_h when the ticket was issued
  z     : Nat,             // a + n
  plan  : ExecutionPlan,   // the immutable plan returned by begin_write
}
```

`plan` contains at least `ticket`, `h`, `B`, `input_ids = T_h[a:z]`, `positions = [a..z-1]`; for each `c ∈ Cp`, `write_slots_c = [slot_c(h,j) | j in [a,z)]` and the page mapping of class c for `[0,z)`; for each `c ∈ Cs`, the live slot `σ_h^c` and `init = (a = 0)`. Calls are single-threaded (E3), and `extend`/`release` are forbidden while a ticket is pending (I9). So `T_h`, every `M_h^c`, every `σ_h^c` and the page-table contents do not change while a ticket is live, and no extra version number is needed. Derived invariant:

```
Req[h].pending = Some t  ⇔  t ∈ dom(Pending) ∧ Pending[t].lease = h
t ∈ dom(Pending)  ⇒  c_h = Pending[t].a  ∧  T_h, M_h^c, σ_h^c unchanged since the ticket was issued
```

`finish_write` accepts only `t ∈ dom(Pending)` with a matching binding. Atomically, it removes the entry, clears `Req[h].pending`, sets `c_h = z`, updates the ghosts `V_c` and `W_c`, publishes the newly completed blocks in every paged class, and updates every `Index_c`. A completion event is consumed only once.

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

## 4. Global invariant Valid(S)

The following properties hold after construction and on return from every public method. Each invariant stated for pages, `ref`, `key`, `F`, `Index`, `V` holds separately in every paged class `c ∈ Cp`, with `PageId` replaced by `U_c`.

**I1 Unit domain and page tables.** All unit ids of class c are in `U_c`. Each active lease's page table in every paged class has no duplicates; `L_h >= 1`, `Fits(m_h)`, and `|M_h^c| = m_h` for every `c ∈ Cp`.

**I2 Exact references.** For every class c and unit g:

\[
ref_c[g]=|\{h\in dom(Req): g\in set(M^c_h)\}| \quad (c \in Cp), \qquad ref_c[g]=|\{h\in dom(Req): \sigma^c_h = g\}| \quad (c \in Cs).
\]

Negative counts, missing references and extra references are all forbidden. The count is the number of lease references. A pending ticket protects its units because its lease cannot be released, not by inflating this count.

**I3 Exact free set.** `g ∈ F_c ⇔ g ∈ U_c ∧ ref_c[g] = 0`. A referenced unit is never reallocated as a writable unit. Free only means reclaimable; it must not be read as "the data is gone" or "zeroed".

**I4 Valid frontier.** `0 <= c_h <= L_h`. For every `c ∈ Cp` and `j < c_h`, `V_c[slot_c(h,j)]` corresponds to `Namespace, T_h[0:j+1]`. This is a KV provenance property; floating-point numerical correctness is the executor's external spec.

**I5 Published cache is genuine.** When `key_c[g] != None`, there exist `q >= 1` and a prefix `τ` of length `qB` such that `den(key_c[g]) = (ns, τ)` and page g of class c holds valid KV for the last complete block of `τ`. A key identifies one definite logical block position and context.

For any active lease h that references a published page g of class c, if `M_h^c[i]=g` then also `key_c[g]=K(h,i)` and `c_h >= (i+1)B`. This applies to pages with ref=1 too, so a request never writes over one of its own published pages as if it were an uncomputed tail.

**I5b Complete implies published.** For every active lease h, `c ∈ Cp` and `i < m_h`, if `(i+1)B <= c_h` then `key_c[M_h^c[i]] = K(h,i)`. I5 only gives "published ⇒ correct"; I5b gives the converse. This makes D8's "lookup is complete" a property of the state, rather than a conclusion that needs replaying history.

**I6 Shared means read-only.** If `ref_c[g]>1`, then `c ∈ Cp` and g has a published key. For every referencing lease h, that key equals `K(h,i)` for g's position i in h, and `c_h >= (i+1)B`. So no referencing lease ever writes to g as if it were an uncomputed tail.

**I7 No overwrite after publication.** A page with a non-empty key must not be overwritten in place by any write plan. A new round of writes may start only once `ref_c[g]=0` and the key and index entry have been revoked, either because the page was chosen as a new page or because its slab was reclaimed and given out again.

**I8 Index consistent both ways.** `Index_c[K] = {g | key_c[g]=K}`. Invalidated pages are not found; published candidates whose page was not reused and whose slab was not reclaimed are found. Under E8, equal digests are treated as equal prefixes, so candidates in `Index_c[K]` need no token-by-token comparison. A key whose candidate set is empty has no stored entry in the concrete representation (I11).

**I9 In-flight protection.** Each active lease has at most one pending ticket, and a request's pending field and the Pending table correspond both ways.
- A ticket is bound to a real lease, an input snapshot, and the interval `[a,z)`, with `a=c_h` and `0<n=z-a<=L_h-c_h`.
- The units it needs, in every class, stay referenced until completion.
- Every pending write plan lies within the valid slot range of each class, and its write pages are exclusive and unpublished; its state slots are the lease's own live slots.
- Different tickets' write slots do not overlap in any class, and their state slots differ.
- While a ticket is live, `T_h`, every `M_h^c` and every `σ_h^c` do not change and `c_h = a` (derived invariant, see §3.4).

**I10 Immutable configuration.** N, S, the class table (`Cp`, `Cs`, every `u_c`), B and Namespace do not change during the coordinator's lifetime; all addresses in execution plans are computed with this instance's values.

**I11 Bounded metadata.** The element count of every metadata container is bounded by the fixed configuration, independent of how many operations have been performed:

- `|dom(Req)| <= N · min_c n_c`;
- `|dom(Pending)| <= |dom(Req)|` (at most one ticket per lease, I9);
- per paged class, the number of stored `Index_c` entries, however the representation groups keys, is at most `|{g | key_c[g] != None}| <= |U_c| <= N·n_c`; an entry exists only for a non-empty candidate set;
- for every lease and `c ∈ Cp`, `|M_h^c| <= N·n_c`, and `Fits(m_h)` bounds `L_h`;
- per-unit state (`ref_c`, `key_c`, membership in `F_c`) has exactly `N·n_c` slots per class, and `owner` has exactly N.

**I11a Distinct last pages and slots** (supporting fact). For distinct active leases `h != h'` and every `c ∈ Cp`, `M_h^c[m_h-1] != M_{h'}^c[m_{h'}-1]`. A lease's last page is always a fresh page taken from `F_c`: attach takes it fresh because `k* <= m-1`, and extend either adds fresh pages or keeps the old last page. Page-table entries never change afterwards. For every `c ∈ Cs`, `σ_h^c != σ_{h'}^c` by I2 and I14. So `|dom(Req)| <= |U_c| <= N·n_c` for every class.

I11 bounds element counts. Total token storage is therefore at most `|dom(Req)| · max{L | Fits(ceil(L/B))}` tokens, because each lease keeps its full input. Whether byte-level memory is bounded additionally depends on the runtime's containers using memory proportional to their peak element count, which is outside the proof.

**I12 Slab ownership.** `owner : SlabId -> Classes ∪ {Free}` is total, and `FS = {s | owner[s] = Free}`. Every slab has exactly one owner or is free.

**I13 Confinement.** For every class c and unit `g ∉ U_c`: `ref_c[g] = 0`, `g ∉ F_c`, and (paged) `key_c[g] = None` and g is in no `Index_c` entry, or (state) `W_c[g] = ⊥`. Every page-table entry, live slot, key, Index candidate and pending write of class c lies in `U_c`.

**I14 Live state slots.** For every `c ∈ Cs` and active lease h, `σ_h^c ∈ U_c` and `ref_c[σ_h^c] = 1`. Distinct leases have distinct slots. A state class has no keys and no Index.

**I15 State provenance.** For every `c ∈ Cs` and active lease h: if `c_h > 0` then `W_c[σ_h^c] = (Namespace, T_h[0:c_h])`. If `c_h = 0`, no claim is made about the slot's contents; the next plan carries `init` (C3, E10).

**Arena disjointness** (theorem, from A1 and I12). For any two distinct pairs `(c,g) ≠ (c',g')` with `g ∈ U_c` and `g' ∈ U_{c'}`, the byte ranges `[g·u_c, (g+1)·u_c)` and `[g'·u_{c'}, (g'+1)·u_{c'})` are disjoint. Within one class, distinct ids are disjoint. Across classes, the units lie in different slabs (I12) and each unit lies inside its own slab (A1). Together with I6, I9 and I14, this gives: no planned write touches a published page, a shared page, another lease's state slot, or another class's unit.

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

### C0. create(N, S, classes, B, Namespace) -> Result<Coordinator>

`classes` is an ordered list of `(kind ∈ {Paged, State}, u_c)`.

**Success:** the configuration is fixed; every slab is free; Req, Pending and every `Index_c` are empty; every unit of every class has ref=0, key=None and `W = ⊥`; every `U_c` and `F_c` is empty; Valid holds.

**Failure:** return an explicit ConfigError and produce no usable coordinator if `N`, `S` or `B` is non-positive; there is no paged class; some `u_c` is non-positive; **some `u_c` does not divide `S` (A1)**; or the configuration cannot be safely represented in machine integers (including `N·S` and `N·n_c·B`).

### C1. attach(T) -> Result<(Handle, cached_tokens, LeaseView)>

Purpose: handle a request for the first time, or re-acquire resources from the retained full input after a request was preempted and released.

**Valid input:** T is a non-empty sequence of valid tokens with `Fits(ceil(L/B))`, and its Namespace is this coordinator's fixed configuration. An input that is too large returns RequestTooLarge; an invalid or empty sequence returns InvalidArgument.

**Exact definition of prefix and capacity:** let `m=ceil(L/B)`. Computed from the pre-call state:

\[
k^*=\begin{cases}0 & \text{if } Cs \ne \varnothing,\\ \max\{k\in[0,m-1]\mid\forall c\in Cp,\ \forall i<k,\ Index_c[K(h,i)]\ne\varnothing\} & \text{otherwise.}\end{cases}
\]

`K(h,i)` is computed incrementally along the §3.3 chain, starting from `Seed(ns)`. The tail block has no key, so the upper bound `m-1` agrees with "the last block is recomputed". The first case is D13: there are no state checkpoints, so no prefix can be resumed. (A future version replaces it with "and a state checkpoint at `kB` exists".)

For `c ∈ Cp`, let `r_c` be the number of the k* prefix positions that have at least one candidate in `Index_c` with `ref>0`. Demand and protected slabs:

\[
\begin{aligned}
d_c &= m-r_c \quad (c\in Cp), \qquad d_c = 1 \quad (c \in Cs),\\
Prot &= \{ slab_c(g) \mid c\in Cp,\ i<k^*,\ \text{no candidate of } Index_c[K(h,i)] \text{ has } ref>0,\ g\in Index_c[K(h,i)] \}.
\end{aligned}
\]

`Prot` holds the slabs of the free candidates this call may reactivate. It depends only on the pre-call state and T, so a call never reclaims a cache entry it is about to hit. With `Cs ≠ ∅`, `k* = 0` and `Prot = ∅`.

**Success if and only if:** for valid input with the handle space not exhausted, attach must succeed when `Cap(d, Prot)` holds and must return NoCapacity otherwise. It must not return NoCapacity because of a poor candidate, donor or slab choice when a feasible plan exists. When the handle space is exhausted it returns `IdentifierExhausted` (consistent with C3), and the state is unchanged.

**Postconditions on success:**

- The slab plan of §3.5 is performed for `(d, Prot)`.
- Returns a fresh valid handle h with `T_h=T`, `c_h=k^*B`, no pending ticket, `|M_h^c| = m` for every `c ∈ Cp`, and one live slot `σ_h^c` for every `c ∈ Cs`.
- For `c ∈ Cp` and `i<k*`, the page-table entry is chosen from the corresponding pre-call `Index_c`. If a referenced candidate exists it is chosen; otherwise a free cached candidate is reactivated.
- For `c ∈ Cp` and `i>=k*`, distinct free pages of class c are allocated; these pages must not overwrite the cache-hit pages chosen in this call.
- For `c ∈ Cs`, `σ_h^c` is a fresh unit taken from `F_c`, with `ref_c = 1`; its contents are unconstrained (`W_c = ⊥`).
- Every old reference count increases by exactly one for each new page-table entry or slot that refers to it. Units taken from `F_c` are removed from it.
- The old keys of pages newly allocated as writable are revoked, and their `Index_c` entries correctly removed. Hit pages' keys and KV are unchanged.
- Other active leases' contents, valid KV and live state are unchanged. The returned LeaseView is an immutable snapshot; later extend calls do not change a view already returned.

The demand formula distinguishes reusing an active page from reusing a free cache page: the former saves one free-unit slot, the latter still consumes one. Finding a cache hit does not mean no physical capacity is needed.

attach does not implicitly preempt other requests, does not evict referenced units, and does not advance GPU computation. Which free page or slab is evicted is not part of this contract, except that reclaim happens only when free slabs do not suffice.

### C2. extend(h, suffix) -> Result<LeaseView>

Purpose: append the tokens that need computing next to a lease, and atomically reserve their capacity.

**Calling phase:** h is valid, has no pending ticket, and `c_h=L_h`, i.e. the current input is fully computed. Returns InvalidPhase if the input is not fully computed, and Busy if a ticket is in flight. suffix is non-empty with valid tokens; the existing prefix may not be modified.

Let the old length be L and the old block count m, `L'=L+|suffix|`, `m'=ceil(L'/B)`. Demand: `d_c = m'-m` for `c ∈ Cp`, `d_c = 0` for `c ∈ Cs`; `Prot = ∅`.

**Success if and only if:** in a valid phase with `Fits(m')`, extend succeeds if and only if `Cap(d, ∅)`. `¬Fits(m')` returns RequestTooLarge. Insufficient space returns NoCapacity, with the old input, page tables and slab ownership unchanged.

**Postconditions on success:**

- The slab plan of §3.5 is performed for `(d, ∅)`.
- `T'_h=T_h ++ suffix` and `c'_h=c_h`; the old input prefix is unchanged.
- For every `c ∈ Cp`, the old page table remains a prefix of the new one; exactly `d_c` new distinct free pages are added, each with ref=1 and key=None.
- State slots are unchanged.
- Existing KV, live state, published keys and other requests are unchanged; any cache identity the newly occupied pages had is correctly revoked.
- extend does not look up the prefix cache for the new suffix and does not copy shared pages. If the old tail block still has unused slots, it must be exclusive and unpublished in every paged class, and later writes may use those slots.

If the final sampled token does not need to be fed to the model again, the scheduler can record the output and release without calling extend. If extend fails, the caller must keep the external token and choose a strategy such as waiting or preemption; this module neither drops nor resamples it.

### C3. begin_write(h,n) -> Result<(Ticket, ExecutionPlan)>

Purpose: produce an immutable execution plan for one chunk or one decode step, covering every class, and mark its resources as in flight.

**Valid call:** h is valid, has no pending ticket, and `0<n<=L_h-c_h`. No remaining input or an out-of-range n returns InvalidArgument; an existing pending ticket returns Busy.

If the implementation runs out of fresh ticket ids, it returns IdentifierExhausted with the state unchanged; it must never wrap around and accept old tickets.

Let `a=c_h` and `z=a+n`.

**Postconditions on success:**

- Returns a fresh ticket bound to h, the input snapshot, and the interval `[a,z)`.
- `input_ids=T_h[a:z]` and `positions=[a,...,z-1]`.
- For every `c ∈ Cp`: the write slot for each position j is exactly `slot_c(h,j)`. There are n slots, distinct and within `[0, N·n_c·B)`, and every write page is exclusive and has no published key. The plan lists the class's page mapping for the needed context `[0,z)`. The old prefix `[0,a)` is already valid; the read dependencies of the new interval are satisfied by the executor's causal computation semantics.
- For every `c ∈ Cs`: the plan names `σ_h^c` and `init = (a = 0)`. When `init` is false, the slot holds the state after `T_h[0:a]` (I15). The executor reads it, and leaves the state after `T_h[0:z]` in the same slot.
- The coordinator records the pending ticket; slab ownership, page tables, slots, ref, F, key, Index and c are unchanged. "Submitted" must not be counted as "completed".

A plan is a data and metadata commitment; it does not prove the GPU has executed it. A CPU adapter must not recompute addresses with a different B or unit size, or modify the plan.

### C4. finish_write(ticket, completion) -> Result<ComputedFrontier>

Purpose: after a computation has really completed, advance the valid frontier and publish newly completed blocks.

**Protocol condition:** ticket is a currently valid pending ticket of this coordinator. An unknown, expired or reused ticket, or one belonging to another coordinator, returns InvalidTicket without changing state.

**External premise Completed(ticket):** the completion comes from the executor and confirms three things: the reads and writes for this ticket have finished in every class, they used the planned inputs and addresses, and the new KV and state satisfy the executor spec. How this fact is obtained from CUDA/NCCL is not proved by this module. A bool supplied arbitrarily by a caller must not be treated as proof of physical completion.

**Postconditions on success:**

- For the bound lease h, `c'_h=z`, and the pending ticket is consumed exactly once; the input, page tables and slots are unchanged.
- For every `c ∈ Cp`, in ghost `V_c`, the provenance of `[a,z)` matches the ticket's fixed prefix; other valid slots are unchanged.
- For every `c ∈ Cs`, `W_c[σ_h^c] = (Namespace, T_h[0:z])`.
- For every `c ∈ Cp` and every newly completed whole block i with `a<(i+1)B<=z`, `K(h,i)` is published on `M_h^c[i]` and `Index_c` updated; partial blocks must not be published. `K(h,i)` is computed once per block, sequentially from the chain head (the key of the last published complete block, or `Seed(ns)`), and used for every paged class. The chain head can be kept as the key at block `floor(c_h/B)-1`, but that is an implementation detail.
- Slab ownership, existing read-only cache pages, ref, F and other requests' state are unchanged. When different pages of one class have the same key, the index keeps all candidates.

This version assumes writes always succeed (E4), so there is no "failed completion" branch and no abort; `finish_write` handles only successful completion. An executor that cannot guarantee this must first stop the affected execution and prove that doing so is safe; that is a future extension.

### C5. release(h) -> Result<TokenSnapshot>

Purpose: release all of a lease's references when its request finishes or is preempted.

**Valid call:** h is valid and has no pending ticket. A pending ticket returns Busy; an invalid handle returns InvalidHandle, and a repeated release must not decrement references a second time.

**Postconditions on success:**

- Returns the full input snapshot held by the lease, so the caller can keep the request's logical state; the user's output sequence is not deleted or modified.
- Removes h from Req, permanently invalidating h.
- For every `c ∈ Cp`, decrements `ref_c` exactly once for each g in the original page table. Pages whose count reaches 0 enter `F_c`; pages still referenced elsewhere do not.
- For every `c ∈ Cs`, `ref_c[σ_h^c]` drops to 0 and the slot enters `F_c` with `W_c = ⊥`.
- Published keys, every `Index_c` and KV are kept for later reuse; unfinished partial blocks still cannot be cache hits.
- Slab ownership is unchanged; a slab whose units all become free stays with its class and becomes reclaimable (D11).
- Other active leases' inputs, page tables, slots, valid frontiers and pending tickets are unchanged. Release itself does not zero KV or state, does not evict active units, and does not decide scheduler state.

After release, the same business request can attach again with the returned T and obtain a new handle; this is the preemption recovery path. With `Cs ≠ ∅` it restarts from `c = 0` (D13).

### C6. inspect(h) -> Result<LeaseView> (read-only helper)

Returns the input length, computed frontier, an immutable view of each paged class's page table, each state class's slot, pending status, and this instance's B. No side effects.

If the optional `slot_of(c, h, j)` is provided, it only guarantees the correct allocated token-slot index for `c ∈ Cp` and `0<=j<L_h`; only for `j<c_h` may it also claim that the slot's KV is valid. Invalid handles, classes or indices return explicit errors.

v0.3 does not require can_allocate/can_append. If a preview is added later, it may only be read-only advice or a plan bound to a state version; it cannot unconditionally guarantee that it will still be executable after later state changes.

### C7. arena() -> ArenaView (read-only helper)

Returns `owner[s]` for every slab, and `|F_c|` and `|R_c|` (with `Prot = ∅`) for every class. No side effects. It is observability for the scheduler, not a reservation.

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

## 8. Mapping from upstream methods and intentional changes

| Upstream interface | Draft interface | Change |
|---|---|---|
| BlockManager constructor | create | Fixes the arena, the class table and B, checks A1, and validates the representation range |
| can_allocate + allocate | attach | One atomic operation across every class; does not depend on an externally supplied num_cached_blocks |
| Sequence.append_token + can_append + may_append | extend | Grows the input snapshot and capacity atomically; needs a scheduler adapter |
| seq.num_scheduled_tokens and runner preparation | begin_write | Produces an address plan for every class consistent with the instance, and records in-flight protection |
| hash_blocks + updating num_cached_tokens | finish_write | Commits the frontier, state provenance and cache publication together after completion |
| deallocate | release | Release while in flight is forbidden; invalidated handles prevent double release |
| compute_hash | Cache identity | Chained 256-bit digest, both identity and index key, shared by every paged class; enters via the collision-resistance assumption E8 (§9) |
| kvspec `layout()` → `PhysicalPlan.paged.stride` / `.state.stride` | `u_c` of a paged / state class | The planner still decides bytes inside a unit; this contract decides which unit |
| kvspec `plan()` pool counts (`slots = ceil(slot_ratio · max_num_seqs)`, rest to blocks) | slab arena | The static split between blocks and state slots is replaced by on-demand slabs |
| `get_num_state_slots(max_num_seqs)` | state class units on demand | No fixed slot count; a slot exists for each lease that holds one |
| `KVCacheManager._view` over `[num_blocks, stride]` / `[num_slots, stride]` buffers | one arena viewed as `[N·n_c, u_c]` per class | Valid by A1; the views alias the same arena but distinct units never overlap (arena disjointness) |
| kvspec `Static` pool | outside the arena | Non-goal (§1.1) |

This is a new interface designed for a provable implementation; it cannot replace the old object without adaptation. In particular, `Sequence` may no longer hold an authoritative page table, state slot or cache frontier that can be modified independently. If a mirror is needed, it may only be exported from the core, and the adapter must be proved to use a consistent version.

## 9. Proofs the implementation must deliver

### 9.0 Main theorem and external assumptions

**Main theorem.** At every step of any valid trace, if the executor executes the plan returned by `begin_write`, then:

(a) for every `c ∈ Cp`, the plan's write slots are exactly `slot_c(h,j)` (`j in [a,z)`), distinct and within `[0, N·n_c·B)`; for every `c ∈ Cs`, the plan's slot is `σ_h^c`;
(b) every slot of `[0,a)` corresponds in ghost `V_c` to `(Namespace, T_h[0:j+1])`, and, if `a > 0`, `W_c[σ_h^c] = (Namespace, T_h[0:a])`;
(c) after `finish_write`, every slot of `[a,z)` is updated to its corresponding prefix, every state slot holds `(Namespace, T_h[0:z])`, and every newly published block i satisfies `den(key_c[M_h^c[i]]) = (Namespace, T_h[0:(i+1)B])`;
(d) the bytes the plan writes are disjoint from every published page, every shared page, every other lease's units, and every other pending plan's writes (arena disjointness);
(e) `Valid(S)` is preserved, each method's frame conditions hold, and error paths satisfy the strong failure atomicity of §5 item 3.

**External assumptions.** The following are not proved, but they must be listed and checked along the verified call chain. E8 is the only cryptographic assumption in this version. A1 is not an assumption: create checks it.

| ID | Assumption | Consequence if violated |
|---|---|---|
| E1 | Completion events are real: the executor confirms the reads and writes are done in every class and used the planned inputs and addresses | The frontier advances over unwritten or wrongly written KV or state |
| E2 | KV and state depend only on the prefix: values are independent of batch composition and chunking (within tolerance). For recurrent state this includes chunked versus step-by-step computation | The ghosts `V_c` of shared pages, or `W_c`, no longer hold |
| E3 | Calls are single-threaded and sequential (or serialized by the caller) | The invariants break under concurrency |
| E4 | Writes always succeed: every issued ticket eventually completes successfully; no failed completion, silent drop, or process termination | Pending never clears, and units stay occupied forever |
| E5 | The executor uses the planned slots, state slots, the instance's B and every `u_c`, and does not recompute addresses | Writes to the wrong unit, slot or class |
| E6 | The Namespace is complete: the final field table covers weights, dtype, B, every class's kind, `u_c` and in-unit layout, rope/scaling, attention semantics and adapters; v0.3 uses a dummy byte string, and completeness is the caller's responsibility | Different semantics share keys, causing silent wrong reuse |
| E7 | `Canon`/`Enc` follow the §3.3 canonical encoding: fixed-width uint32 tokens, length-prefixed fields, fixed field order, domain separation | Structural collisions (probability 1) that E8 cannot cover |
| E8 | SHA-256 is collision resistant; the collision probability over `Q` key generations/comparisons during the deployment is `<= Q^2/2^257 + Q/2^256` | Wrong KV reuse across requests (a data leak under multi-tenancy) |
| E9 | The arena is one allocation of at least `N·S` bytes whose base is aligned to every class's required alignment (kvspec `Pool.align`), and every kernel addresses unit g of class c at `base + g·u_c` plus the kvspec region offset | Units of different classes alias, or kernels read misaligned or wrong bytes |
| E10 | When a plan has `init = true` for a state slot, the executor sets the slot to the model's initial state before reading it; it writes state only to the planned slot | A lease starts from another lease's leftover state |

### 9.1 Proof obligations

1. **Initialization:** Valid holds after a successful create, and create returns ConfigError exactly in the cases listed in C0.
2. **Per-method preservation:** for every real method body, prove that Valid is preserved, together with C0–C7's functional, error and frame conditions.
3. **Allocation sufficiency:** attach's k*, `r_c`, `d_c` and `Prot` match their definitions; with correct candidate choice, `Cap` guarantees success.
4. **Addressing and isolation:** slot range per class, no aliasing within a request, no conflicts between pending writes, distinct live slots, and shared pages are never written.
5. **Cache soundness:**
   - the canonical chained-key implementation (`Canon`/`Enc`/`Tag`/domain separation) is consistent with every `Index_c` in both directions;
   - the publication condition is correct in every paged class;
   - a page's identity is revoked before it is written for a new use, whether by fresh allocation or slab reclaim;
   - the chain lemma (§3.3) is proved in the ideal hash model, with E8 as the only cryptographic assumption for the concrete instance.
6. **Protocol correctness:** handle/ticket invalidation, single consumption of completions, and in-flight units are never reclaimed. Prove that the executor-interface premises hold along the verified call chain, or list them as explicit external assumptions (E1, E2, E5, E9, E10).
7. **Termination and representation:** all loops terminate; machine-integer, array and set operations are safe; a verifier UNKNOWN or timeout is not a pass.
8. **Deployment link:** run the verified implementation or its trusted compiled output. A hand-rewritten version does not automatically inherit the proof. The digest implementation and the canonical `Canon`/`Enc` must match the proof's definitions byte for byte.
9. **Bounded metadata:** prove that every method preserves I11 (with I11a), so metadata stays O(Σ_c N·n_c) for traces of any length.
10. **Arena disjointness:** prove the theorem of §4 from A1 and I12, and that every unit address in a plan lies in `[0, N·S)`.
11. **Capacity exactness:** `Cap(d, Prot)` holds iff a slab plan following §3.5 rules 1–4 exists; the implementation acquires exactly `need_c` slabs per class, uses `FS` before reclaiming, never reclaims a slab in `Prot` or with a referenced unit, and never takes units from a slab it gave up in the same call.
12. **Reclaim correctness:** reclaiming a slab preserves I3, I8, I11 and I13, revokes every key in it, and changes nothing outside that slab's units and `owner`.
13. **Cross-class atomicity:** on every error path of attach and extend, slab ownership and every class's state are unchanged; on success, no lease has resources in some classes but not others (I1, I14).
14. **Refinement of v0.2.1:** with `|Cp| = 1` and `Cs = ∅`, every public method's observable behavior (results, errors, k*, cached tokens, plans up to page renaming) equals v0.2.1 with `P = N·n_c`, treating units of free slabs as unkeyed free pages. This lets the v0.2.1 proofs be reused for the paged class.

### 9.2 Trusted base

1. E8 (SHA-256 collision resistance and the ε bound);
2. E6 (Namespace completeness) and E7 (canonical encoding): design obligations, not probabilistic assumptions;
3. trusted compiled output (§9.1 item 8);
4. E1/E2/E5/E9/E10 (executor and arena interface). E3/E4 are deployment assumptions (single thread, writes always succeed) and do not enter the method-body proofs.

Auxiliary lemmas, loop invariants and data structures may be designed by the agent. But new assumes, axioms, skipped function bodies, or weakened pre/postconditions must not be used to pass off a proof as complete. E1–E10 are explicitly listed external assumptions and must not become a loophole for new assumes.

Implement and prove in steps: first the slab arena with one paged class, and obligation 14 against the existing v0.2.1 proof; then several paged classes with per-class Index and `Cap`; then state classes and cross-class atomicity; finally the ticket/completion protocol across classes and the Python runner adapter. Each step keeps the same external functional goals; deferred properties must not be counted as proved.

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

Still open (must be decided in a later version or before implementation):

- State checkpoints and joint prefix hits: checkpoint units keyed by `K(h,i)` at grain boundaries (DeepInfer stores state only at multiples of `KVSTORE_GRAIN`), the `on_hit` modes `restore` / `replay` / `empty`, the copy from checkpoint to live slot in the plan, and the joint `k*` rule.
- Guidance on slab size when the LCM of unit sizes is large: how much padding of `u_c` (kvspec `stride_align`) is acceptable.
- Several paged classes with different B (e.g. different lifetimes), and how hits align across them.
- Reclaim policy among reclaimable slabs (e.g. fewest keyed pages first), and whether an explicit trim operation that returns idle slabs is useful.
- The real Namespace field table (E6), its alignment with `Engine.store_identity()`, and how it encodes the kvspec plan of every class.
- Whether to share identity with `prefix_keys` in `shell/offload.py`. Sharing requires aligning the Tag, the namespace fields and `grain == B`; otherwise the contract should state explicitly that there are two separate schemes.
- Primitives for speculative decoding and offload (`truncate`/`commit`, `adopt`).
- Static caches inside the arena.
- The verification toolchain and repository name (outside this document).

One more explicit boundary: this draft proves resources, provenance, addresses and protocol. Whether the GPU actually completed according to plan, and whether the KV and state values are numerically correct, need a separate executor contract. That boundary cannot be treated as proved just by assigning values to the ghosts `V_c` and `W_c`.
