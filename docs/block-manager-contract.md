# Block Manager Functional Contract v0.2.1 (draft)

Status: specification draft for review. v0.2.1 is v0.2 plus invariant I11 (bounded metadata).
It is implemented and verified in this repository; see `SPEC_NOTES.md`.
Date: 2026-11-03 (v0.2: 2026-11-02; v0.1: 2026-11-01).
Reference code: nano-vLLM `bb823b3e06983d71485a8e1f23715ebd87d98ef8`: `block_manager.py`, `sequence.py`, `scheduler.py`; `prefix_keys` in `shell/offload.py` (the existing implementation of chained keys).

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

This module is responsible for: physical KV page allocation, request page tables, whole-block prefix reuse (keyed by chained digests), capacity growth, the computed frontier, page protection during execution, cache publication, and reference release.

The following semantics belong to other modules: choosing which requests to schedule each step, prefill/decode priority, token budget, EOS and max_tokens, the model's context limit, numerical correctness of the model, and GPU kernels and communication. The block manager does not modify this business state.

The module guarantees that the page tables and slot plans it outputs conform to this contract; the external executor must execute according to the plan. The correctness guarantees hold only given a fixed KV namespace, valid external completion events, and a correct executor.

Each manager owns its own physical pool; external code cannot bypass it to overwrite completed KV or reuse its pages. Multiple managers need separate physical pools; a protocol for several managers sharing one pool is out of scope for this draft.

### 1.1 Explicit non-goals and write assumption for v0.2

The following capabilities are not in this draft's state machine. Callers must handle them separately and must not treat them as proved properties:

- Partial commit for speculative decoding, and truncation of rejected drafts: `finish_write` only advances the frontier to the ticket's `z`, and `extend` only appends, so tokens of a rejected draft cannot be removed from `T_h`. The existing shell's `spec_decode` (`docs/spec/shell.md` §1.9) needs additional primitives.
- External KV import (adopt) for offload/store: the only way to advance `c_h` is the executor's completion event for a ticket. The `restore_prefix` path needs additional primitives.
- Multi-threaded concurrent calls: see the single-thread assumption E3 in §5.

This version **assumes writes always succeed** (E4): every issued ticket eventually completes successfully, with no failed completion, silent drop, or process termination. There is therefore no abort/rollback path, and no promise of progress under GPU faults (see C4).

Until these primitives exist, an adapter must not claim to cover every feature of the existing scheduler (in particular `spec_decode` and `store`).

## 2. Design decisions adopted in this version

| ID | Draft default | Rationale or cost |
|---|---|---|
| D1 | Each manager fixes `P`, `B` and the KV namespace; there is no globally mutable block size | Multiple processes or instances do not depend on one implicit global value |
| D2 | attach reserves pages for all current input tokens | Keeps upstream's eager allocation; chunked prefill only advances the computed frontier |
| D3 | Reuse only a contiguous prefix of completed whole blocks; attach always leaves the last logical block for recomputation | Keeps upstream's convention for computing the first output; the last block is excluded even when the input length is an exact multiple of B |
| D4 | Cache hits are decided by chained 256-bit digest identity; the digest is also the index key | The key is a chain `H(parent, block)`, O(1) per block. Identity exactness rests on "SHA-256 is collision resistant" as an explicit probabilistic assumption (E8). No 64-bit practical hash, and no per-candidate exact comparison |
| D5 | Complete prefixes may be shared read-only; pages being written must be exclusive; no COW in this version | Writes the boundary between sharing and writing into the spec |
| D6 | The core interface uses atomic `attach` / `extend` that check capacity and mutate together | Avoids relying on possibly stale can_allocate/can_append results |
| D7 | `begin_write` / `finish_write` make in-flight work explicit; in-flight requests cannot extend or release | Protects pages through a metadata protocol; whether the GPU actually completed remains the executor's responsibility |
| D8 | Keep every published cache entry whose page has not actually been reused; lookup is complete and the hit prefix is the longest | An explicit cache-functionality promise, stronger than upstream's single-valued hash index; can be implemented as a multi-candidate index |
| D9 | Free-page choice, eviction order, and page choice among equal keys are not fixed; when a referenced hit candidate exists, it is preferred | Leaves room for optimization and ensures no spurious failure when resources suffice |

D1–D9 are proposed semantics, not claims that upstream already satisfies them. D4 and D6–D8 in particular require changes to the implementation and interface; this draft does not promise function-by-function compatibility with the old API.

## 3. Abstract state

### 3.1 Fixed configuration

- `P >= 1`: number of physical pages, `PageId = {0,...,P-1}`.
- `B >= 1`: token slots per physical page.
- `Namespace`: the configuration identity that decides cache reusability, an opaque byte string. The final field table should cover model and weight version, adapters, positional encoding/scaling, attention semantics (including sliding window), B, and KV dtype and layout, and should align with `Engine.store_identity()`. v0.2 starts with a dummy (an implementation may pass a fixed string such as `"dummy-v0.2"`). Completeness remains the caller's obligation (E6); the field table is deferred to v0.3.
- `Token`: the type of valid token ids; sequences are finite and 0-indexed.

The abstract spec uses mathematical integers. A concrete implementation must prove that machine-integer arithmetic on page ids, lengths, counts and addresses does not overflow, and must reject unrepresentable configurations at construction. Other limits, such as CUDA's current requirement that B be a multiple of some value and its int32 slot limit, must be added explicitly by the corresponding implementation or adapter, never silently ignored.

### 3.2 Mutable state

| Symbol | Meaning |
|---|---|
| `Req[h]` | An attached request lease: the input sequence `T_h` (never modified in place), page table `M_h`, computed frontier `c_h`, and an optional pending ticket |
| `F` | The set of physical pages currently referenced by no request; includes free cache pages that still hold reusable data |
| `ref[b]` | How many active leases reference physical page b |
| `key[b]` | Page b's reusable cache identity (a chained 256-bit digest), or None |
| `Index[K]` | All candidate physical pages whose published key is K |
| `Pending[t]` | A submitted but not yet completed computation: the lease, original frontier `a`, interval end `z`, and execution plan `plan` |
| `V` | Ghost KV-provenance marker used by the proof; records the Namespace and full causal token prefix of each slot |
| `den` | Ghost used by the proof: a partial function from digest to `(Namespace, full causal prefix)`; it gives chained keys their meaning |

The domain of `den` is exactly the chain outputs `{Seed(ns)} ∪ {K(h,i)}`. It is injective in the ideal model, and E8 covers this for the concrete instance. It is not part of the executable state.

Request handles and execution tickets use distinct types that cannot be confused, and are bound to the manager and to their generation. An invalidated handle or ticket can never become valid again on a later object. If a concrete implementation's counter space is exhausted, it must safely reject new operations and never wrap around and reuse ids.

A request in this draft means a block-manager lease, not the scheduler's WAITING/RUNNING/FINISHED state. The scheduler still manages its business requests; releasing a lease does not delete the user request or its output.

### 3.3 Semantic conventions

Let `L_h = |T_h|` and `m_h = ceil(L_h/B)`.

Page-table entry `M_h[i]` is the physical page of logical block i. The slot address of token position j is:

\[
slot(h,j)=M_h[\lfloor j/B\rfloor]\cdot B+(j\bmod B).
\]

`c_h` is the length of the contiguous computed prefix: positions `[0,c_h)` have valid KV, and `[c_h,L_h)` are not all done. Reserved capacity does not mean the KV is valid.

The cache key of logical block i is a chained 256-bit digest. Let `H` be a 256-bit collision-resistant hash (SHA-256 in the implementation), `Tag` the scheme version (e.g. `"mg-block-key-v1"`), `Canon` the canonical encoding of the Namespace, and `Enc` the fixed-width encoding of B tokens:

\[
\begin{aligned}
Seed(ns) &= H(Tag \,\|\, 0x00 \,\|\, Canon(ns))\\
K(h,0) &= H(Tag \,\|\, 0x01 \,\|\, Seed(ns) \,\|\, Enc(T_h[0:B]))\\
K(h,i) &= H(Tag \,\|\, 0x01 \,\|\, K(h,i-1) \,\|\, Enc(T_h[iB:(i+1)B]))
\end{aligned}
\]

**Encoding (E7).** `Canon(ns)` encodes the namespace byte string as `u32 len || ns_bytes`. (In v0.2 the namespace is an opaque byte string; once it has fields, they are encoded in a fixed order, each as `u32 tag || u32 len || bytes`.) `Enc(blk)` writes each of the B tokens as a 4-byte little-endian uint32, concatenated at fixed width: exactly `4B` bytes. The parent digest is always 32 bytes, and `Tag` with `0x00`/`0x01` provides domain separation, so `Tag || 0x01 || parent || Enc(blk)` splits in only one way. This uniqueness does not depend on the hash (E7); the hash is only responsible for E8. Counterexamples: concatenating variable-length tokens directly, joining strings with a separator, or JSON with unspecified key order can each encode two different prefixes to the same byte string. The collision probability is then 1, not `2^-256`.

`K(h,i)` is defined only for complete blocks, `(i+1)B <= L_h`; an incomplete tail block has no key and is never published. A key means the full causal prefix `(Namespace, T_h[0:(i+1)B])`, given by the ghost `den`; the chained construction is only its O(1) representation. Any difference in an earlier block must change every later key. The chain guarantees this; "current-block tokens only", "token hash only" or "same length" are all insufficient.

In the ideal hash model (`H` injective) the chain lemma holds:

\[
K(h,i)=K(h',i') \iff ns=ns' \land i=i' \land T_h[0:(i+1)B]=T_h'[0:(i+1)B].
\]

For the concrete instance (SHA-256) the equivalence holds with probability `>= 1 - \epsilon`, `\epsilon <= Q^2/2^{257} + Q/2^{256}`, where `Q` is the number of key generations and comparisons during the deployment (E8). `den` is injective on chain outputs (ideal model), and E8 likewise covers the concrete instance; hence `den(K(h,i)) = (Namespace, T_h[0:(i+1)B])` is the meaning of a key.

A key lives as long as its page: the digest is stored on the page, and the `Index` entry is removed when the key is revoked. There is no intern table, ancestor chain, or GC. A page that is released but not reused keeps its key (C5), so total metadata is O(P) digests (made precise by I11). The chain head (the key of the last published complete block, or `Seed(ns)`) lets `finish_write` compute the keys of new blocks incrementally; it is an implementation detail.

### 3.4 Representation of Index and Pending

**Index.** `Index : Map<Key, Set<PageId>>`, with `Index[K] = {b | key[b] = K}` (I8).
- It is the inverse relation of `key` and covers only published pages. `F` contains both published pages (still findable through Index) and unpublished ones; `key[b]` tells them apart.
- One key may map to several physical pages. At each hit position, `attach` prefers a candidate with `ref>0`; otherwise it reactivates a candidate with `ref=0`.
- Entries are removed when `key` is revoked (C1/C2, I7). `release` does not remove entries (C5).
- The total number of entries is ≤ P, and a key whose candidate set becomes empty keeps no stored entry (I11).

**Pending.** `Pending : Map<TicketId, PendingRec>`. `dom(Pending)` corresponds both ways to `Req[·].pending` (I9):

```
PendingRec = {
  lease : Handle,          // h
  a     : Nat,             // c_h when the ticket was issued
  z     : Nat,             // a + n
  plan  : ExecutionPlan,   // the immutable plan returned by begin_write
}
```

`plan` contains at least `ticket`, `h`, `input_ids = T_h[a:z]`, `positions = [a..z-1]`, `write_slots = [slot(h,j) | j in [a,z)]`, the page mapping for `[0,z)`, and `B`. Calls are single-threaded (E3), and `extend`/`release` are forbidden while a ticket is pending (I9). So `T_h`, `M_h` and the page-table contents do not change while a ticket is live, and no extra version number is needed. Derived invariant:

```
Req[h].pending = Some t  ⇔  t ∈ dom(Pending) ∧ Pending[t].lease = h
t ∈ dom(Pending)  ⇒  c_h = Pending[t].a  ∧  T_h, M_h unchanged since the ticket was issued
```

`finish_write` accepts only `t ∈ dom(Pending)` with a matching binding. Atomically, it removes the entry, clears `Req[h].pending`, sets `c_h = z`, updates the ghost `V`, publishes the newly completed blocks, and updates `Index`. A completion event is consumed only once.

## 4. Global invariant Valid(S)

The following properties hold after construction and on return from every public method.

**I1 Page domain and page tables.** All page ids are in `[0,P)`. Each active lease's page table has no duplicates; `1 <= L_h <= P*B` and `|M_h| = ceil(L_h/B)`.

**I2 Exact references.**

\[
ref[b]=|\{h\in dom(Req): b\in set(M_h)\}|.
\]

Negative counts, missing references and extra references are all forbidden. The count is the number of lease references. A pending ticket protects its pages because its lease cannot be released, not by inflating this count.

**I3 Exact free set.** `b in F <=> ref[b]=0`. A referenced page is never reallocated as a writable page. Free only means reclaimable; it must not be read as "the data is gone" or "zeroed".

**I4 Valid frontier.** `0 <= c_h <= L_h`. For every `j<c_h`, `V[slot(h,j)]` corresponds to `Namespace, T_h[0:j+1]`. This is a KV provenance property; floating-point numerical correctness is the executor's external spec.

**I5 Published cache is genuine.** When `key[b] != None`, there exist `q >= 1` and a prefix `τ` of length `qB` such that `den(key[b]) = (ns, τ)` and page b holds valid KV for the last complete block of `τ`. A key identifies one definite logical block position and context.

For any active lease h that references a published page b, if `M_h[i]=b` then also `key[b]=K(h,i)` and `c_h >= (i+1)B`. This applies to pages with ref=1 too, so a request never writes over one of its own published pages as if it were an uncomputed tail.

**I5b Complete implies published.** For every active lease h and `i < |M_h|`, if `(i+1)B <= c_h` then `key[M_h[i]] = K(h,i)`. I5 only gives "published ⇒ correct"; I5b gives the converse. This makes D8's "lookup is complete" a property of the state, rather than a conclusion that needs replaying history.

**I6 Shared means read-only.** If `ref[b]>1`, b has a published key. For every referencing lease h, that key equals `K(h,i)` for b's position i in h, and `c_h >= (i+1)B`. So no referencing lease ever writes to b as if it were an uncomputed tail.

**I7 No overwrite after publication.** A page with a non-empty key must not be overwritten in place by any write plan. A new round of writes may start only once `ref[b]=0`, the page has been chosen as a new page, and its key and index entry have been revoked.

**I8 Index consistent both ways.** `Index[K] = {b | key[b]=K}`. Invalidated pages are not found; published candidates that have not been evicted are found. Under E8, equal digests are treated as equal prefixes, so candidates in `Index[K]` need no token-by-token comparison. A key whose candidate set is empty has no stored entry in the concrete representation (I11).

**I9 In-flight protection.** Each active lease has at most one pending ticket, and a request's pending field and the Pending table correspond both ways.
- A ticket is bound to a real lease, an input snapshot, and the interval `[a,z)`, with `a=c_h` and `0<n=z-a<=L_h-c_h`.
- The pages it needs stay referenced until completion.
- Every pending write plan lies within the valid slot range, and its write pages are exclusive and unpublished.
- Different tickets' write slots do not overlap.
- While a ticket is live, `T_h` and `M_h` do not change and `c_h = a` (derived invariant, see §3.4).

**I10 Immutable configuration.** P, B and Namespace do not change during the manager's lifetime; all addresses in execution plans are computed with this instance's B.

**I11 Bounded metadata** (new in v0.2.1). The element count of every metadata container is bounded by the fixed configuration, independent of how many operations have been performed:

- `|dom(Req)| <= P`;
- `|dom(Pending)| <= |dom(Req)|` (at most one ticket per lease, I9);
- the number of stored Index entries, however the representation groups keys, is at most `|{b | key[b] != None}| <= P`; an entry exists only for a non-empty candidate set;
- for every lease, `|M_h| <= P` and `L_h <= P*B` (I1);
- per-page state (`ref`, `key`, `F`) has exactly P slots.

**I11a Distinct last pages** (supporting fact). For distinct active leases `h != h'`, `M_h[m_h-1] != M_h'[m_h'-1]`. A lease's last page is always a fresh page taken from `F`: attach takes it fresh because `k* <= m-1`, and extend either adds fresh pages or keeps the old last page. Page-table entries never change afterwards. So `h -> M_h[m_h-1]` is injective, which gives `|dom(Req)| <= P`.

I11 bounds element counts. Total token storage is therefore at most `P * P * B` tokens, because each lease keeps its full input. Whether byte-level memory is bounded additionally depends on the runtime's containers using memory proportional to their peak element count, which is outside the proof.

## 5. General method conventions

A real implementation must encapsulate its internal state: external code may update it only through the verified methods. `Valid(S)` must not be treated as a condition that an arbitrary external Python caller will always respect voluntarily.

Every method must satisfy:

1. If the entry state is Valid, the state on normal return is also Valid.
2. The method terminates on every finite valid input, with no out-of-bounds access, counter overflow, or unspecified state change.
3. Declared error results are strongly failure-atomic: `S'=S`, including page tables, frontiers, reference counts, the index, pending tickets, and id-allocation state.
4. The inputs, page tables, frontiers and pending tickets of uninvolved leases stay unchanged; existing KV referenced by multiple leases must not change.
5. Externally observable outputs satisfy each method's functional postcondition, not merely "the state is still valid".

These failure-atomicity requirements cover the specified input, capacity and phase errors. Process termination, runtime OOM and hardware faults are outside this version's state-machine promises.

This draft assumes methods are called sequentially on one thread (or serialized by the caller), and claims no multi-threaded linearizability (E3). Computing a chained key is a pure function and modifies no state. `Index` changes only on successful methods. So the strong failure atomicity of item 3 covers page tables, references, `Index` and id-allocation state, with no separate key-store state to cover.

## 6. API contracts

### C0. create(P,B,Namespace) -> Result<Manager>

**Success:** the page universe is fixed; F is all physical pages; Req, Pending and Index are empty; every page has ref=0 and key=None; Valid holds.

**Failure:** if the configuration is non-positive or cannot be safely represented in machine integers, return an explicit ConfigError and produce no usable manager.

### C1. attach(T) -> Result<(Handle, cached_tokens, PageTableView)>

Purpose: handle a request for the first time, or re-acquire resources from the retained full input after a request was preempted and released.

**Valid input:** T is a non-empty sequence of valid tokens with `L<=P*B`, and its Namespace is this manager's fixed configuration. An input that is too long returns RequestTooLarge; an invalid or empty sequence returns InvalidArgument.

**Exact definition of prefix and capacity:** let `m=ceil(L/B)`. Computed from the pre-call state:

\[
k^*=\max\{k\in[0,m-1]\mid\forall i<k,\ Index[K(h,i)]\ne\varnothing\}.
\]

`K(h,i)` is computed incrementally along the §3.3 chain, starting from `Seed(ns)`. The tail block has no key, so the upper bound `m-1` agrees with "the last block is recomputed".

Let u be the number of these k* prefix positions that have at least one candidate with `ref>0`. The minimum number of pages to take from the free set is:

\[
d=m-u.
\]

**Success if and only if:** for valid input with the handle space not exhausted, attach must succeed when `|F|>=d` and must return NoCapacity when `|F|<d`. It must not return NoCapacity because of a poor candidate choice when a feasible plan exists. When the handle space is exhausted it returns `IdentifierExhausted` (consistent with C3), and the state is unchanged.

**Postconditions on success:**

- Returns a fresh valid handle h with `T_h=T`, `|M_h|=m`, `c_h=k^*B`, and no pending ticket.
- For `i<k*`, the page-table entry is chosen from the corresponding pre-call Index. If a referenced candidate exists it is chosen; otherwise a free cached candidate is reactivated.
- For `i>=k*`, distinct free pages are allocated; these pages must not overwrite the cache-hit pages chosen in this call.
- Every old reference count increases by exactly one for each new page-table entry that refers to it. Pages taken from F are removed from it.
- The old keys of pages newly allocated as writable are revoked, and their Index entries correctly removed. Hit pages' keys and KV are unchanged.
- Other active leases' contents and valid KV are unchanged. The returned PageTableView is an immutable snapshot; later extend calls do not change a view already returned.

The capacity formula distinguishes reusing an active page from reusing a free cache page: the former saves one free-page slot, the latter still consumes one. Finding a cache hit does not mean no physical capacity is needed.

attach does not implicitly preempt other requests, does not evict referenced pages, and does not advance GPU computation. Which page is evicted is not part of this contract.

### C2. extend(h, suffix) -> Result<PageTableView>

Purpose: append the tokens that need computing next to a lease, and atomically reserve their capacity.

**Calling phase:** h is valid, has no pending ticket, and `c_h=L_h`, i.e. the current input is fully computed. Returns InvalidPhase if the input is not fully computed, and Busy if a ticket is in flight. suffix is non-empty with valid tokens; the existing prefix may not be modified.

Let the old length be L and the old page count m, `L'=L+|suffix|`, `m'=ceil(L'/B)`, and `d=m'-m`.

**Success if and only if:** in a valid phase with `L'<=P*B`, extend succeeds if and only if `|F|>=d`. `L'>P*B` returns RequestTooLarge. Insufficient space returns NoCapacity, with the old input and page table unchanged.

**Postconditions on success:**

- `T'_h=T_h ++ suffix` and `c'_h=c_h`; the old input prefix is unchanged.
- The old page table remains a prefix of the new one; exactly d new distinct free pages are added, each with ref=1 and key=None.
- Existing KV, published keys and other requests are unchanged; any cache identity the newly occupied pages had is correctly revoked.
- extend does not look up the prefix cache for the new suffix and does not copy shared pages. If the old tail block still has unused slots, it must be exclusive and unpublished, and later writes may use those slots.

If the final sampled token does not need to be fed to the model again, the scheduler can record the output and release without calling extend. If extend fails, the caller must keep the external token and choose a strategy such as waiting or preemption; this module neither drops nor resamples it.

### C3. begin_write(h,n) -> Result<(Ticket, ExecutionPlan)>

Purpose: produce an immutable execution plan for one chunk or one decode step, and mark its resources as in flight.

**Valid call:** h is valid, has no pending ticket, and `0<n<=L_h-c_h`. No remaining input or an out-of-range n returns InvalidArgument; an existing pending ticket returns Busy.

If the implementation runs out of fresh ticket ids, it returns IdentifierExhausted with the state unchanged; it must never wrap around and accept old tickets.

Let `a=c_h` and `z=a+n`.

**Postconditions on success:**

- Returns a fresh ticket bound to h, the input snapshot, and the interval `[a,z)`.
- `input_ids=T_h[a:z]` and `positions=[a,...,z-1]`.
- The write slot for each position j is exactly `slot(h,j)`. There are n slots in total, distinct and within `[0,P*B)`, and every write page is exclusive and has no published key.
- The plan explicitly lists the page mapping for the needed context `[0,z)`. The old prefix `[0,a)` is already valid; the read dependencies of the new interval are satisfied by the executor's causal computation semantics.
- The manager records the pending ticket; page tables, ref, F, key, Index and c are unchanged. "Submitted" must not be counted as "completed".

A plan is a data and metadata commitment; it does not prove the GPU has executed it. A CPU adapter must not recompute addresses with a different B or modify the plan.

### C4. finish_write(ticket, completion) -> Result<ComputedFrontier>

Purpose: after a computation has really completed, advance the valid frontier and publish newly completed blocks.

**Protocol condition:** ticket is a currently valid pending ticket of this manager. An unknown, expired or reused ticket, or one belonging to another manager, returns InvalidTicket without changing state.

**External premise Completed(ticket):** the completion comes from the executor and confirms three things: the reads and writes for this ticket have finished, they used the planned inputs and addresses, and the new KV satisfies the executor spec. How this fact is obtained from CUDA/NCCL is not proved by this module. A bool supplied arbitrarily by a caller must not be treated as proof of physical completion.

**Postconditions on success:**

- For the bound lease h, `c'_h=z`, and the pending ticket is consumed exactly once; the input and page table are unchanged.
- In ghost V, the provenance of `[a,z)` matches the ticket's fixed prefix; other valid slots are unchanged.
- For every newly completed whole block i with `a<(i+1)B<=z`, `K(h,i)` is published and Index updated; partial blocks must not be published. `K(h,i)` is computed sequentially from the chain head (the key of the last published complete block, or `Seed(ns)`). The chain head can be kept as the key at block `floor(c_h/B)-1`, but that is an implementation detail.
- Existing read-only cache pages, ref, F and other requests' state are unchanged. When different physical pages have the same key, the index keeps all candidates.

This version assumes writes always succeed (E4), so there is no "failed completion" branch and no abort; `finish_write` handles only successful completion. An executor that cannot guarantee this must first stop the affected execution and prove that doing so is safe; that is a future extension.

### C5. release(h) -> Result<TokenSnapshot>

Purpose: release all of a lease's references when its request finishes or is preempted.

**Valid call:** h is valid and has no pending ticket. A pending ticket returns Busy; an invalid handle returns InvalidHandle, and a repeated release must not decrement references a second time.

**Postconditions on success:**

- Returns the full input snapshot held by the lease, so the caller can keep the request's logical state; the user's output sequence is not deleted or modified.
- Removes h from Req, permanently invalidating h.
- Decrements ref exactly once for each b in the original page table. Pages whose count reaches 0 enter F; pages still referenced elsewhere do not.
- Published keys, Index and KV are kept for later reuse; unfinished partial blocks still cannot be cache hits.
- Other active leases' inputs, page tables, valid frontiers and pending tickets are unchanged. Release itself does not zero KV, does not evict active pages, and does not decide scheduler state.

After release, the same business request can attach again with the returned T and obtain a new handle; this is the preemption recovery path.

### C6. inspect(h) -> Result<RequestView> (read-only helper)

Returns the input length, computed frontier, an immutable view of the page table, pending status, and this instance's B. No side effects.

If the optional `slot_of(h,j)` is provided, it only guarantees the correct allocated address for `0<=j<L_h`; only for `j<c_h` may it also claim that the slot's KV is valid. Invalid handles or indices return explicit errors.

v0.2 does not require can_allocate/can_append. If a preview is added later, it may only be read-only advice or a plan bound to a state version; it cannot unconditionally guarantee that it will still be executable after later state changes.

## 7. Edge cases that must be reviewed

| Scenario | Expected behavior |
|---|---|
| Empty input | attach returns InvalidArgument; state unchanged |
| Single-block input, or input of exactly B tokens | attach has k*=0; the last block still needs computing |
| Input of exactly 2B with both blocks cached | Reuse at most the first block; must not mark the whole input as computed |
| Prefix hit on an active page | Add a reference, which can reduce the free pages needed; that page must not be written |
| Prefix hit on a cached page with ref=0 | Reactivate it; this consumes one free-page slot |
| Same current-block tokens, different preceding context | The chained keys differ; must not reuse |
| Tail block not full (L not a multiple of B) | The block has no key and is not in Index; no hit even with identical tokens |
| Tail block completed by extend, then finished | Published only then; a partial block is never published |
| Two requests attach the same T one after the other | The second reuses published pages and adds references; both start computing from k*B |
| Several candidates for one key | Prefer an active candidate, so a servable request is not wrongly rejected |
| Only one free page, but two new pages needed | NoCapacity; must not allocate one page and leave a half-done state |
| L=B, fully computed, append one token | One new page; the new token's logical offset is 0 |
| L=B-1, fully computed, append one token | No new page; the old tail block stays exclusive, and later writes touch only the new slot |
| In-flight ticket not yet complete | release/extend return Busy; old pages cannot be reclaimed |
| The same completion arrives twice | The second is InvalidTicket; the frontier and publication do not advance twice |
| An old handle or old ticket arrives after preemption | Rejected; it does not act on the new lease |
| B=512, execution position j=256, M[0]=0 | The slot must be 256; must not rely on Sequence's default B=256 |
| Many distinct prompts published, then their pages reused (long-running churn) | Stored Index entries stay ≤ P; no entry survives for a key with no candidates (I11) |

## 8. Mapping from upstream methods and intentional changes

| Upstream interface | Draft interface | Change |
|---|---|---|
| BlockManager constructor | create | Fixes the instance configuration and validates the representation range |
| can_allocate + allocate | attach | One atomic operation; does not depend on an externally supplied num_cached_blocks |
| Sequence.append_token + can_append + may_append | extend | Grows the input snapshot and capacity atomically; needs a scheduler adapter |
| seq.num_scheduled_tokens and runner preparation | begin_write | Produces an address plan consistent with the instance, and records in-flight protection |
| hash_blocks + updating num_cached_tokens | finish_write | Commits the frontier and cache publication together after completion |
| deallocate | release | Release while in flight is forbidden; invalidated handles prevent double release |
| compute_hash | Cache identity | Chained 256-bit digest, both identity and index key; enters via the collision-resistance assumption E8 (§9) |

This is a new interface designed for a provable implementation; it cannot replace the old object without adaptation. In particular, `Sequence` may no longer hold an authoritative page table or cache frontier that can be modified independently. If a mirror is needed, it may only be exported from the core, and the adapter must be proved to use a consistent version.

## 9. Proofs the implementation must deliver

### 9.0 Main theorem and external assumptions

**Main theorem.** At every step of any valid trace, if the executor executes the plan returned by `begin_write`, then:

(a) the plan's write slots are exactly `slot(h,j)` (`j in [a,z)`), distinct and within `[0,P*B)`;
(b) every slot of `[0,a)` corresponds in ghost `V` to `(Namespace, T_h[0:j+1])`;
(c) after `finish_write`, every slot of `[a,z)` is updated to its corresponding prefix, and every newly published block i satisfies `den(key[M_h[i]]) = (Namespace, T_h[0:(i+1)B])`;
(d) `Valid(S)` is preserved, each method's frame conditions hold, and error paths satisfy the strong failure atomicity of §5 item 3.

**External assumptions.** The following are not proved, but they must be listed and checked along the verified call chain. E8 is the only cryptographic assumption in this version.

| ID | Assumption | Consequence if violated |
|---|---|---|
| E1 | Completion events are real: the executor confirms the reads and writes are done and used the planned inputs and addresses | The frontier advances over unwritten or wrongly written KV |
| E2 | KV depends only on the prefix: values are independent of batch composition and chunking (within tolerance) | The ghost `V` of shared pages no longer holds |
| E3 | Calls are single-threaded and sequential (or serialized by the caller) | The invariants break under concurrency |
| E4 | Writes always succeed: every issued ticket eventually completes successfully; no failed completion, silent drop, or process termination | Pending never clears, and pages stay occupied forever |
| E5 | The executor uses the planned slots and the instance's B, and does not recompute addresses | Writes to the wrong page or slot |
| E6 | The Namespace is complete: the final field table covers weights, dtype, B, KV format/layout, rope/scaling, attention semantics and adapters; v0.2 uses a dummy byte string, and completeness is the caller's responsibility | Different semantics share keys, causing silent wrong reuse |
| E7 | `Canon`/`Enc` follow the §3.3 canonical encoding: fixed-width uint32 tokens, length-prefixed fields, fixed field order, domain separation | Structural collisions (probability 1) that E8 cannot cover |
| E8 | SHA-256 is collision resistant; the collision probability over `Q` key generations/comparisons during the deployment is `<= Q^2/2^257 + Q/2^256` | Wrong KV reuse across requests (a data leak under multi-tenancy) |

### 9.1 Proof obligations

1. **Initialization:** Valid holds after a successful create.
2. **Per-method preservation:** for every real method body, prove that Valid is preserved, together with C0–C6's functional, error and frame conditions.
3. **Allocation sufficiency:** attach's k*, u and d match their definitions; with correct candidate choice, sufficient capacity guarantees success.
4. **Addressing and isolation:** slot range, no aliasing within a request, no conflicts between pending writes, and shared pages are never written.
5. **Cache soundness:**
   - the canonical chained-key implementation (`Canon`/`Enc`/`Tag`/domain separation) is consistent with Index in both directions;
   - the publication condition is correct;
   - a page's identity is revoked before it is written for a new use;
   - the chain lemma (§3.3) is proved in the ideal hash model, with E8 as the only cryptographic assumption for the concrete instance.
6. **Protocol correctness:** handle/ticket invalidation, single consumption of completions, and in-flight pages are never reclaimed. Prove that the executor-interface premises hold along the verified call chain, or list them as explicit external assumptions (E1, E2, E5).
7. **Termination and representation:** all loops terminate; machine-integer, array and set operations are safe; a verifier UNKNOWN or timeout is not a pass.
8. **Deployment link:** run the verified implementation or its trusted compiled output. A hand-rewritten version does not automatically inherit the proof. The digest implementation and the canonical `Canon`/`Enc` must match the proof's definitions byte for byte.
9. **Bounded metadata** (new in v0.2.1): prove that every method preserves I11 (with I11a), so metadata stays O(P) for traces of any length.

### 9.2 Trusted base

1. E8 (SHA-256 collision resistance and the ε bound);
2. E6 (Namespace completeness) and E7 (canonical encoding): design obligations, not probabilistic assumptions;
3. trusted compiled output (§9.1 item 8);
4. E1/E2/E5 (executor interface). E3/E4 are deployment assumptions (single thread, writes always succeed) and do not enter the method-body proofs.

Auxiliary lemmas, loop invariants and data structures may be designed by the agent. But new assumes, axioms, skipped function bodies, or weakened pre/postconditions must not be used to pass off a proof as complete. E1–E8 are explicitly listed external assumptions and must not become a loophole for new assumes.

Implement and prove in three steps: first unshared allocation/growth/release; then the chained-digest prefix cache and sharing; finally the ticket/completion protocol and the Python runner adapter. Each step keeps the same external functional goals; deferred properties must not be counted as proved.

## 10. Decided and open

Decided in v0.2:

- Keys are chained 256-bit digests: the chain starts at `Seed(ns)` and appends each block's tokens; the digest is both identity and index key. Tail blocks have no key. Identity exactness rests on the explicit probabilistic assumption E8 (§3.3, D4).
- The invariant keeps the ghost `den` so that "which prefix a key describes" can be stated; the concrete layer stores only a 32-byte digest per page, with no intern table and no GC (§3.2, I5).
- `Canon`/`Enc` use the §3.3 canonical encoding; `Tag` is the scheme version; digests are 256-bit and never truncated.
- Single-threaded (E3), and writes always succeed (E4). Spec-decode, offload and multi-threading are non-goals (§1.1).
- The Namespace starts as a dummy byte string (E6); the field table is deferred to v0.3.
- `Pending` stores no `table_ver`; the derived invariants of §3.4 replace it.
- D2/D3 continue: attach reserves for the full input and recomputes the last block. D6/D7's atomic interfaces and explicit in-flight protection are unchanged.

Added in v0.2.1:

- I11 (bounded metadata) with I11a (distinct last pages); I8 tightened so that an empty candidate set has no stored entry.

Still open (must be decided in v0.3 or before implementation):

- The real Namespace field table (E6), and its alignment with `Engine.store_identity()`.
- Whether to share identity with `prefix_keys` in `shell/offload.py`. Sharing requires aligning the Tag, the namespace fields and `grain == B`; otherwise the contract should state explicitly that there are two separate schemes.
- Primitives for speculative decoding and offload (`truncate`/`commit`, `adopt`): whether to add them in v0.3.
- The verification toolchain and repository name (outside this document).

One more explicit boundary: this draft proves resources, provenance, addresses and protocol. Whether the GPU actually completed according to plan, and whether the KV values are numerically correct, need a separate executor contract. That boundary cannot be treated as proved just by assigning values to the ghost V.
