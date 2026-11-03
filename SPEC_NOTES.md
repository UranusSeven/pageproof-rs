# Spec notes: contract v0.2 vs. the Verus implementation

The contract is [docs/block-manager-contract.md](docs/block-manager-contract.md). This file maps
each obligation to where it is proved, and records every deliberate representation choice or
deviation.

## Coverage

| Contract | Where | What is proved |
|---|---|---|
| §3.3 encodings, E7 | `spec.rs`, `e8.rs` | `Canon`/`Enc`/`Tag`/domain separation are injective and parse uniquely. The exec byte builders equal the spec. |
| §3.3 chain lemma | `spec::lemma_chain_inj` | Equal logged chain keys ⇒ same namespace, depth and prefix (under the E8 log). |
| `den` | `spec::den`, `lemma_den_unique`, `lemma_chain_denotes` | `den(K(h,i)) = (ns, T_h[0:(i+1)B])`. |
| I1–I10, I5b | `model::inv` | `cfg_ok` (I1/I10 and representability), `lease_ok` (I1, I4, I5 lease part, I5b, I9), `page_ok` (I2, I3 via derived `F`, I5, I6, I7), `pend_ok` (I9, `c_h = a`). I8 is `index::rep_ok`, connected through `Manager::rep`. |
| §5.1 Valid preserved | each method | `ensures final(self).valid()` |
| §5.3 failure atomicity | each method | `r is Err ==> final(self)@ == old(self)@` (whole abstract state, including ids, index and pending). |
| §5.4 frame | `released`/`attached`/`extended`/`began`/`finish_rel` | Exact abstract post-states: every field not mentioned is unchanged. |
| C0 create | `manager.rs` | Initial state is exact; `ConfigError` on `P = 0`, `B = 0`, `P·B > 2⁴⁰`, or a namespace too long for its `u32` prefix. |
| C1 attach | `ops_attach.rs` | Exact `k*` (`is_kstar`, unique). Success **iff** `|F| ≥ m − u` (`lemma_attach_capacity_iff`), else `NoCapacity`. Hits come from the call-time Index, and an active candidate is used whenever one exists. Fresh pages come from `F` and have their keys revoked. Refs increase by exactly one per table entry. `c = k*·B`. New handle id never reused. |
| C2 extend | `ops_extend.rs` | Phase errors in contract order. Success iff `|F| ≥ d`. Old table is a prefix of the new one. Exactly `d` fresh free pages are added. `T' = T ++ suffix`, `c` unchanged. |
| C3 begin_write | `ops_write.rs` | `plan_ok`: exact inputs, positions, slots `= slot(h,j)`, slots distinct and in `[0, P·B)`, write pages exclusive (`ref = 1`, not in any other lease) and unpublished; page map for `[0,z)`; §9.0 (b). |
| C4 finish_write | `ops_write.rs` | Ticket consumed once, `c = z`. Ghost `V` on `[a,z)` is set to the causal prefix, other slots unchanged. Every block with `a < (i+1)B ≤ z` is published with `K(h,i)` and `den = (ns, T[0:(i+1)B])`; no partial block is published. |
| C5 release | `ops_release.rs` | Exact decrement per page. Pages that reach 0 rejoin `F`. Keys, Index and `V` are retained. `InvalidHandle`/`Busy`. Handle permanently invalid. |
| C6 inspect / slot_of | `ops_release.rs` | Read-only. `slot_of(h,j)` for `j < L_h` equals `slot(h,j)` and lies in range. |
| §9.1.4 pending writes disjoint | `ops_write::lemma_pending_disjoint` | Two live tickets never share a write slot. |
| §9.1.7 integers | everywhere | `usize`/`u64` with overflow checks. `IdentifierExhausted` for handles and tickets, with no wraparound. Manager ids: see the deviations below. |
| §3.3 O(P) metadata | `Manager::lemma_bounded` | Key-index buckets ≤ P (no empty buckets, at most one per published page). Leases ≤ P (`model::last_ok`: distinct leases have distinct last pages). Pending ≤ leases. Each table ≤ P entries, each input ≤ P·B tokens. `refs`, `keys` and the free set have exactly P slots. |

## Representation choices

1. **`F` and `Index` are derived in the abstract state.** `MgrV::free_set() = {b < P | ref[b] = 0}`
   (so I3 holds by definition), and `Index[K] = {b | key[b] = K}` (`index::in_index`), which is
   I8. The concrete `IdxSet` and `KeyIndex` are proved to represent them exactly.
2. **Ghost `holders[b]`** is the set of lease ids that reference `b`, with `ref[b] = |holders[b]|`.
   This makes I2 a per-page fact, so `release` no longer needs a cardinality argument over all
   leases. That cardinality argument is where the Dafny prototype stalled.
3. **Ghost `pdep`/`ptoks`** record, for each published page, its block depth and covered prefix.
   I5's existential becomes a stored witness.
4. **`den` is a function of the E8 log** (`spec::den(log, B, K)`), not a separately stored map.
   `Manager::den_log()` exposes the log. Every method only extends it.
5. **The Index buckets on a 32-bit digest prefix** and compares full 256-bit digests within a
   bucket. Buckets are a performance device: correctness rests only on full-digest equality.
   A bucket is removed when its last page is revoked, so the bucket count stays at most P.
6. **Namespace is fixed per manager (I10),** so ghost `V` stores only the token prefix.
7. **Handles and tickets** carry `(manager id, u64 id)`. Manager ids come from a process-global
   atomic counter, so objects from another manager are rejected even in the same process.

## Deviations and their status

- **`Completion`** is a plain struct naming the ticket. The manager checks that it names this
  ticket and that the ticket is live. Whether the work actually happened is E1, as the contract
  says. A `bool` from an arbitrary caller is not treated as a proof.
- **`create` caps `P·B` at 2⁴⁰ slots.** This keeps `slot`, length and position arithmetic far
  from `usize` overflow. Configurations above the cap return `ConfigError`, as §3.1 allows.
- **`PageTableView` is an owned `Vec` snapshot.** Later `extend` calls cannot change a view that
  was already returned (§C1, §C2).
- **Allocation policy** (which free page, which eviction) is unspecified, as D9 allows. The
  implementation pops from a stack.
- **E3 inside one process:** `Manager` methods take `&mut self`, so Rust serializes them. The
  Python class is `unsendable`.
- **Manager-id uniqueness is trusted, not proved.** vstd's `AtomicU64` specs say nothing about
  return values, so the proof does not establish that two managers get different ids. Rejecting
  another manager's handle or ticket is covered by a runtime test only. `fresh_mgr_id` gives up
  after 1,024 lost compare-exchange races and `create` then returns `IdentifierExhausted`. That
  can only happen when several threads create managers concurrently, which is outside E3.
- **Memory bounds are element counts.** vstd models `Vec`/`HashMap` by their contents, not
  their capacity, so "bytes ∝ peak element count" is trusted about std.
