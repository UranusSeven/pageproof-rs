# Spec notes: contract v0.3 vs. the Verus implementation

The contract is [docs/block-manager-contract.md](docs/block-manager-contract.md). This file maps
each obligation to where it is proved, and records every deliberate representation choice or
deviation. The v0.2.1 single-class `Manager` remains available and verified; in v0.3 it is the
paged-class building block of the `Coordinator`.

## Coverage: v0.3 coordinator

| Contract | Where | What is proved |
|---|---|---|
| §3.1 A1, C0 create | `coord.rs` `Coordinator::create`, `cfg_accepts` | `ConfigError` exactly when `cfg_accepts` fails: `N`, `S`, `B` ≥ 1, at least one paged class, every `u_c ≥ 1` with `u_c \| S`, `N·S ≤ u64::MAX`, `N·n_c·B ≤ 2⁴⁰`. Every slab starts free; no leases. |
| I12 slab ownership, I13 confinement | `Coordinator::own_ok` | `owner` is total, `FS = {s \| owner[s] = 0}`, and unit `x` of class `c` is owned iff `owner[x / n_c] = c + 1`. Per-pool `page_ok`/`StateV::wf` give ref 0 and no key on unowned units. |
| I1–I11 per paged class | `Coordinator::pools_ok` | Every paged class is a valid `Manager` over `N·n_c` units, so the full v0.2.1 invariant holds per class on its owned units. |
| D14 lockstep | `Coordinator::lock_ok` | Paged classes hold the same lease ids, inputs, frontiers, pending tickets and ticket counters. Every lease satisfies `Fits(m)`. |
| I14 live slots, I15 state provenance | `Coordinator::slots_ok`, `state.rs` | One exclusive slot per lease per state class, held by exactly that lease; once `c_h > 0` its ghost `W` is `T_h[0:c_h]`. |
| §3.5 `Cap(d, Prot)` | `CoordV::cap`, `need`, `give`, `rcount`, `fcount` | Stated over per-class free units and slab counts. `check_cap` computes it exactly. |
| §3.5 slab plan, §9.1 obligations 11, 12 | `slabplan.rs` `run_plan`, `CoordV::plan_rel` | Given `Cap`, the greedy plan terminates with `\|F_c\| ≥ d_c` for every class. Each class gains exactly `need_c` slabs and loses at most `give_c`. Free slabs are used first: exactly `max(0, Σ need − \|FS\|)` slabs are reclaimed. A changed slab was free, or idle and outside `Prot`. Keys are revoked only on unreferenced pages of unprotected slabs. Leases, references, tickets and live slots are unchanged. |
| C1 attach | `coord_attach.rs` `Coordinator::attach`, `coord_attach_result`, `lemma_coord_attach_capacity_iff` | Exact joint `k*` (`joint_k`, unique; 0 with a state class). Exact `Prot` (`attach_prot`) and demand. Success **iff** `Cap(d, Prot)`, else `NoCapacity`, atomically. Hits come from the call-time Index and prefer active candidates. Every paged class gets `attached(...)` on the post-plan state; every state class gives a fresh slot with `W = ⊥`. |
| C2 extend | `coord_ops.rs` `Coordinator::extend`, `coord_extend_result` | Phase errors in contract order. `RequestTooLarge` iff `¬Fits(m')`. Success iff `Cap(d, ∅)` with demand `m' − m` per paged class and 0 per state class. State slots unchanged. |
| C3 begin_write | `Coordinator::begin_write`, `cplan_ok` | One ticket for every class. Per paged class: exact write slots `slot_c(h,j)`, distinct, in range, on exclusive unpublished pages; page map for `[0,z)`; §9.0 (b). The state slots are `σ_h^c` and `init = (a = 0)`. When `a > 0` each slot holds `T_h[0:a]`. |
| C4 finish_write | `Coordinator::finish_write`, `coord_finish_result` | `finish_rel` in every paged class (frontier, ghost `V`, publication). Every live state slot's `W` becomes `T_h[0:z]`. Ticket consumed once. |
| C5 release | `Coordinator::release`, `coord_released` | `released(...)` in every paged class. Slots return to `F` with `W = ⊥`. Slab ownership unchanged. Succeeds whenever the lease is live and not pending. |
| C6 inspect / slot_of, C7 arena | `Coordinator::inspect`, `slot_of`, `arena` | Read-only. `arena` returns `owner`, `\|F_c\|` and `\|R_c\|` (with `Prot = ∅`) exactly. |
| Arena disjointness, §9.0 (d), obligation 10 | `Coordinator::theorem_arena_disjoint` | Two distinct owned `(class, unit)` pairs occupy disjoint byte ranges `[g·u_c, (g+1)·u_c)`, all within `[0, N·S)`. Proved from A1 and I12. |
| I11 for the coordinator | `Coordinator::lemma_bounded` | Leases ≤ `N·n_0`. Slot records equal leases. Pending ≤ leases. Each class's index buckets ≤ `N·n_c`. |
| Obligation 13 cross-class atomicity | every coordinator method | `r is Err ==> final@ == old@` on every declared error. On success, every class reflects the operation (`lock_ok`, `slots_ok`). |
| Obligation 14 refinement of v0.2.1 | `Manager` unchanged in behaviour; `Manager::create` = `create_own(.., true)` | With one paged class the per-class step is exactly the v0.2.1 operation, whose proofs are reused unchanged (the v0.2.1 test suite still passes). The stronger statement (coordinator behaviour equals v0.2.1 up to page renaming) is not separately proved; see deviations. |
| Public usability | `crates/pageproof-client` | `attach_release`: from the public specs alone, `release` right after a successful `attach` succeeds and returns the input. `coord_churn`: validity and bounds over an arbitrary scheduler loop. |

## Coverage: v0.2.1 manager (unchanged)

| Contract | Where | What is proved |
|---|---|---|
| §3.3 encodings, E7 | `spec.rs`, `e8.rs` | `Canon`/`Enc`/`Tag`/domain separation are injective and parse uniquely. The exec byte builders equal the spec. |
| §3.3 chain lemma | `spec::lemma_chain_inj` | Equal logged chain keys ⇒ same namespace, depth and prefix (under the E8 log). |
| `den` | `spec::den`, `lemma_den_unique`, `lemma_chain_denotes` | `den(K(h,i)) = (ns, T_h[0:(i+1)B])`. |
| I1–I11, I5b, I11a | `model::inv` | `cfg_ok` (I1/I10, representability), `lease_ok` (I1, I4, I5 lease part, I5b, I9), `page_ok` (I2, I3, I5, I6, I7, and I13 for ownership), `pend_ok` (I9, `c_h = a`). I8 is `index::rep_ok`. I11a is `model::last_ok`. |
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
| I11 bounded metadata (§3.3 O(P)) | `Manager::lemma_bounded` | Key-index buckets ≤ P (no empty buckets, at most one per published page). Leases ≤ P (`model::last_ok`: distinct leases have distinct last pages). Pending ≤ leases. Each table ≤ P entries, each input ≤ P·B tokens. `refs`, `keys` and the free set have exactly P slots. |
| C1 split | `ops_attach.rs` | `attach` is `probe_prefix` (capped run, ghost-log only) + `attach_commit` (at any hit prefix `k`). The coordinator uses these to commit at a joint `k*`. |
| Slab moves on one class | `ops_slab.rs` | `grant_range` and `reclaim_range` preserve `Valid`. Reclaim requires an idle range and revokes every key in it. |

## Representation choices

1. **One `Manager` per paged class, one `StatePool` per state class.** Unit ids of class `c` are
   `[0, N·n_c)`. Unit `g` lies in slab `g / n_c`. Per-unit ownership `own[g]` equals
   `owner[g / n_c] = c + 1` (`own_ok`).
2. **Lockstep paged classes.** Every paged class holds every lease (same id, input, frontier,
   pending ticket). The coordinator's handle and ticket ids are paged class 0's ids, so they name
   the same lease and ticket everywhere. This puts all of D14 in the invariant (`lock_ok`).
3. **Slab counts are recursive counts** (`cnt.rs`), not set cardinalities. The greedy plan's
   proof is a per-step accounting of `need`, `give`, `gained`, `lost` and `|FS|`
   (`slabplan::pinv`).
4. **`Prot` is computed from the full candidate set** of each inactive hit key
   (`KeyIndex::candidates`), so it is exactly the contract's set, not an over-approximation.
5. **Ghost `W`** for state units is `Option<Seq<Token>>`. The namespace is fixed per coordinator,
   so only the prefix is stored.
6. Representation choices 1–7 of v0.2.1 (derived `F` and `Index`, ghost holders, `pdep`/`ptoks`,
   `den` from the E8 log, 32-bit buckets, handle/ticket ids) still hold per paged class.

## Deviations and their status

- **Reclaim choice is greedy.** D9 leaves the donor and slab choice open. The implementation takes
  the first class with surplus and its first reclaimable slab. `plan_rel` proves the counts the
  contract requires.
- **Obligation 14 is partial.** The single-class operations are the v0.2.1 methods with their
  proofs. The coordinator-level refinement statement is not separately proved.
- **State units are not cleared.** Freed and reclaimed state units get `W = ⊥`; E10 makes the
  executor initialise a slot when `init` is set.
- **`Coordinator::create` caps the class count at 2¹⁶** and each class at `N·n_c·B ≤ 2⁴⁰` token
  slots (§3.1 allows rejecting unrepresentable configurations).
- **`Completion`, manager ids, E3, memory bounds:** as in v0.2.1 (see below).
- **`Completion`** is a plain struct naming the ticket. Whether the work happened is E1.
- **Manager-id uniqueness is trusted, not proved.** vstd's `AtomicU64` specs say nothing about
  return values. Rejecting another coordinator's handles is covered by a runtime test only.
- **E3 inside one process:** methods take `&mut self`. The Python classes are `unsendable`.
- **Memory bounds are element counts.** "Bytes ∝ peak element count" is trusted about std.
