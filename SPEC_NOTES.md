# Spec notes: contract v0.6 vs. the Verus implementation

The contract is [docs/block-manager-contract.md](docs/block-manager-contract.md). This file maps
each obligation to where it is proved, and records every deliberate representation choice or
deviation. v0.6 adds speculative decoding (v0.4.1), zero-overhead scheduling (ZOS, v0.5) and their
combination (v0.6) to the v0.3 coordinator. The v0.2.1 single-class `Manager` remains available
and verified; it is the paged-class building block of the `Coordinator`.

## Coverage: coordinator C0–C7 and C2b

| Contract | Where | What is proved |
|---|---|---|
| §3.1 A1, C0 create | `coord.rs` `Coordinator::create`, `create_early_ok`, `cfg_rel` | `ConfigError` on the v0.3 conditions, and also on: drafter classes with `λ = 0`, no target class, `δ > 1`, `μ` not representable, or `¬Fits(ceil((1 + μ)/B))`. Otherwise `μ = (δ + 1)·λ + λ·[Cx ≠ ∅]` and every paged class gets the same `(μ, λ, δ, ntarget)`. Every slab starts free; no leases. |
| I12 slab ownership, I13 confinement | `Coordinator::own_ok` | `owner` is total, `FS = {s \| owner[s] = 0}`, and unit `x` of class `c` is owned iff `owner[x / n_c] = c + 1`. |
| I1–I11, I16–I18 per paged class | `Coordinator::pools_ok`, `model::inv` | Every paged class (target and drafter) is a valid `Manager` over `N·n_c` units with the shared configuration. |
| D14 lockstep, obligation 17 | `Coordinator::lock_ok` | Paged classes hold the same leases, inputs, frontiers, reaches, queues, deferred flags, stopped flags, tickets and counters. Every lease satisfies `Fits(ceil(ρ_h/B))`. |
| I14, I15 | `Coordinator::slots_ok`, `w_ok` | One exclusive slot per lease per state class. `W = T_h[0:c_h]` once `c_h > 0` on a lease that is not stopped, and `W = ⊥` on a stopped lease. |
| C1 attach | `coord_attach.rs` | v0.3's result, with tables sized for the reach `ρ = L + μ` (`m^+ = ceil((L + μ)/B)`), joint `k*` over `ceil(L/B)`, success iff `Cap(d, Prot)`. |
| C2 extend, C2b extend_deferred | `coord_ops.rs` `Coordinator::grow`, `coord_grow_result` | One body for both. Errors in contract order: InvalidHandle, InvalidPhase on a stopped lease, Busy (extend: full queue or a head with drafts or `propose`; extend_deferred: full queue), InvalidPhase (`X_h` non-empty, `p_h ≠ L_h`, or extend_deferred with an empty queue), InvalidArgument, RequestTooLarge iff `¬Fits(m')`, NoCapacity iff `¬Cap`. On success every paged class gets `grown(...)`: `ρ' = L̂' + μ`, and extend_deferred sets `X_h = [Q_h[0]]`. |
| C3 begin_write | `Coordinator::begin_write`, `coord_begin_result`, `cplan_ok` | Errors in contract order (InvalidPhase on a stopped lease, then Busy, then InvalidArgument, then IdentifierExhausted). A valid call never fails for capacity. The plan has `lo = p_h`, `slack = s_h`, `ℓ`, `k`, `propose`, `producer` (for a continuation), `init = (lo = 0)`, inputs `T_h[lo:lo+ℓ] ++ D` or placeholders, and per paged class the slots `slot_c(h,j)` for `j ∈ [lo, lo + s + ℓ + k (+λ))`, distinct, in range and on exclusive unpublished pages. |
| C4 finish_write | `Coordinator::finish_write`, `coord_finish_result` | Head ticket only (InvalidTicket otherwise). Orphan: Ok with any fields, `coord_dropped`. Otherwise InvalidArgument unless `n ≤ k`, `x` is given when the ticket heads `X_h` without `stop`, and a continuation with deferred drafts reports exactly `n`. Success: commit `D[0:n]` (known or reported), then bind `x` when the ticket heads `X_h` and `x` is given, then `finish_rel` in every class with `c' = z + n` and publication over `T'_h`. Without `stop` every state slot gets `W = T'_h[0:c']`; with `stop` the lease is stopped and `W = ⊥`. |
| C5 release | `Coordinator::release` | v0.3's result. Busy while any ticket, orphans included, is pending. |
| C6 inspect / slot_of, C7 arena | `Coordinator::inspect`, `slot_of`, `arena` | `L_h`, `c_h`, `ρ_h`, `p_h`, `s_h`, `X_h` (as `deferred`), `stopped_h`, `Q_h` in issue order, tables, slots, `λ`, `μ`, `δ`. `slot_of` for `j < ρ_h`. |
| Arena disjointness, obligation 10 | `Coordinator::theorem_arena_disjoint` | Unchanged from v0.3; drafter classes are paged classes. |
| I11, obligation 9 | `Coordinator::lemma_bounded` | Leases ≤ `N·n_0`. Pending ≤ `(δ + 1)·leases`. Index buckets ≤ `N·n_c`. |
| Obligation 13 | every coordinator method | `r is Err ==> final@ == old@`, including extend_deferred. |
| Public usability | `crates/pageproof-client` | `coord_churn` runs chunks, a deferred step, a continuation and a completion with `stop` in a loop; validity and the bounds hold at every iteration from the public specs alone. |

## Coverage: v0.4–v0.6 obligations (§9.1)

| Obligation | Where | Status |
|---|---|---|
| 15 Draft reservation | `lease_ok` (I16: `L̂ ≤ ρ ≤ L̂ + μ`, room clause), `pend_ok` (span fits), `begin_args_ok` | Proved. Demands use `reach_blocks`. begin and finish never change ownership, `F_c` or `ref_c` (`paged_step`, `finish_rel`). |
| 16 Partial commit | `ops_write.rs` `committed_t`, `lemma_commit_inv`, `finish_rel` | Proved for every `n ≤ k`: `T'_h = T_h ++ D[0:n]`, `c' = z + n`, I4/I5/I5b/I6/I15 over `T'_h`. A rejected count leaves the state unchanged. |
| 17 Drafter classes | `lock_ok`, `CoordV::ext_of`, `cplan_class` | Proved. The drafter range `[lo, W + λ)` is in the reach and on exclusive unpublished pages. finish credits `[a, z + n)` only, so proposal rows gain no claim. |
| 19 E11/E12 enter only at finish | method bodies | By construction: only `finish_core` updates `W`, and only `finish_rel` updates `V` and keys. The plan exposes `num_drafts` and `propose`. |
| 21 Pipelined tickets | `lease_ok` (I9 queue clauses), `pend_ok`, `is_head` | Proved: at most `δ + 1` tickets in issue order, contiguous, completed in order. Pending plans stay valid because every position at or past `c_h` is on an exclusive unpublished page (`lemma_uncomputed_exclusive`). |
| 22 Deferred tail | `lease_ok` (I17), `bind_deferred`, `lemma_finish_facts` | Proved: `X_h` holds at most the head; its token is bound exactly once, after the head's accepted drafts, or never with `stop` and no token. The head's `z ≤ L_h`, so no key covers a deferred position. |
| 23 E13 enters only at finish | method bodies | By construction. The plan exposes `producer`, `lo` and `slack`. |
| 25 Bounded start | `pend_ok` (head starts at `c_h`), `lease_ok` (second-ticket fit), `committed_t` | Proved: committing `n` raises the next ticket's base by `n`, so it starts exactly at `c'_h`. A valid ticket's span fits the reach for every acceptance count of the ticket ahead. The orphan window bound is E13. |
| 26 Overlapping windows | `cplan_ok`, `lemma_uncomputed_exclusive` | Proved as stated: the listed slots cover `[lo, lo + s + ℓ + k)`, which contains every window `lo + σ`, `σ ≤ s`; every listed page past `c_h` is exclusive and unpublished, and stays so as `c_h` grows. |
| 27 Stop and orphans | `lease_ok` (I18), `finish_rel(.., stop)`, `dropped` | Proved: stop credits the committed prefix, stops the lease, empties `X_h` and sets `W = ⊥`; an orphan changes only `Q_h` and `Pending`; begin, extend and extend_deferred return InvalidPhase; release succeeds once the queue is empty. |
| 14, 18, 20, 24 Refinement of earlier versions | specs | Not proved as observational equivalences. See the deviations. |

## Coverage: v0.2.1 manager

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
| §9.1.4 pending writes disjoint | `ops_write::lemma_pending_disjoint`, `lemma_reserved_disjoint` | The input intervals of two pending tickets never share a slot. Across leases, every position from `c_h` to `ρ_h` (so every listed draft, proposal-row and slack slot) is on a slot no other lease's plan can list. Within one lease, a continuation's window may overlap the earlier ticket's rejected and proposal rows (obligation 26). |
| §9.1.7 integers | everywhere | `usize`/`u64` with overflow checks. `IdentifierExhausted` for handles and tickets, with no wraparound. Manager ids: see the deviations below. |
| I11 bounded metadata (§3.3 O(P)) | `Manager::lemma_bounded` | Key-index buckets ≤ P (no empty buckets, at most one per published page). Leases ≤ P (`model::last_ok`: distinct leases have distinct last pages). Pending ≤ leases. Each table ≤ P entries, each input ≤ P·B tokens. `refs`, `keys` and the free set have exactly P slots. |
| C1 split | `ops_attach.rs` | `attach` is `probe_prefix` (capped run, ghost-log only) + `attach_commit` (at any hit prefix `k`). The coordinator uses these to commit at a joint `k*`. |
| Slab moves on one class | `ops_slab.rs` | `grant_range` and `reclaim_range` preserve `Valid`. Reclaim requires an idle range and revokes every key in it. |

## Representation choices

1. **One `Manager` per paged class, one `StatePool` per state class.** Drafter classes are paged
   classes `[ntarget, np)`. Unit ids of class `c` are `[0, N·n_c)`; unit `g` lies in slab `g / n_c`.
2. **Lockstep paged classes.** Every paged class holds every lease and every ticket. The
   coordinator's handle and ticket ids are paged class 0's.
3. **`X_h` is a flag.** With `δ ≤ 1`, the deferred tail holds at most one ticket, and then it is
   `Q_h[0]` (extend_deferred needs `|Q_h| ≤ δ`). So `LeaseV.dfr` represents `X_h`, and
   `L̂_h = L_h + [dfr]` (`model::lhat`).
4. **A pending ticket's `a` and `z` are its base and `base + ℓ`.** Committing the head's `n`
   accepted drafts raises the second ticket's `a` and `z` by `n` (`committed_t`), so the head
   always starts at `c_h`. `lo` and `s` are plan fields only; the invariant needs only that the
   second ticket fits the reach for every acceptance count of the head.
5. **Orphans are the tickets of a stopped lease** (I18 makes these equivalent). With `δ ≤ 1` a
   stopped lease holds at most one orphan, so no per-ticket flag is stored.
6. **A continuation's deferred drafts are placeholders** (`PendV.ddr`); the completion's reported
   drafts replace them at commit.
7. **Commit drops the head's rejected drafts.** Nothing reads them after the commit.
8. v0.3's representation choices (slab counts as recursive counts, `Prot` from the full candidate
   set, ghost `W` as `Option<Seq<Token>>`) and v0.2.1's still hold.

## Deviations and their status

- **Refinement obligations 14, 18, 20, 24 are partial.** Each method's spec specialises to the
  earlier version's when `λ = 0`, `δ = 0` or `Cx = ∅`, and the v0.2.1 and v0.3 test suites still
  pass, but the observational-equivalence statements are not separately proved.
- **C6 does not return each pending ticket's `lo`, `s`, `ℓ`, `k`, `propose` and `producer`.**
  `inspect` returns `Q_h` (ticket ids in issue order) and the lease-level `p_h`, `s_h`, `X_h` and
  `stopped_h`; the per-ticket fields are in the plan the caller holds.
- **The per-class `Manager` API gains states it cannot reach.** Its result specs include
  InvalidPhase on a stopped lease and InvalidArgument on a deferred head, but only the coordinator
  stops leases or defers positions (`Manager::create` has `δ = 0`). `Manager::extend_deferred`
  never succeeds with `δ = 0`. `create_empty` also requires `λ + δλ ≤ μ`, which every coordinator
  configuration satisfies.
- **Reclaim choice is greedy** (D9 leaves it open); `plan_rel` proves the counts.
- **Paged classes agree on leases, not on which pages hits share.** D14 keeps every paged class
  on the same leases, inputs and table lengths, but each class picks its own candidate for a hit.
  `scan_bucket` takes the first referenced candidate in bucket order, revoking a key reorders a
  bucket (`swap_remove`), and each class's free set pops in its own order. Classes with different
  pages per slab can therefore revoke a key in one class only, and later hits can share one
  lease's page in one class and another lease's in the other. Free-unit counts then differ across
  classes, so a paged-only arena can reclaim: `coord_edge_cases.rs::divergent_paged_arena` builds
  such an arena. With it, `paged_only_reclaim_revokes_the_keys_of_its_slab` checks that a
  reclaimed slab's key stops being a hit, and `prot_keeps_the_only_free_candidate_of_a_hit` covers
  the §7 row "a reclaimable slab holds the only free candidate for a hit" (Prot under pressure).
  The proofs never relied on the classes sharing the same pages.
- **State units are not cleared.** Freed, reclaimed and stopped slots get `W = ⊥`; E10 makes the
  executor initialise a slot when `init` is set.
- **`Coordinator::create` caps the class count at 2¹⁶** and each class at `N·n_c·B ≤ 2⁴⁰` token
  slots (§3.1 allows rejecting unrepresentable configurations).
- **`Completion` and `CoordCompletion`** are plain structs. Whether the work happened, and whether
  the reported count, token and drafts are the device's, are E1 and E13.
- **Manager-id uniqueness is trusted, not proved.** vstd's `AtomicU64` specs say nothing about
  return values. Rejecting another coordinator's handles is covered by a runtime test only.
- **E3 inside one process:** methods take `&mut self`. The Python classes are `unsendable`.
- **Memory bounds are element counts.** "Bytes ∝ peak element count" is trusted about std.
