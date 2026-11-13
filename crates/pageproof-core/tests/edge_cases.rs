//! Runtime checks of the contract §7 edge-case table against the verified implementation.
//! These complement the proofs: they exercise the compiled code paths end to end.
use pageproof_core::manager::Manager;
use pageproof_core::ops_write::Completion;
use pageproof_core::types::{Error, Handle, Ticket};

const NS: &[u8] = b"dummy-v0.2";

fn mgr(p: usize, b: usize) -> Manager {
    Manager::create(p, b, NS).expect("create")
}

/// Runs one begin/finish round for `n` tokens and returns the new frontier.
fn compute(m: &mut Manager, h: Handle, n: usize) -> usize {
    let (t, plan) = m.begin_write(h, n).expect("begin_write");
    assert_eq!(plan.ticket, t);
    assert_eq!(plan.write_slots.len(), n);
    m.finish_write(t, Completion { ticket: t }).expect("finish_write")
}

fn compute_all(m: &mut Manager, h: Handle) {
    let v = m.inspect(h).unwrap();
    if v.computed < v.len {
        compute(m, h, v.len - v.computed);
    }
}

fn toks(n: usize, seed: u32) -> Vec<u32> {
    (0..n as u32).map(|i| i.wrapping_mul(2654435761).wrapping_add(seed)).collect()
}

#[test]
fn create_rejects_bad_config() {
    assert_eq!(Manager::create(0, 4, NS).err(), Some(Error::ConfigError));
    assert_eq!(Manager::create(4, 0, NS).err(), Some(Error::ConfigError));
    assert_eq!(Manager::create(1 << 21, 1 << 20, NS).err(), Some(Error::ConfigError));
    let m = mgr(8, 4);
    assert_eq!(m.free_count(), 8);
}

#[test]
fn empty_input_is_invalid() {
    let mut m = mgr(4, 4);
    assert_eq!(m.attach(&[]).err(), Some(Error::InvalidArgument));
    assert_eq!(m.free_count(), 4);
}

#[test]
fn too_large_input() {
    let mut m = mgr(2, 4);
    assert_eq!(m.attach(&toks(9, 0)).err(), Some(Error::RequestTooLarge));
    assert!(m.attach(&toks(8, 0)).is_ok());
}

#[test]
fn single_block_and_exact_b_have_kstar_zero() {
    let mut m = mgr(8, 4);
    for n in [1usize, 3, 4] {
        let (h, cached, view) = m.attach(&toks(n, 7)).unwrap();
        assert_eq!(cached, 0, "n={n}");
        assert_eq!(view.pages.len(), 1);
        compute_all(&mut m, h);
        m.release(h).unwrap();
        // Even after publishing the exact-B block, re-attaching must recompute the last block.
        let (h2, cached2, _) = m.attach(&toks(n, 7)).unwrap();
        assert_eq!(cached2, 0, "last block always recomputed (n={n})");
        m.release(h2).unwrap();
    }
}

#[test]
fn exactly_two_blocks_reuses_at_most_first() {
    let mut m = mgr(8, 4);
    let t = toks(8, 1);
    let (h, _, _) = m.attach(&t).unwrap();
    compute_all(&mut m, h);
    m.release(h).unwrap();
    let (h2, cached, _) = m.attach(&t).unwrap();
    assert_eq!(cached, 4);
    let v = m.inspect(h2).unwrap();
    assert_eq!(v.computed, 4);
    assert!(v.computed < v.len);
}

#[test]
fn hit_on_active_page_saves_capacity() {
    // P=3, B=4: first request uses 3 pages for 12 tokens (blocks 0,1,2).
    let mut m = mgr(3, 4);
    let t = toks(12, 3);
    let (h1, _, v1) = m.attach(&t).unwrap();
    compute_all(&mut m, h1);
    assert_eq!(m.free_count(), 0);
    // Second request with the same 12 tokens: k* = 2 active hits, d = 3 - 2 = 1 > |F| = 0.
    assert_eq!(m.attach(&t).err(), Some(Error::NoCapacity));
    // A request sharing 2 blocks and needing exactly 2 more pages... still no capacity.
    // Release nothing; now a request that shares the first 2 blocks and is 8+1 tokens long
    // needs 3 blocks with 2 active hits: d = 1 > 0.
    let mut t3 = t[..8].to_vec();
    t3.push(99);
    assert_eq!(m.attach(&t3).err(), Some(Error::NoCapacity));
    // A request of exactly the 8 shared tokens needs 2 blocks; k* = 1 (last block recomputed),
    // u = 1, d = 1 > 0.
    assert_eq!(m.attach(&t[..8]).err(), Some(Error::NoCapacity));
    let pages1 = v1.pages.clone();
    m.release(h1).unwrap();
    assert_eq!(m.free_count(), 3);
    // Two concurrent sharers: first attaches, second shares two active pages.
    let (ha, ca, va) = m.attach(&t[..8]).unwrap();
    assert_eq!(ca, 4);
    assert_eq!(va.pages[0], pages1[0], "reactivates the cached page");
    assert_eq!(m.free_count(), 1);
    let (hb, cb, vb) = m.attach(&t[..8]).unwrap();
    assert_eq!(cb, 4);
    assert_eq!(vb.pages[0], va.pages[0], "prefers the active candidate");
    assert_eq!(m.free_count(), 0);
    m.release(ha).unwrap();
    m.release(hb).unwrap();
}

#[test]
fn hit_on_free_cached_page_costs_a_slot() {
    let mut m = mgr(2, 4);
    let t = toks(8, 5);
    let (h, _, _) = m.attach(&t).unwrap();
    compute_all(&mut m, h);
    m.release(h).unwrap();
    // Both pages free but block 0 is cached. Re-attach needs 2 pages: 1 reactivated + 1 fresh.
    let (h2, cached, _) = m.attach(&t).unwrap();
    assert_eq!(cached, 4);
    assert_eq!(m.free_count(), 0);
    m.release(h2).unwrap();
}

#[test]
fn same_block_different_context_does_not_hit() {
    let mut m = mgr(8, 4);
    let a: Vec<u32> = vec![1, 2, 3, 4, 10, 11, 12, 13, 0];
    let b: Vec<u32> = vec![9, 9, 9, 9, 10, 11, 12, 13, 0];
    let (h, _, _) = m.attach(&a).unwrap();
    compute_all(&mut m, h);
    let (h2, cached, _) = m.attach(&b).unwrap();
    assert_eq!(cached, 0, "block 1 tokens match but the chain differs");
    m.release(h).unwrap();
    m.release(h2).unwrap();
}

#[test]
fn partial_tail_is_never_published() {
    let mut m = mgr(8, 4);
    let t = toks(6, 11);
    let (h, _, _) = m.attach(&t).unwrap();
    compute_all(&mut m, h);
    m.release(h).unwrap();
    // Same 6 tokens plus more: block 0 (complete) is a hit; block 1 was partial and never keyed.
    let mut t2 = t.clone();
    t2.extend_from_slice(&[1, 2, 3]);
    let (h2, cached, _) = m.attach(&t2).unwrap();
    assert_eq!(cached, 4);
    m.release(h2).unwrap();
}

#[test]
fn tail_completed_by_extend_is_published_on_finish() {
    let mut m = mgr(8, 4);
    let t = toks(6, 13);
    let (h, _, _) = m.attach(&t).unwrap();
    compute_all(&mut m, h);
    m.extend(h, &[100, 101, 102]).unwrap();
    compute_all(&mut m, h);
    m.release(h).unwrap();
    let mut full = t.clone();
    full.extend_from_slice(&[100, 101, 102]);
    full.push(7);
    let (h2, cached, _) = m.attach(&full).unwrap();
    assert_eq!(cached, 8, "blocks 0 and 1 (completed via extend) both hit");
    m.release(h2).unwrap();
}

#[test]
fn two_requests_same_input_share() {
    let mut m = mgr(8, 4);
    let t = toks(10, 17);
    let (h1, _, v1) = m.attach(&t).unwrap();
    compute_all(&mut m, h1);
    let (h2, cached, v2) = m.attach(&t).unwrap();
    assert_eq!(cached, 8);
    assert_eq!(&v1.pages[..2], &v2.pages[..2]);
    assert_ne!(v1.pages[2], v2.pages[2]);
    assert_eq!(m.inspect(h2).unwrap().computed, 8);
    compute_all(&mut m, h2);
    m.release(h1).unwrap();
    m.release(h2).unwrap();
}

#[test]
fn no_capacity_is_atomic() {
    let mut m = mgr(1, 4);
    assert_eq!(m.attach(&toks(5, 0)).err(), Some(Error::RequestTooLarge));
    let mut m = mgr(2, 4);
    let (h, _, _) = m.attach(&toks(4, 0)).unwrap();
    assert_eq!(m.free_count(), 1);
    assert_eq!(m.attach(&toks(8, 1)).err(), Some(Error::NoCapacity));
    assert_eq!(m.free_count(), 1, "no half-completed allocation");
    let _ = m.attach(&toks(4, 2)).unwrap();
    assert_eq!(m.free_count(), 0);
    m.release(h).unwrap();
}

#[test]
fn extend_at_block_boundary_adds_page() {
    let mut m = mgr(4, 4);
    let (h, _, _) = m.attach(&toks(4, 0)).unwrap();
    compute_all(&mut m, h);
    let view = m.extend(h, &[42]).unwrap();
    assert_eq!(view.pages.len(), 2);
    let s = m.slot_of(h, 4).unwrap();
    assert_eq!(s, view.pages[1] * 4, "new token has logical offset 0 on the new page");
}

#[test]
fn extend_within_tail_adds_no_page() {
    let mut m = mgr(4, 4);
    let (h, _, v0) = m.attach(&toks(3, 0)).unwrap();
    compute_all(&mut m, h);
    let free0 = m.free_count();
    let view = m.extend(h, &[42]).unwrap();
    assert_eq!(view.pages, v0.pages);
    assert_eq!(m.free_count(), free0);
    let (_, plan) = m.begin_write(h, 1).unwrap();
    assert_eq!(plan.write_slots, vec![v0.pages[0] * 4 + 3]);
}

#[test]
fn extend_phase_errors_and_snapshot() {
    let mut m = mgr(4, 4);
    let (h, _, v0) = m.attach(&toks(4, 0)).unwrap();
    assert_eq!(m.extend(h, &[1]).err(), Some(Error::InvalidPhase));
    compute_all(&mut m, h);
    assert_eq!(m.extend(h, &[]).err(), Some(Error::InvalidArgument));
    assert_eq!(m.extend(h, &toks(13, 1)).err(), Some(Error::RequestTooLarge));
    let _ = m.extend(h, &toks(4, 1)).unwrap();
    assert_eq!(v0.pages.len(), 1, "earlier view is an immutable snapshot");
}

#[test]
fn pending_blocks_extend_and_release() {
    let mut m = mgr(4, 4);
    let (h, _, _) = m.attach(&toks(4, 0)).unwrap();
    let (t, _) = m.begin_write(h, 4).unwrap();
    assert_eq!(m.release(h).err(), Some(Error::Busy));
    assert_eq!(m.extend(h, &[1]).err(), Some(Error::Busy));
    assert_eq!(m.begin_write(h, 1).err(), Some(Error::Busy));
    assert_eq!(m.free_count(), 3, "pages stay reserved while in flight");
    m.finish_write(t, Completion { ticket: t }).unwrap();
    m.release(h).unwrap();
}

#[test]
fn completion_is_consumed_once() {
    let mut m = mgr(4, 4);
    let (h, _, _) = m.attach(&toks(4, 0)).unwrap();
    let (t, _) = m.begin_write(h, 2).unwrap();
    assert_eq!(m.finish_write(t, Completion { ticket: t }), Ok(2));
    assert_eq!(m.finish_write(t, Completion { ticket: t }).err(), Some(Error::InvalidTicket));
    assert_eq!(m.inspect(h).unwrap().computed, 2);
}

#[test]
fn stale_handle_and_ticket_rejected_after_preemption() {
    let mut m = mgr(4, 4);
    let t = toks(6, 0);
    let (h, _, _) = m.attach(&t).unwrap();
    let (tk, _) = m.begin_write(h, 2).unwrap();
    m.finish_write(tk, Completion { ticket: tk }).unwrap();
    let snap = m.release(h).unwrap();
    assert_eq!(snap, t);
    assert_eq!(m.release(h).err(), Some(Error::InvalidHandle), "no double release");
    let (h2, _, _) = m.attach(&snap).unwrap();
    assert_ne!(h2, h);
    assert_eq!(m.inspect(h).err(), Some(Error::InvalidHandle));
    assert_eq!(m.begin_write(h, 1).err(), Some(Error::InvalidHandle));
    assert_eq!(m.finish_write(tk, Completion { ticket: tk }).err(), Some(Error::InvalidTicket));
    // Handles and tickets of another manager are rejected.
    let mut other = mgr(4, 4);
    assert_eq!(other.inspect(h2).err(), Some(Error::InvalidHandle));
    let (t2, _) = m.begin_write(h2, 1).unwrap();
    assert_eq!(other.finish_write(t2, Completion { ticket: t2 }).err(), Some(Error::InvalidTicket));
    let forged = Ticket { mgr: t2.mgr, id: t2.id + 1 };
    assert_eq!(m.finish_write(forged, Completion { ticket: forged }).err(), Some(Error::InvalidTicket));
    assert_eq!(
        m.finish_write(t2, Completion { ticket: forged }).err(),
        Some(Error::InvalidTicket),
        "completion must name the ticket"
    );
}

#[test]
fn plan_uses_instance_block_size() {
    // B=512, position j=256, M[0]=0 -> slot 256.
    let mut m = mgr(4, 512);
    let (h, _, view) = m.attach(&toks(300, 0)).unwrap();
    assert_eq!(view.pages.len(), 1);
    let (t, _) = m.begin_write(h, 256).unwrap();
    m.finish_write(t, Completion { ticket: t }).unwrap();
    let (_, plan) = m.begin_write(h, 1).unwrap();
    assert_eq!(plan.block_size, 512);
    assert_eq!(plan.positions, vec![256]);
    assert_eq!(plan.write_slots, vec![view.pages[0] * 512 + 256]);
    assert_eq!(m.slot_of(h, 256), Ok(view.pages[0] * 512 + 256));
    assert_eq!(m.slot_of(h, 300).err(), Some(Error::InvalidArgument));
}

#[test]
fn plan_contents() {
    let mut m = mgr(8, 4);
    let t = toks(10, 21);
    let (h, _, view) = m.attach(&t).unwrap();
    let (tk, plan) = m.begin_write(h, 7).unwrap();
    assert_eq!(plan.ticket, tk);
    assert_eq!(plan.handle, h);
    assert_eq!(plan.input_ids, t[..7].to_vec());
    assert_eq!(plan.positions, (0..7).collect::<Vec<_>>());
    let exp: Vec<usize> = (0..7).map(|j| view.pages[j / 4] * 4 + j % 4).collect();
    assert_eq!(plan.write_slots, exp);
    assert_eq!(plan.page_table, view.pages[..2].to_vec());
    assert_eq!(m.begin_write(h, 0).err(), Some(Error::Busy));
    m.finish_write(tk, Completion { ticket: tk }).unwrap();
    assert_eq!(m.begin_write(h, 0).err(), Some(Error::InvalidArgument));
    assert_eq!(m.begin_write(h, 4).err(), Some(Error::InvalidArgument));
    assert!(m.begin_write(h, 3).is_ok());
}

#[test]
fn key_matches_reference_chain() {
    // Independent re-implementation of §3.3 (Seed/K/Canon/Enc) with the sha2 crate.
    use sha2::{Digest, Sha256};
    fn seed(ns: &[u8]) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"mg-block-key-v1");
        h.update([0u8]);
        h.update((ns.len() as u32).to_le_bytes());
        h.update(ns);
        h.finalize().into()
    }
    fn node(parent: &[u8; 32], blk: &[u32]) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"mg-block-key-v1");
        h.update([1u8]);
        h.update(parent);
        for t in blk {
            h.update(t.to_le_bytes());
        }
        h.finalize().into()
    }
    let s = seed(NS);
    let k0 = node(&s, &[1, 2, 3, 4]);
    let got = pageproof_core::e8::node_input_bytes(&s, &[1, 2, 3, 4]);
    let mut exp = b"mg-block-key-v1".to_vec();
    exp.push(1);
    exp.extend_from_slice(&s);
    for t in [1u32, 2, 3, 4] {
        exp.extend_from_slice(&t.to_le_bytes());
    }
    assert_eq!(got, exp);
    let mut sexp = b"mg-block-key-v1".to_vec();
    sexp.push(0);
    sexp.extend_from_slice(&(NS.len() as u32).to_le_bytes());
    sexp.extend_from_slice(NS);
    assert_eq!(pageproof_core::e8::seed_input_bytes(NS), sexp);
    assert_ne!(k0, s);
}

#[test]
fn many_requests_random_walk() {
    // Light randomized walk: exercise interleavings, check frees are conserved.
    let p = 16;
    let mut m = mgr(p, 4);
    let mut live: Vec<Handle> = Vec::new();
    let mut x: u64 = 0x9e3779b97f4a7c15;
    let mut next = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let base = toks(40, 99);
    for _ in 0..2000 {
        match next() % 4 {
            0 => {
                let n = 1 + (next() % 20) as usize;
                let start = if next() % 2 == 0 { 0 } else { (next() % 8) as usize };
                if let Ok((h, _, _)) = m.attach(&base[start..start + n]) {
                    live.push(h);
                }
            }
            1 if !live.is_empty() => {
                let h = live[(next() as usize) % live.len()];
                let v = m.inspect(h).unwrap();
                if v.pending.is_none() && v.computed < v.len {
                    let n = 1 + (next() as usize) % (v.len - v.computed);
                    let (t, _) = m.begin_write(h, n).unwrap();
                    m.finish_write(t, Completion { ticket: t }).unwrap();
                }
            }
            2 if !live.is_empty() => {
                let i = (next() as usize) % live.len();
                let h = live.swap_remove(i);
                m.release(h).unwrap();
            }
            _ if !live.is_empty() => {
                let h = live[(next() as usize) % live.len()];
                let v = m.inspect(h).unwrap();
                if v.computed == v.len && v.len < 60 {
                    let _ = m.extend(h, &[(next() % 1000) as u32]);
                }
            }
            _ => {}
        }
    }
    for h in live {
        m.release(h).unwrap();
    }
    assert_eq!(m.free_count(), p);
}

#[test]
fn index_buckets_stay_bounded_under_churn() {
    // Many distinct prompts, each published then evicted by later fresh allocations. Before the
    // empty-bucket fix this left one empty bucket per distinct digest prefix ever published.
    let p = 8;
    let mut m = mgr(p, 4);
    for r in 0..5000u32 {
        let t = toks(9, r.wrapping_mul(7919));
        if let Ok((h, _, _)) = m.attach(&t) {
            compute_all(&mut m, h);
            m.release(h).unwrap();
        }
        assert!(m.index_bucket_count() <= p, "round {r}: {} buckets", m.index_bucket_count());
    }
    assert_eq!(m.free_count(), p);
}

#[test]
fn reclaim_revokes_the_keys_of_its_range() {
    // §3.5 rule 3, obligation 12: reclaiming a slab revokes every key in it. In a coordinator this
    // can't show as a lost hit, because reclaim needs a state class and a state class disables
    // hits (D13). So this checks it on one paged class, through the same `reclaim_range` and
    // `grant_range` the coordinator's slab plan calls. One page per slab.
    let t = toks(12, 41);
    for (revoked, cached) in [(1usize, 4usize), (0, 0)] {
        let mut m = mgr(4, 4);
        let (h, _, v) = m.attach(&t).unwrap();
        compute_all(&mut m, h);
        m.release(h).unwrap();
        // Control: with every slab kept, both complete blocks are hits.
        let (h, c, _) = m.attach(&t).unwrap();
        assert_eq!(c, 8);
        m.release(h).unwrap();
        // Reclaim the slab of block `revoked` and give it straight back: unowned, then a fresh
        // free page with no key.
        let pg = v.pages[revoked];
        assert!(m.range_idle(pg, 1));
        m.reclaim_range(pg, 1);
        m.grant_range(pg, 1);
        let (h, c, _) = m.attach(&t).unwrap();
        assert_eq!(c, cached, "block {revoked}'s key must be gone");
        m.release(h).unwrap();
    }
}
