//! Runtime checks of the contract v0.3 §7 edge cases against the verified coordinator: slab arena,
//! several paged classes, state classes, reclaim, Prot, and the all-or-nothing operations.
use pageproof_core::coord::Coordinator;
use pageproof_core::coord_attach::LeaseView;
use pageproof_core::coord_ops::{CoordCompletion, Drafts};
use pageproof_core::types::{Error, Handle};

const NS: &[u8] = b"dummy-v0.3";

/// A completion with no accepted drafts.
fn done(t: pageproof_core::types::Ticket) -> CoordCompletion {
    done_n(t, 0)
}

/// A completion accepting the first `n` drafts.
fn done_n(t: pageproof_core::types::Ticket, n: usize) -> CoordCompletion {
    CoordCompletion { ticket: t, accepted: n, token: None, drafts: vec![], stop: false }
}

fn toks(n: usize, seed: u32) -> Vec<u32> {
    (0..n as u32).map(|i| i.wrapping_mul(2654435761).wrapping_add(seed)).collect()
}

/// Computes the rest of a lease's input in one ticket.
fn compute_all(co: &mut Coordinator, h: Handle) {
    let v = co.inspect(h).unwrap();
    if v.computed < v.len {
        let (t, plan) = co.begin_write(h, v.len - v.computed, Drafts::Known(vec![]), false).unwrap();
        assert_eq!(plan.ticket, t);
        co.finish_write(t, done(t)).unwrap();
    }
}

fn owners(co: &Coordinator) -> Vec<usize> {
    co.arena().owner
}

fn count_owner(co: &Coordinator, c: usize) -> usize {
    owners(co).iter().filter(|&&o| o == c + 1).count()
}

fn free_slabs(co: &Coordinator) -> usize {
    owners(co).iter().filter(|&&o| o == 0).count()
}

/// Every unit a lease holds lies in a slab its class owns; distinct (class, unit) pairs of all
/// live leases occupy disjoint byte ranges.
fn check_disjoint(co: &Coordinator, units: &[usize], per: &[usize], views: &[&LeaseView], np: usize) {
    let own = owners(co);
    let mut ranges: Vec<(usize, usize, usize, usize)> = Vec::new();
    for v in views {
        for (c, t) in v.tables.iter().enumerate() {
            for &g in t {
                assert_eq!(own[g / per[c]], c + 1, "page {g} of class {c} outside its slabs");
                ranges.push((c, g, g * units[c], (g + 1) * units[c]));
            }
        }
        for (j, &g) in v.slots.iter().enumerate() {
            let c = np + j;
            assert_eq!(own[g / per[c]], c + 1, "slot {g} of class {c} outside its slabs");
            ranges.push((c, g, g * units[c], (g + 1) * units[c]));
        }
    }
    ranges.sort_by_key(|r| (r.2, r.0, r.1));
    ranges.dedup();
    for w in ranges.windows(2) {
        assert!(w[0].3 <= w[1].2 || (w[0].0 == w[1].0 && w[0].1 == w[1].1), "overlap {:?} {:?}", w[0], w[1]);
    }
}

#[test]
fn a1_rejects_non_dividing_unit() {
    // S = 1000 is not a multiple of 96.
    assert_eq!(Coordinator::create(4, 1000, &[96], &[], &[], 4, 0, 0, NS).err(), Some(Error::ConfigError));
    assert_eq!(Coordinator::create(0, 960, &[96], &[], &[], 4, 0, 0, NS).err(), Some(Error::ConfigError));
    assert_eq!(Coordinator::create(4, 960, &[], &[], &[96], 4, 0, 0, NS).err(), Some(Error::ConfigError));
    assert_eq!(Coordinator::create(4, 960, &[0], &[], &[], 4, 0, 0, NS).err(), Some(Error::ConfigError));
    assert!(Coordinator::create(4, 960, &[96], &[], &[320], 4, 0, 0, NS).is_ok());
}

#[test]
fn lcm_slab_layout() {
    // S = lcm(96 KiB, 640 KiB) = 1.875 MiB: 20 pages and 3 state slots per slab.
    let (u_p, u_s) = (96 * 1024, 640 * 1024);
    let s = 1966080;
    let mut co = Coordinator::create(2, s, &[u_p], &[], &[u_s], 4, 0, 0, NS).unwrap();
    let (h, cached, v) = co.attach(&toks(5, 1)).unwrap();
    assert_eq!(cached, 0);
    assert_eq!(v.tables[0].len(), 2);
    assert_eq!(v.slots.len(), 1);
    assert_eq!(count_owner(&co, 0), 1);
    assert_eq!(count_owner(&co, 1), 1);
    let a = co.arena();
    assert_eq!(a.free_units, vec![18, 2]);
    check_disjoint(&co, &[u_p, u_s], &[20, 3], &[&v], 1);
    co.release(h).unwrap();
}

#[test]
fn empty_and_too_large() {
    let mut co = Coordinator::create(2, 64, &[16], &[], &[], 4, 0, 0, NS).unwrap();
    assert_eq!(co.attach(&[]).err(), Some(Error::InvalidArgument));
    // 2 slabs x 4 pages x B=4 = 32 tokens fit; 33 do not.
    assert_eq!(co.attach(&toks(33, 0)).err(), Some(Error::RequestTooLarge));
    assert!(co.attach(&toks(32, 0)).is_ok());
}

#[test]
fn fits_counts_state_slabs() {
    // With a state class, one slab is reserved for its slot: 1 paged slab left => 16 tokens.
    let mut co = Coordinator::create(2, 64, &[16], &[], &[64], 4, 0, 0, NS).unwrap();
    assert_eq!(co.attach(&toks(17, 0)).err(), Some(Error::RequestTooLarge));
    assert!(co.attach(&toks(16, 0)).is_ok());
}

#[test]
fn prefix_hit_without_state_class() {
    let mut co = Coordinator::create(4, 64, &[16], &[], &[], 4, 0, 0, NS).unwrap();
    let t = toks(12, 3);
    let (h1, c1, v1) = co.attach(&t).unwrap();
    assert_eq!(c1, 0);
    compute_all(&mut co, h1);
    let (h2, c2, v2) = co.attach(&t).unwrap();
    // Reuse the first two blocks; the last is recomputed.
    assert_eq!(c2, 8);
    assert_eq!(&v2.tables[0][..2], &v1.tables[0][..2]);
    assert_ne!(v2.tables[0][2], v1.tables[0][2]);
    co.release(h1).unwrap();
    co.release(h2).unwrap();
}

#[test]
fn state_class_disables_hits() {
    let mut co = Coordinator::create(4, 64, &[16], &[], &[32], 4, 0, 0, NS).unwrap();
    let t = toks(12, 3);
    let (h1, _, v1) = co.attach(&t).unwrap();
    compute_all(&mut co, h1);
    let (h2, c2, v2) = co.attach(&t).unwrap();
    assert_eq!(c2, 0, "D13: no state checkpoints, no hits");
    assert_ne!(v1.slots[0], v2.slots[0], "distinct live slots");
    let (t2, plan) = co.begin_write(h2, 12, Drafts::Known(vec![]), false).unwrap();
    assert!(plan.init, "first plan starts from the initial state (E10)");
    assert_eq!(plan.state_slots, v2.slots);
    co.finish_write(t2, done(t2)).unwrap();
    check_disjoint(&co, &[16, 32], &[4, 2], &[&v1, &v2], 1);
}

#[test]
fn two_paged_classes_kstar_is_joint() {
    // Class 0 and class 1 share B and keys; a hit needs both classes.
    let mut co = Coordinator::create(6, 64, &[16, 32], &[], &[], 4, 0, 0, NS).unwrap();
    let t = toks(12, 9);
    let (h1, _, _) = co.attach(&t).unwrap();
    compute_all(&mut co, h1);
    co.release(h1).unwrap();
    let (h2, c2, v2) = co.attach(&t).unwrap();
    assert_eq!(c2, 8);
    assert_eq!(v2.tables.len(), 2);
    assert_eq!(v2.tables[0].len(), 3);
    assert_eq!(v2.tables[1].len(), 3);
    co.release(h2).unwrap();
}

#[test]
fn no_capacity_is_atomic() {
    // Paged class needs 2 more pages, has 1 free, no free slab, nothing reclaimable.
    let mut co = Coordinator::create(1, 48, &[16], &[], &[], 4, 0, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(8, 1)).unwrap();
    let before = co.arena();
    assert_eq!(co.attach(&toks(8, 2)).err(), Some(Error::NoCapacity));
    let after = co.arena();
    assert_eq!(before.owner, after.owner);
    assert_eq!(before.free_units, after.free_units);
    assert_eq!(co.inspect(h).unwrap().len, 8);
}

#[test]
fn free_slab_before_reclaim() {
    // A free slab exists and a reclaimable slab exists: the free slab is used.
    let mut co = Coordinator::create(3, 64, &[16], &[], &[64], 4, 0, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(4, 1)).unwrap();
    compute_all(&mut co, h);
    co.release(h).unwrap();
    // Now: one paged slab (idle, keyed), one state slab (idle), one free slab.
    assert_eq!(free_slabs(&co), 1);
    let (h2, _, _) = co.attach(&toks(4, 2)).unwrap();
    // The new lease fits in the owned slabs: nothing is reclaimed or granted.
    assert_eq!(free_slabs(&co), 1);
    co.release(h2).unwrap();
}

#[test]
fn reclaim_idle_keyed_slab_for_state() {
    // 4 slabs of 64 B. Paged unit 64 B (1 page per slab), state unit 64 B (1 slot per slab).
    let mut co = Coordinator::create(4, 64, &[64], &[], &[64], 4, 0, 0, NS).unwrap();
    // Lease A: 3 blocks -> 3 paged slabs, 1 state slab; FS = 0. Its blocks get published.
    let (ha, _, _) = co.attach(&toks(12, 1)).unwrap();
    compute_all(&mut co, ha);
    assert_eq!(free_slabs(&co), 0);
    co.release(ha).unwrap();
    // Release keeps slabs: 3 idle keyed paged slabs, 1 idle state slab.
    assert_eq!(count_owner(&co, 0), 3);
    assert_eq!(count_owner(&co, 1), 1);
    // Lease B: 1 block. Fits in owned units; nothing moves.
    let (hb, _, vb) = co.attach(&toks(4, 2)).unwrap();
    assert_eq!(count_owner(&co, 0), 3);
    // Lease C: 1 block. The state class has no free slot and FS is empty; the paged class keeps
    // 2 free pages for a demand of 1, so it gives up one idle (keyed) slab, which is reclaimed.
    let (hc, _, vc) = co.attach(&toks(4, 3)).unwrap();
    assert_eq!(count_owner(&co, 0), 2, "one idle keyed paged slab reclaimed");
    assert_eq!(count_owner(&co, 1), 2, "and granted to the state class");
    assert_eq!(free_slabs(&co), 0);
    check_disjoint(&co, &[64, 64], &[1, 1], &[&vb, &vc], 1);
    // Lease D: no free slot, no free slab, the paged class has no surplus: NoCapacity, atomically.
    let before = co.arena();
    assert_eq!(co.attach(&toks(4, 4)).err(), Some(Error::NoCapacity));
    assert_eq!(co.arena().owner, before.owner);
    co.release(hb).unwrap();
    co.release(hc).unwrap();
}

#[test]
fn reclaim_revokes_keys() {
    // Paged-only: reclaim moves an idle keyed slab from one paged class to another; afterwards the
    // revoked blocks can no longer be hit. Class 0: 1 page/slab; class 1: 4 pages/slab.
    let mut co = Coordinator::create(3, 64, &[64, 16], &[], &[], 4, 0, 0, NS).unwrap();
    let t = toks(8, 5);
    // Lease A (2 blocks): class 0 takes 2 slabs, class 1 takes 1 slab. FS = 0.
    let (ha, _, _) = co.attach(&t).unwrap();
    compute_all(&mut co, ha);
    co.release(ha).unwrap();
    assert_eq!(free_slabs(&co), 0);
    // Block 0 is a hit in both classes.
    let (hb, cb, _) = co.attach(&t).unwrap();
    assert_eq!(cb, 4);
    co.release(hb).unwrap();
    let a = co.arena();
    assert_eq!(a.reclaimable, vec![2, 1]);
}

#[test]
fn reclaim_paged_slab_for_other_paged_class() {
    // Two paged classes over 3 slabs: class 0 unit 16 (4/slab), class 1 unit 64 (1/slab).
    let mut co = Coordinator::create(3, 64, &[16, 64], &[], &[], 4, 0, 0, NS).unwrap();
    // A 1-block lease takes one slab per class; then release: both slabs idle, one free slab.
    let (h1, _, _) = co.attach(&toks(4, 1)).unwrap();
    compute_all(&mut co, h1);
    co.release(h1).unwrap();
    assert_eq!(free_slabs(&co), 1);
    // A 2-block lease: class 0 has 4 free units (enough), class 1 has 1 free unit and needs 2,
    // so it takes the free slab. No reclaim.
    let (h2, _, v2) = co.attach(&toks(8, 2)).unwrap();
    assert_eq!(free_slabs(&co), 0);
    assert_eq!(count_owner(&co, 0), 1);
    assert_eq!(count_owner(&co, 1), 2);
    check_disjoint(&co, &[16, 64], &[4, 1], &[&v2], 2);
    co.release(h2).unwrap();
}

#[test]
fn reclaim_when_free_slabs_run_out() {
    // 3 slabs. Class 0: unit 16 (4/slab). Class 1: unit 64 (1/slab).
    let mut co = Coordinator::create(3, 64, &[16, 64], &[], &[], 4, 0, 0, NS).unwrap();
    // Lease A: 5 blocks needs 2 slabs of class 0 and 5 of class 1: too large (Fits).
    assert_eq!(co.attach(&toks(20, 1)).err(), Some(Error::RequestTooLarge));
    // Lease A: 1 block => class 0 gets slab, class 1 gets slab.
    let (ha, _, _) = co.attach(&toks(4, 1)).unwrap();
    compute_all(&mut co, ha);
    // Lease B: 1 block => class 0 has room; class 1 takes the last free slab.
    let (hb, _, _) = co.attach(&toks(4, 2)).unwrap();
    compute_all(&mut co, hb);
    assert_eq!(free_slabs(&co), 0);
    co.release(ha).unwrap();
    co.release(hb).unwrap();
    // Now class 0 owns 1 slab (idle, keyed); class 1 owns 2 slabs (idle, keyed).
    // Lease C: 2 blocks => class 0 has 4 free (ok); class 1 has 2 free (ok). No moves.
    let (hc, _, vc) = co.attach(&toks(8, 3)).unwrap();
    assert_eq!(count_owner(&co, 1), 2);
    check_disjoint(&co, &[16, 64], &[4, 1], &[&vc], 2);
    co.release(hc).unwrap();
}

#[test]
fn prot_keeps_hit_slab() {
    // Class 0: unit 16 (4/slab). Class 1: unit 32 (2/slab). 3 slabs.
    let mut co = Coordinator::create(3, 64, &[16, 32], &[], &[], 4, 0, 0, NS).unwrap();
    let t = toks(8, 7);
    let (ha, _, va) = co.attach(&t).unwrap();
    compute_all(&mut co, ha);
    co.release(ha).unwrap();
    // The hit candidates for block 0 lie in idle slabs; re-attaching must not reclaim them.
    let (hb, cb, vb) = co.attach(&t).unwrap();
    assert_eq!(cb, 4);
    assert_eq!(vb.tables[0][0], va.tables[0][0]);
    assert_eq!(vb.tables[1][0], va.tables[1][0]);
    co.release(hb).unwrap();
}

#[test]
fn extend_demand_paged_only() {
    let mut co = Coordinator::create(4, 64, &[16], &[], &[64], 4, 0, 0, NS).unwrap();
    let (h, _, v) = co.attach(&toks(4, 1)).unwrap();
    compute_all(&mut co, h);
    let state_owned = count_owner(&co, 1);
    let v2 = co.extend(h, &toks(4, 2)).unwrap();
    assert_eq!(v2.tables[0].len(), 2);
    assert_eq!(&v2.tables[0][..1], &v.tables[0][..]);
    assert_eq!(v2.slots, v.slots);
    assert_eq!(count_owner(&co, 1), state_owned);
    // Phase errors.
    assert_eq!(co.extend(h, &toks(1, 3)).err(), Some(Error::InvalidPhase));
    compute_all(&mut co, h);
    assert_eq!(co.extend(h, &[]).err(), Some(Error::InvalidArgument));
    assert_eq!(co.begin_write(h, 0, Drafts::Known(vec![]), false).err(), Some(Error::InvalidArgument));
    let v3 = co.extend(h, &toks(1, 4)).unwrap();
    assert_eq!(v3.tables[0].len(), 3);
    let (t, _) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.extend(h, &toks(1, 5)).err(), Some(Error::Busy));
    assert_eq!(co.release(h).err(), Some(Error::Busy));
    co.finish_write(t, done(t)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn state_plan_after_first_chunk() {
    let mut co = Coordinator::create(4, 64, &[16], &[], &[64], 4, 0, 0, NS).unwrap();
    let (h, _, v) = co.attach(&toks(10, 1)).unwrap();
    let (t1, p1) = co.begin_write(h, 6, Drafts::Known(vec![]), false).unwrap();
    assert!(p1.init);
    assert_eq!(p1.write_slots.len(), 1);
    assert_eq!(p1.write_slots[0].len(), 6);
    co.finish_write(t1, done(t1)).unwrap();
    let (t2, p2) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    assert!(!p2.init, "later plans read the live slot");
    assert_eq!(p2.state_slots, v.slots);
    assert_eq!(p2.positions, (6..10).collect::<Vec<_>>());
    co.finish_write(t2, done(t2)).unwrap();
    assert_eq!(co.inspect(h).unwrap().computed, 10);
}

#[test]
fn tickets_and_handles_are_single_use() {
    let mut co = Coordinator::create(4, 64, &[16], &[], &[64], 4, 0, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(4, 1)).unwrap();
    let (t, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.begin_write(h, 1, Drafts::Known(vec![]), false).err(), Some(Error::Busy));
    co.finish_write(t, done(t)).unwrap();
    assert_eq!(co.finish_write(t, done(t)).err(), Some(Error::InvalidTicket));
    co.release(h).unwrap();
    assert_eq!(co.release(h).err(), Some(Error::InvalidHandle));
    assert!(co.inspect(h).is_err());
    // Handles of another coordinator are rejected.
    let mut other = Coordinator::create(4, 64, &[16], &[], &[64], 4, 0, 0, NS).unwrap();
    let (h2, _, _) = other.attach(&toks(4, 1)).unwrap();
    assert_eq!(co.release(h2).err(), Some(Error::InvalidHandle));
}

#[test]
fn release_keeps_slabs_and_makes_them_reclaimable() {
    let mut co = Coordinator::create(4, 64, &[16], &[], &[64], 4, 0, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(8, 1)).unwrap();
    compute_all(&mut co, h);
    let owned = owners(&co);
    co.release(h).unwrap();
    assert_eq!(owners(&co), owned, "release never returns slabs");
    let a = co.arena();
    assert!(a.reclaimable[0] >= 1);
    assert!(a.reclaimable[1] >= 1);
}

#[test]
fn churn_stays_disjoint_and_bounded() {
    let units = [16usize, 32, 64];
    let per = [4usize, 2, 1];
    let mut co = Coordinator::create(12, 64, &units[..2], &[], &units[2..], 4, 0, 0, NS).unwrap();
    let mut live: Vec<(Handle, LeaseView)> = Vec::new();
    let mut seed = 1u32;
    for step in 0..400 {
        seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
        let r = (seed >> 16) as usize;
        if !r.is_multiple_of(3) || live.is_empty() {
            let n = 1 + r % 14;
            let prompt = toks(n, (r % 5) as u32);
            match co.attach(&prompt) {
                Ok((h, _, v)) => {
                    compute_all(&mut co, h);
                    live.push((h, v));
                },
                Err(e) => assert!(e == Error::NoCapacity || e == Error::RequestTooLarge, "step {step}: {e:?}"),
            }
        } else {
            let (h, _) = live.swap_remove(r % live.len());
            co.release(h).unwrap();
        }
        let views: Vec<&LeaseView> = live.iter().map(|(_, v)| v).collect();
        check_disjoint(&co, &units, &per, &views, 2);
    }
}

// ---------------------------------------------------------------------------------------------
// Contract v0.4/v0.6 §7: the draft reservation (D18, I16). No drafter class and δ = 0 here, so
// μ = λ.
// ---------------------------------------------------------------------------------------------

#[test]
fn reservation_sizes_page_tables() {
    // §7: attach of L = 2B - 1 with λ = 3, B = 64 covers ceil(130/64) = 3 blocks, not 2.
    let mut co = Coordinator::create(4, 64, &[16], &[], &[], 64, 3, 0, NS).unwrap();
    let (h, cached, v) = co.attach(&toks(127, 1)).unwrap();
    assert_eq!(cached, 0);
    assert_eq!(v.tables[0].len(), 3);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.reach, iv.lam, iv.mu, iv.delta), (127, 130, 3, 3, 0));
    // Every position of the reach has a slot; past it there is none (C6).
    assert!(co.slot_of(0, h, 129).is_ok());
    assert_eq!(co.slot_of(0, h, 130).err(), Some(Error::InvalidArgument));
    compute_all(&mut co, h);
    assert_eq!(co.inspect(h).unwrap().computed, 127);
    co.release(h).unwrap();
}

#[test]
fn reservation_counts_for_fits() {
    // §7: Fits(ceil(L/B)) holds but Fits(ceil((L+μ)/B)) does not => RequestTooLarge.
    // 2 slabs x 4 pages x B=4 = 32 slots; with λ = 3, L = 32 needs ceil(35/4) = 9 pages.
    let mut co = Coordinator::create(2, 64, &[16], &[], &[], 4, 3, 0, NS).unwrap();
    assert_eq!(co.attach(&toks(32, 0)).err(), Some(Error::RequestTooLarge));
    assert_eq!(co.attach(&toks(30, 0)).err(), Some(Error::RequestTooLarge));
    assert!(co.attach(&toks(29, 0)).is_ok());
}

#[test]
fn reservation_counts_for_capacity() {
    // The reserved blocks are part of the demand: with λ = 4 a 12-token lease takes 4 pages.
    let mut co = Coordinator::create(2, 64, &[16], &[], &[], 4, 4, 0, NS).unwrap();
    let (h1, _, v1) = co.attach(&toks(12, 1)).unwrap();
    let (h2, _, v2) = co.attach(&toks(12, 2)).unwrap();
    assert_eq!((v1.tables[0].len(), v2.tables[0].len()), (4, 4));
    assert_eq!(free_slabs(&co), 0);
    // A one-token lease still needs ceil(5/4) = 2 pages, and none are left.
    assert_eq!(co.attach(&toks(1, 3)).err(), Some(Error::NoCapacity));
    co.release(h1).unwrap();
    co.release(h2).unwrap();
}

#[test]
fn extend_reuses_reserved_pages() {
    // C2: pages already reserved at [L, ρ_h) serve the suffix. λ = 3, B = 4: L = 4 gives ρ = 7
    // (2 pages); extending by 1 gives ρ' = 8, still 2 pages, so the demand is 0.
    let mut co = Coordinator::create(2, 64, &[16], &[], &[], 4, 3, 0, NS).unwrap();
    let (h, _, v) = co.attach(&toks(4, 5)).unwrap();
    assert_eq!(v.tables[0].len(), 2);
    compute_all(&mut co, h);
    let slot4 = co.slot_of(0, h, 4).unwrap();
    let free_before = co.arena().free_units[0];
    let v2 = co.extend(h, &[7]).unwrap();
    assert_eq!(v2.tables[0], v.tables[0]);
    assert_eq!(co.arena().free_units[0], free_before);
    assert_eq!(co.slot_of(0, h, 4).unwrap(), slot4);
    assert_eq!(co.inspect(h).unwrap().reach, 8);
    // Extending past the reserved pages takes a new one: L' = 6 gives ρ' = 9, 3 pages.
    compute_all(&mut co, h);
    let v3 = co.extend(h, &[8]).unwrap();
    assert_eq!(v3.tables[0].len(), 3);
    assert_eq!(&v3.tables[0][..2], &v.tables[0][..]);
    co.release(h).unwrap();
}

#[test]
fn release_returns_reserved_pages() {
    // §7: reserved pages past L_h return to F_c unkeyed.
    let mut co = Coordinator::create(2, 64, &[16], &[], &[], 4, 3, 0, NS).unwrap();
    let (h, _, v) = co.attach(&toks(4, 9)).unwrap();
    assert_eq!(v.tables[0].len(), 2);
    assert_eq!(co.arena().free_units[0], 2);
    compute_all(&mut co, h);
    co.release(h).unwrap();
    assert_eq!(co.arena().free_units[0], 4);
    // The published block is still a hit; the reserved page was never published.
    let (h2, cached, _) = co.attach(&toks(5, 9)).unwrap();
    assert_eq!(cached, 4);
    co.release(h2).unwrap();
}

#[test]
fn create_rejects_unfittable_reservation() {
    // C0: ¬Fits(ceil((1 + μ)/B)) is a ConfigError. One slab of 4 pages, B = 4: 16 slots.
    assert_eq!(Coordinator::create(1, 64, &[16], &[], &[], 4, 16, 0, NS).err(), Some(Error::ConfigError));
    assert!(Coordinator::create(1, 64, &[16], &[], &[], 4, 15, 0, NS).is_ok());
    // A state class takes a slab of its own.
    assert_eq!(Coordinator::create(2, 64, &[16], &[], &[64], 4, 16, 0, NS).err(), Some(Error::ConfigError));
    assert!(Coordinator::create(2, 64, &[16], &[], &[64], 4, 15, 0, NS).is_ok());
}

#[test]
fn lambda_zero_has_no_reservation() {
    // Obligation 18: with λ = 0 the reach is the input.
    let mut co = Coordinator::create(2, 64, &[16], &[], &[], 4, 0, 0, NS).unwrap();
    let (h, _, v) = co.attach(&toks(5, 1)).unwrap();
    assert_eq!(v.tables[0].len(), 2);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.reach, iv.mu), (5, 0));
    assert_eq!(co.slot_of(0, h, 5).err(), Some(Error::InvalidArgument));
}

// ---------------------------------------------------------------------------------------------
// Contract v0.4/v0.6 §7: verify tickets with linear drafts (D16, D17, D19). B = 4 throughout.
// ---------------------------------------------------------------------------------------------

/// A lease with `len` tokens, all computed, on a coordinator with λ = `lam`.
fn computed_lease(nslab: usize, lam: usize, len: usize, seed: u32) -> (Coordinator, Handle) {
    let mut co = Coordinator::create(nslab, 64, &[16], &[], &[], 4, lam, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(len, seed)).unwrap();
    compute_all(&mut co, h);
    (co, h)
}

/// A verify ticket over the last input position `L - 1` with `drafts`.
fn verify(co: &mut Coordinator, h: Handle, drafts: &[u32]) -> pageproof_core::types::Ticket {
    // The caller has extended the lease by one token, so the frontier is at L - 1.
    let (t, plan) = co.begin_write(h, 1, Drafts::Known(drafts.to_vec()), false).unwrap();
    assert_eq!(plan.num_drafts, drafts.len());
    t
}

#[test]
fn verify_accepts_every_draft() {
    // §7: k = 4, n = 4: T' = T ++ D, c' = L' = L + 4, and ρ - L' = λ - 4 = 0.
    let (mut co, h) = computed_lease(4, 4, 5, 1);
    co.extend(h, &[50]).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.reach), (6, 5, 10));
    let d = [51, 52, 53, 54];
    let (t, plan) = co.begin_write(h, 1, Drafts::Known(d.to_vec()), false).unwrap();
    assert_eq!(plan.input_ids, vec![50, 51, 52, 53, 54]);
    assert_eq!(plan.positions, vec![5, 6, 7, 8, 9]);
    assert_eq!(plan.write_slots[0].len(), 5);
    for (q, s) in plan.write_slots[0].iter().enumerate() {
        assert_eq!(*s, co.slot_of(0, h, 5 + q).unwrap());
    }
    assert_eq!(co.finish_write(t, done_n(t, 4)).unwrap(), 10);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.reach), (10, 10, 10));
    // Blocks 0 and 1 (positions 0..7, two of them accepted drafts) are published and hit.
    let mut t2 = toks(5, 1);
    t2.extend_from_slice(&[50, 51, 52, 53]);
    let (h2, cached, _) = co.attach(&t2).unwrap();
    assert_eq!(cached, 8);
    co.release(h2).unwrap();
    co.release(h).unwrap();
}

#[test]
fn verify_rejects_every_draft() {
    // §7: k = 4, n = 0: T and c = L as before; nothing credited, freed or published.
    let (mut co, h) = computed_lease(4, 4, 5, 2);
    co.extend(h, &[60]).unwrap();
    let free = co.arena().free_units[0];
    let t = verify(&mut co, h, &[61, 62, 63, 64]);
    assert_eq!(co.finish_write(t, done_n(t, 0)).unwrap(), 6);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.reach), (6, 6, 10));
    assert_eq!(co.arena().free_units[0], free);
    // A second verify needs the bonus token first.
    assert_eq!(co.begin_write(h, 1, Drafts::Known(vec![1]), false).err(), Some(Error::InvalidArgument));
    co.extend(h, &[65]).unwrap();
    assert_eq!(co.inspect(h).unwrap().reach, 11);
    let t = verify(&mut co, h, &[66, 67]);
    co.finish_write(t, done(t)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn verify_partial_accept_publishes_completed_block() {
    // §7: k = 4, n = 2, where the second accepted draft completes block 1 (positions 4..7).
    let (mut co, h) = computed_lease(4, 4, 5, 3);
    co.extend(h, &[70]).unwrap();
    let t = verify(&mut co, h, &[71, 72, 73, 74]);
    assert_eq!(co.finish_write(t, done_n(t, 2)).unwrap(), 8);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed), (8, 8));
    let mut t2 = toks(5, 3);
    t2.extend_from_slice(&[70, 71, 72, 99]);
    let (h2, cached, _) = co.attach(&t2).unwrap();
    assert_eq!(cached, 8);
    co.release(h2).unwrap();
    co.release(h).unwrap();
}

#[test]
fn rejected_drafts_never_publish() {
    // §7: drafts that would complete block 1 are rejected: the block is not published, and the
    // same tokens find no cached block 1.
    let (mut co, h) = computed_lease(4, 4, 5, 4);
    co.extend(h, &[80]).unwrap();
    let t = verify(&mut co, h, &[81, 82, 83, 84]);
    co.finish_write(t, done_n(t, 0)).unwrap();
    let mut t2 = toks(5, 4);
    t2.extend_from_slice(&[80, 81, 82, 83]);
    let (h2, cached, _) = co.attach(&t2).unwrap();
    assert_eq!(cached, 4);
    co.release(h2).unwrap();
    co.release(h).unwrap();
}

#[test]
fn finish_write_rejects_bad_acceptance_counts() {
    // §7: n > k, or n > 0 for k = 0: InvalidArgument, the ticket stays pending; a second delivery
    // of the same completion is InvalidTicket.
    let (mut co, h) = computed_lease(4, 4, 5, 5);
    co.extend(h, &[90]).unwrap();
    let t = verify(&mut co, h, &[91, 92]);
    assert_eq!(co.finish_write(t, done_n(t, 3)).err(), Some(Error::InvalidArgument));
    assert_eq!(co.finish_write(t, done_n(t, 1)).unwrap(), 7);
    assert_eq!(co.finish_write(t, done_n(t, 0)).err(), Some(Error::InvalidTicket));
    assert_eq!(co.inspect(h).unwrap().len, 7);
    co.extend(h, &[93]).unwrap();
    let (t2, _) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.finish_write(t2, done_n(t2, 1)).err(), Some(Error::InvalidArgument));
    co.finish_write(t2, done(t2)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn begin_write_rejects_misplaced_drafts() {
    // §7: drafts while c + n < L, more than λ drafts, or `propose` without a drafter class.
    let (mut co, h) = computed_lease(4, 4, 5, 6);
    co.extend(h, &[1, 2]).unwrap();
    assert_eq!(co.begin_write(h, 1, Drafts::Known(vec![9]), false).err(), Some(Error::InvalidArgument));
    assert_eq!(co.begin_write(h, 2, Drafts::Known(vec![9; 5]), false).err(), Some(Error::InvalidArgument));
    assert_eq!(co.begin_write(h, 2, Drafts::Known(vec![]), true).err(), Some(Error::InvalidArgument));
    assert_eq!(co.begin_write(h, 2, Drafts::Deferred(1), false).err(), Some(Error::InvalidArgument));
    let (t, plan) = co.begin_write(h, 2, Drafts::Known(vec![9; 4]), false).unwrap();
    assert_eq!(plan.input_ids.len(), 6);
    co.finish_write(t, done(t)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn verify_on_a_hybrid_lease() {
    // §7: a ticket over the whole prompt (a = 0) with k > 0 drafts on a lease with a state class:
    // init = true; the single state slot is the plan's, and no second slot is ever allocated.
    let mut co = Coordinator::create(4, 64, &[16], &[], &[64], 4, 3, 0, NS).unwrap();
    let (h, _, v) = co.attach(&toks(5, 7)).unwrap();
    let (t, plan) = co.begin_write(h, 5, Drafts::Known(vec![1, 2, 3]), false).unwrap();
    assert!(plan.init);
    assert_eq!(plan.num_drafts, 3);
    assert_eq!(plan.state_slots, v.slots);
    assert_eq!(co.finish_write(t, done_n(t, 1)).unwrap(), 6);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed), (6, 6));
    assert_eq!(iv.lease.slots, v.slots);
    co.release(h).unwrap();
}

#[test]
fn extend_after_every_draft_accepted() {
    // §7: after n = λ the reservation is used up (ρ = L'), and the bonus-token extend needs
    // ceil((L' + 1 + μ)/B) - m_h new pages.
    let (mut co, h) = computed_lease(4, 4, 5, 8);
    co.extend(h, &[40]).unwrap();
    let t = verify(&mut co, h, &[41, 42, 43, 44]);
    co.finish_write(t, done_n(t, 4)).unwrap();
    let pages = co.inspect(h).unwrap().lease.tables[0].len();
    assert_eq!(pages, 3);
    let v = co.extend(h, &[45]).unwrap();
    assert_eq!(v.tables[0].len(), 4);
    assert_eq!(co.inspect(h).unwrap().reach, 15);
    co.release(h).unwrap();
}

#[test]
fn stop_is_not_yet_supported() {
    // D25 lands with continuations; until then a completion with `stop` is rejected.
    let (mut co, h) = computed_lease(4, 4, 5, 9);
    co.extend(h, &[30]).unwrap();
    let t = verify(&mut co, h, &[31]);
    let mut c = done(t);
    c.stop = true;
    assert_eq!(co.finish_write(t, c).err(), Some(Error::InvalidArgument));
    co.finish_write(t, done(t)).unwrap();
    co.release(h).unwrap();
}

// ---------------------------------------------------------------------------------------------
// Contract v0.4.1/v0.6 §7: drafter classes and proposal rows (D20). B = 4; one target class
// (units 16) and one drafter class (units 16), so μ = 2λ.
// ---------------------------------------------------------------------------------------------

fn drafter_coord(nslab: usize, lam: usize) -> Coordinator {
    Coordinator::create(nslab, 64, &[16], &[16], &[], 4, lam, 0, NS).unwrap()
}

#[test]
fn drafter_classes_need_drafts() {
    // §7: Cx ≠ ∅ with λ = 0 is a ConfigError; so is a configuration with only drafter classes.
    assert_eq!(Coordinator::create(4, 64, &[16], &[16], &[], 4, 0, 0, NS).err(), Some(Error::ConfigError));
    assert_eq!(Coordinator::create(4, 64, &[], &[16], &[], 4, 2, 0, NS).err(), Some(Error::ConfigError));
    // δ is capped at 1.
    assert_eq!(Coordinator::create(4, 64, &[16], &[], &[], 4, 2, 2, NS).err(), Some(Error::ConfigError));
}

#[test]
fn drafter_reservation_is_two_lambda() {
    // §7: attach of L with λ = 4 and a drafter class: μ = 8, and every paged class (target and
    // drafter) covers ceil((L + 8)/B) blocks.
    let mut co = drafter_coord(8, 4);
    let (h, _, v) = co.attach(&toks(5, 1)).unwrap();
    assert_eq!((v.tables.len(), v.tables[0].len(), v.tables[1].len()), (2, 4, 4));
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.reach, iv.mu, iv.lam), (13, 8, 4));
    co.release(h).unwrap();
}

#[test]
fn proposal_rows_widen_the_drafter_plan() {
    // §7: a verify with k = 4 and `propose`: the target class writes [a, z + 4), the drafter class
    // [a, z + 4 + λ). After n = 2, c' = z + 2 in every class; no slot at or past z + 2 is credited.
    let mut co = drafter_coord(8, 4);
    let (h, _, _) = co.attach(&toks(5, 2)).unwrap();
    compute_all(&mut co, h);
    co.extend(h, &[50]).unwrap();
    let (t, plan) = co.begin_write(h, 1, Drafts::Known(vec![51, 52, 53, 54]), true).unwrap();
    assert!(plan.propose);
    assert_eq!(plan.input_ids.len(), 5);
    assert_eq!(plan.write_slots[0].len(), 5);
    assert_eq!(plan.write_slots[1].len(), 9);
    for (q, s) in plan.write_slots[1].iter().enumerate() {
        assert_eq!(*s, co.slot_of(1, h, 5 + q).unwrap());
    }
    assert_eq!(co.finish_write(t, done_n(t, 2)).unwrap(), 8);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed), (8, 8));
    // The next verify, after the bonus token, starts at the bonus position z + 2 and may propose.
    co.extend(h, &[55]).unwrap();
    let (t2, p2) = co.begin_write(h, 1, Drafts::Known(vec![56]), true).unwrap();
    assert_eq!(p2.positions[0], 8);
    co.finish_write(t2, done(t2)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn proposal_rows_end_at_the_reach() {
    // §7: k = λ, all accepted, with `propose`: the proposal rows end at z + 2λ = ρ_h; no
    // allocation.
    let mut co = drafter_coord(8, 2);
    let (h, _, _) = co.attach(&toks(3, 3)).unwrap();
    compute_all(&mut co, h);
    co.extend(h, &[60]).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.reach), (4, 8));
    let free = co.arena().free_units.clone();
    let (t, plan) = co.begin_write(h, 1, Drafts::Known(vec![61, 62]), true).unwrap();
    assert_eq!(plan.write_slots[1].len(), 5);
    assert!(co.slot_of(1, h, 7).is_ok());
    assert_eq!(co.arena().free_units, free);
    co.finish_write(t, done_n(t, 2)).unwrap();
    assert_eq!(co.arena().free_units, free);
    co.release(h).unwrap();
}

#[test]
fn propose_requires_the_end_of_the_input() {
    // §7: `propose` with c_h + n < L_h is InvalidArgument.
    let mut co = drafter_coord(8, 2);
    let (h, _, _) = co.attach(&toks(6, 4)).unwrap();
    assert_eq!(co.begin_write(h, 3, Drafts::Known(vec![]), true).err(), Some(Error::InvalidArgument));
    let (t, plan) = co.begin_write(h, 6, Drafts::Known(vec![]), true).unwrap();
    assert_eq!((plan.write_slots[0].len(), plan.write_slots[1].len()), (6, 8));
    co.finish_write(t, done(t)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn drafter_and_target_pages_are_hit_together() {
    // §7: the joint k* runs over target and drafter classes; both publish their blocks together.
    let mut co = drafter_coord(8, 2);
    let t = toks(9, 5);
    let (h1, _, v1) = co.attach(&t).unwrap();
    compute_all(&mut co, h1);
    let (h2, cached, v2) = co.attach(&t).unwrap();
    assert_eq!(cached, 8);
    assert_eq!(&v2.tables[0][..2], &v1.tables[0][..2]);
    assert_eq!(&v2.tables[1][..2], &v1.tables[1][..2]);
    co.release(h1).unwrap();
    co.release(h2).unwrap();
}

// ---- v0.5 ZOS: ticket queues of up to δ + 1 tickets (D21) ----

/// One target class and one state class, `δ = 1`.
fn zos_coord(nslab: usize, lam: usize) -> Coordinator {
    Coordinator::create(nslab, 64, &[16], &[], &[8], 4, lam, 1, NS).unwrap()
}

#[test]
fn zos_reach_is_two_lambda() {
    // D18: μ = (δ + 1)·λ; δ > 1 is a ConfigError.
    let mut co = zos_coord(8, 2);
    let (h, _, _) = co.attach(&toks(5, 20)).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.mu, iv.delta, iv.reach), (4, 1, 9));
    assert_eq!(Coordinator::create(8, 64, &[16], &[], &[], 4, 2, 2, NS).err(), Some(Error::ConfigError));
    co.release(h).unwrap();
}

#[test]
fn zos_pipelined_chunks() {
    // §7: two chunks in flight; the second plans from p_h, not c_h; finishes run in order.
    let mut co = zos_coord(8, 1);
    let (h, _, _) = co.attach(&toks(12, 21)).unwrap();
    let (t1, p1) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    let (t2, p2) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(p1.positions, vec![0, 1, 2, 3]);
    assert_eq!(p2.positions, vec![4, 5, 6, 7]);
    assert!(p1.init && !p2.init);
    assert_eq!(p1.state_slots, p2.state_slots);
    for (q, s) in p2.write_slots[0].iter().enumerate() {
        assert_eq!(*s, co.slot_of(0, h, 4 + q).unwrap());
    }
    // A third ticket overflows the queue.
    assert_eq!(co.begin_write(h, 4, Drafts::Known(vec![]), false).err(), Some(Error::Busy));
    // Out of order: only the oldest ticket can finish.
    assert_eq!(co.finish_write(t2, done(t2)).err(), Some(Error::InvalidTicket));
    assert_eq!(co.inspect(h).unwrap().pending, Some(t1));
    assert_eq!(co.finish_write(t1, done(t1)).unwrap(), 4);
    assert_eq!(co.inspect(h).unwrap().computed, 4);
    let (t3, p3) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(p3.positions, vec![8, 9, 10, 11]);
    assert_eq!(co.finish_write(t2, done(t2)).unwrap(), 8);
    assert_eq!(co.finish_write(t3, done(t3)).unwrap(), 12);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.computed, iv.pending), (12, None));
    co.release(h).unwrap();
}

#[test]
fn zos_drafts_need_an_empty_queue() {
    // D21: host-known drafts behind a pending ticket are Busy; without drafts the chunk queues.
    let mut co = zos_coord(8, 2);
    let (h, _, _) = co.attach(&toks(8, 22)).unwrap();
    let (t1, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.begin_write(h, 4, Drafts::Known(vec![7]), false).err(), Some(Error::Busy));
    let (t2, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    co.finish_write(t1, done(t1)).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    // With an empty queue drafts are accepted again.
    co.extend(h, &[9]).unwrap();
    let (t3, p3) = co.begin_write(h, 1, Drafts::Known(vec![10, 11]), false).unwrap();
    assert_eq!(p3.num_drafts, 2);
    co.finish_write(t3, done_n(t3, 1)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn zos_extend_with_a_pending_ticket() {
    // D21: extend is allowed while a k = 0 ticket covering the whole input is pending.
    let mut co = zos_coord(8, 1);
    let (h, _, _) = co.attach(&toks(8, 23)).unwrap();
    let (t1, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    // Positions [4, 8) are neither computed nor planned.
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::InvalidPhase));
    let (t2, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    // A full queue is Busy for extend too.
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::Busy));
    co.finish_write(t1, done(t1)).unwrap();
    co.extend(h, &[1, 2]).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.reach), (10, 4, 12));
    let (t3, p3) = co.begin_write(h, 2, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(p3.positions, vec![8, 9]);
    co.finish_write(t2, done(t2)).unwrap();
    co.finish_write(t3, done(t3)).unwrap();
    assert_eq!(co.inspect(h).unwrap().computed, 10);
    co.release(h).unwrap();
}

#[test]
fn zos_extend_behind_a_verify_is_busy() {
    // D21: a pending ticket with drafts makes extend Busy.
    let mut co = zos_coord(8, 2);
    let (h, _, _) = co.attach(&toks(4, 24)).unwrap();
    compute_all(&mut co, h);
    co.extend(h, &[5]).unwrap();
    let (t, _) = co.begin_write(h, 1, Drafts::Known(vec![6]), false).unwrap();
    assert_eq!(co.extend(h, &[7]).err(), Some(Error::Busy));
    co.finish_write(t, done(t)).unwrap();
    co.extend(h, &[7]).unwrap();
    co.release(h).unwrap();
}

#[test]
fn delta_zero_rejects_a_second_ticket() {
    // §7: with δ = 0 the queue holds one ticket.
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 1, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(8, 25)).unwrap();
    let (t, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.begin_write(h, 4, Drafts::Known(vec![]), false).err(), Some(Error::Busy));
    co.finish_write(t, done(t)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn zos_release_with_pending_tickets_is_busy() {
    let mut co = zos_coord(8, 1);
    let (h, _, _) = co.attach(&toks(8, 26)).unwrap();
    let (t1, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    let (t2, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.release(h).err(), Some(Error::Busy));
    co.finish_write(t1, done(t1)).unwrap();
    assert_eq!(co.release(h).err(), Some(Error::Busy));
    co.finish_write(t2, done(t2)).unwrap();
    co.release(h).unwrap();
}

// ---- v0.5 deferred tail: extend_deferred and continuations (D22, D24 with s = 0, k = 0) ----

fn tok(t: pageproof_core::types::Ticket, x: u32) -> CoordCompletion {
    CoordCompletion { ticket: t, accepted: 0, token: Some(x), drafts: vec![], stop: false }
}

#[test]
fn deferred_decode_loop() {
    // §7: the next decode step is planned before the previous step's token reaches the host.
    let mut co = Coordinator::create(8, 64, &[16], &[], &[8], 4, 0, 1, NS).unwrap();
    let (h, _, _) = co.attach(&toks(5, 30)).unwrap();
    let (t1, _) = co.begin_write(h, 5, Drafts::Known(vec![]), false).unwrap();
    co.extend_deferred(h).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.deferred, iv.reach), (5, true, 6));
    // The continuation reads the deferred position; its inputs are placeholders.
    let (t2, p2) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(p2.producer, Some(t1));
    assert_eq!((p2.input_ids.clone(), p2.positions.clone()), (vec![0], vec![5]));
    assert!(!p2.init);
    assert_eq!(p2.write_slots[0], vec![co.slot_of(0, h, 5).unwrap()]);
    // The producer heads X_h: its completion must carry the token.
    assert_eq!(co.finish_write(t1, done(t1)).err(), Some(Error::InvalidArgument));
    assert_eq!(co.finish_write(t1, tok(t1, 77)).unwrap(), 5);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.deferred), (6, 5, false));
    // Steady state: one step in flight, the next planned behind it.
    co.extend_deferred(h).unwrap();
    let (t3, p3) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    assert_eq!((p3.producer, p3.positions.clone()), (Some(t2), vec![6]));
    assert_eq!(co.finish_write(t2, tok(t2, 78)).unwrap(), 6);
    // t3 does not head X_h: its token is the caller's, not the lease's.
    assert_eq!(co.finish_write(t3, tok(t3, 79)).unwrap(), 7);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.pending, iv.deferred), (7, 7, None, false));
    assert_eq!(&co.release(h).unwrap()[5..], &[77, 78]);
}

#[test]
fn extend_deferred_phase_errors() {
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 0, 1, NS).unwrap();
    let (h, _, _) = co.attach(&toks(8, 31)).unwrap();
    // No pending ticket: nothing to defer.
    assert_eq!(co.extend_deferred(h).err(), Some(Error::InvalidPhase));
    let (t1, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    // The newest ticket does not end at L.
    assert_eq!(co.extend_deferred(h).err(), Some(Error::InvalidPhase));
    let (t2, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    // A full queue is Busy.
    assert_eq!(co.extend_deferred(h).err(), Some(Error::Busy));
    co.finish_write(t1, done(t1)).unwrap();
    co.extend_deferred(h).unwrap();
    // X_h is full; extend needs every input known.
    assert_eq!(co.extend_deferred(h).err(), Some(Error::InvalidPhase));
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::InvalidPhase));
    // Known inputs past p_h are gone: only the one-token continuation fits.
    assert_eq!(co.begin_write(h, 2, Drafts::Known(vec![]), false).err(), Some(Error::InvalidArgument));
    assert_eq!(co.begin_write(h, 1, Drafts::Known(vec![5]), false).err(), Some(Error::Busy));
    assert_eq!(co.release(h).err(), Some(Error::Busy));
    co.finish_write(t2, tok(t2, 9)).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.deferred, iv.pending), (9, 8, false, None));
    // The bound token at position 8 is known but not computed yet.
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::InvalidPhase));
    compute_all(&mut co, h);
    co.extend(h, &[1]).unwrap();
    co.release(h).unwrap();
}

#[test]
fn extend_deferred_with_delta_zero_never_succeeds() {
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 1, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(4, 32)).unwrap();
    assert_eq!(co.extend_deferred(h).err(), Some(Error::InvalidPhase));
    let (t, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.extend_deferred(h).err(), Some(Error::Busy));
    co.finish_write(t, done(t)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn extend_deferred_allocates_across_a_block() {
    // §3.5: extend_deferred's demand is ceil((L̂' + μ)/B) - m_h pages per paged class.
    let mut co = Coordinator::create(4, 64, &[16], &[], &[], 4, 0, 1, NS).unwrap();
    let (h, _, v) = co.attach(&toks(4, 33)).unwrap();
    assert_eq!(v.tables[0].len(), 1);
    let (t1, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    let lv = co.extend_deferred(h).unwrap();
    assert_eq!(lv.tables[0].len(), 2);
    assert_eq!(&lv.tables[0][..1], &v.tables[0][..]);
    let (t2, p2) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(p2.write_slots[0], vec![lv.tables[0][1] * 4]);
    co.finish_write(t1, tok(t1, 3)).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn extend_deferred_needs_capacity() {
    // One slab of four 16-byte pages; the lease fills it exactly, so the deferred position needs
    // a fifth page.
    let mut co = Coordinator::create(1, 64, &[16], &[], &[], 4, 0, 1, NS).unwrap();
    let (h, _, _) = co.attach(&toks(16, 34)).unwrap();
    let (t1, _) = co.begin_write(h, 16, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.extend_deferred(h).err(), Some(Error::RequestTooLarge));
    let iv = co.inspect(h).unwrap();
    assert!(!iv.deferred);
    co.finish_write(t1, done(t1)).unwrap();
    co.release(h).unwrap();
}
