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
fn release_leaves_idle_keyed_slabs_reclaimable() {
    // Paged-only: after release, idle keyed slabs count as reclaimable while their blocks remain
    // hits. (Without a state class no paged slab is ever reclaimed: every paged class grows in
    // lockstep, so none is ever short while another has an idle slab to spare.) Class 0: 1
    // page/slab; class 1: 4 pages/slab.
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
fn second_paged_class_takes_the_free_slab() {
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
fn stop_after_a_verify_without_zos() {
    // D25 with δ = 0: stop commits the accepted prefix and stops the lease.
    let (mut co, h) = computed_lease(4, 4, 5, 9);
    co.extend(h, &[30]).unwrap();
    let t = verify(&mut co, h, &[31]);
    let mut c = done_n(t, 1);
    c.stop = true;
    co.finish_write(t, c).unwrap();
    let iv = co.inspect(h).unwrap();
    assert!(iv.stopped && iv.pending.is_none());
    assert_eq!(co.extend(h, &[32]).err(), Some(Error::InvalidPhase));
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

// ---- v0.6 ZOS with speculative decoding: continuations behind a verify (D24) ----
// §7: B = 4, λ = 2, one drafter class, δ = 1, μ = 3λ = 6.

fn spec_coord() -> Coordinator {
    Coordinator::create(8, 64, &[16], &[16], &[], 4, 2, 1, NS).unwrap()
}

fn comp(t: pageproof_core::types::Ticket, n: usize, x: Option<u32>, drafts: Vec<u32>) -> CoordCompletion {
    CoordCompletion { ticket: t, accepted: n, token: x, drafts, stop: false }
}

/// A lease with `L = 7`, `c_h = 6`, `ρ_h = 13`.
fn lease_l7(co: &mut Coordinator) -> Handle {
    let (h, _, _) = co.attach(&toks(7, 40)).unwrap();
    let (t, _) = co.begin_write(h, 6, Drafts::Known(vec![]), false).unwrap();
    co.finish_write(t, done(t)).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.reach, iv.mu), (7, 6, 13, 6));
    h
}

#[test]
fn continuation_behind_a_verify() {
    let mut co = spec_coord();
    let h = lease_l7(&mut co);
    // Verify t1: target slots 6-8, drafter slots 6-10; p_h = 7, s_h = 2.
    let (t1, p1) = co.begin_write(h, 1, Drafts::Known(vec![101, 102]), true).unwrap();
    assert_eq!((p1.write_slots[0].len(), p1.write_slots[1].len()), (3, 5));
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.planned, iv.slack), (7, 2));
    // extend_deferred behind the verify: L̂ = 8, ρ = 14.
    co.extend_deferred(h).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.deferred, iv.reach), (7, true, 14));
    // The continuation t2: lo = 7, s = 2, ℓ = 1, k = 2; target 7-11, drafter 7-13; no allocation.
    let free = co.arena().free_units.clone();
    let (t2, p2) = co.begin_write(h, 1, Drafts::Deferred(2), true).unwrap();
    assert_eq!((p2.lo, p2.slack, p2.num_inputs, p2.num_drafts), (7, 2, 1, 2));
    assert_eq!(p2.producer, Some(t1));
    assert_eq!(p2.input_ids, vec![0, 0, 0]);
    assert_eq!(p2.positions, vec![7, 8, 9]);
    assert_eq!((p2.write_slots[0].len(), p2.write_slots[1].len()), (5, 7));
    for (q, s) in p2.write_slots[1].iter().enumerate() {
        assert_eq!(*s, co.slot_of(1, h, 7 + q).unwrap());
    }
    // μ = 3λ is tight: the last proposal row is at ρ − 1 = 13.
    assert!(co.slot_of(1, h, 13).is_ok() && co.slot_of(1, h, 14).is_err());
    assert_eq!(co.arena().free_units, free);
    // extend behind the verify is Busy (C2 checks Busy first).
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::Busy));
    // t1 accepts one draft and samples x1: T' = T ++ [d1, x1], c = 8; block 1 is published.
    assert_eq!(co.finish_write(t1, comp(t1, 1, None, vec![])).err(), Some(Error::InvalidArgument));
    assert_eq!(co.finish_write(t1, comp(t1, 1, Some(201), vec![])).unwrap(), 8);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.deferred, iv.pending), (9, 8, false, Some(t2)));
    // t2 is the oldest; it starts exactly at 8.
    assert_eq!(iv.planned, 9);
    // extend_deferred makes t2 the producer: L̂ = 10, ρ = 16, no new page.
    let lv = co.extend_deferred(h).unwrap();
    assert_eq!(lv.tables[0].len(), 4);
    assert_eq!(co.inspect(h).unwrap().reach, 16);
    // A continuation's completion must report exactly its accepted drafts.
    assert_eq!(co.finish_write(t2, comp(t2, 2, Some(202), vec![])).err(), Some(Error::InvalidArgument));
    assert_eq!(co.finish_write(t2, comp(t2, 2, Some(202), vec![301])).err(), Some(Error::InvalidArgument));
    assert_eq!(co.finish_write(t2, comp(t2, 2, Some(202), vec![301, 302])).unwrap(), 11);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.pending), (12, 11, None));
    let snap = co.release(h).unwrap();
    assert_eq!(&snap[7..], &[101, 201, 301, 302, 202]);
}

#[test]
fn verify_blocks_are_published_after_the_producer_completes() {
    // Block 1 (positions 4-7) is published by t1's completion and hit by a new lease.
    let mut co = spec_coord();
    let h = lease_l7(&mut co);
    let (t1, _) = co.begin_write(h, 1, Drafts::Known(vec![101, 102]), true).unwrap();
    co.extend_deferred(h).unwrap();
    let (t2, _) = co.begin_write(h, 1, Drafts::Deferred(2), true).unwrap();
    co.finish_write(t1, comp(t1, 1, Some(201), vec![])).unwrap();
    let mut prefix = toks(7, 40);
    prefix.extend_from_slice(&[101, 201]);
    let (h2, cached, _) = co.attach(&prefix).unwrap();
    assert_eq!(cached, 8);
    co.finish_write(t2, comp(t2, 0, None, vec![])).unwrap();
    co.release(h2).unwrap();
    co.release(h).unwrap();
}

#[test]
fn continuation_starts_after_every_acceptance_count() {
    // The device runs t1 with n1 = 0, 1 or 2: t2's window starts at 7 + n1.
    for n1 in 0..=2usize {
        let mut co = spec_coord();
        let h = lease_l7(&mut co);
        let (t1, _) = co.begin_write(h, 1, Drafts::Known(vec![101, 102]), true).unwrap();
        co.extend_deferred(h).unwrap();
        let (t2, p2) = co.begin_write(h, 1, Drafts::Deferred(2), true).unwrap();
        co.finish_write(t1, comp(t1, n1, Some(201), vec![])).unwrap();
        let iv = co.inspect(h).unwrap();
        assert_eq!(iv.computed, 7 + n1);
        assert_eq!(iv.planned, 8 + n1);
        // The window [7 + n1, 7 + n1 + 3) lies inside the listed target slots.
        for i in 0..3 {
            assert_eq!(p2.write_slots[0][n1 + i], co.slot_of(0, h, 7 + n1 + i).unwrap());
        }
        co.finish_write(t2, comp(t2, 2, None, vec![301, 302])).unwrap();
        let iv = co.inspect(h).unwrap();
        assert_eq!((iv.len, iv.computed), (8 + n1 + 2, 8 + n1 + 2));
        co.release(h).unwrap();
    }
}

#[test]
fn deferred_drafts_need_a_continuation_and_a_proposal() {
    let mut co = spec_coord();
    let h = lease_l7(&mut co);
    // Deferred outside a continuation.
    assert_eq!(co.begin_write(h, 1, Drafts::Deferred(1), false).err(), Some(Error::InvalidArgument));
    let (t1, _) = co.begin_write(h, 1, Drafts::Known(vec![101, 102]), false).unwrap();
    // No remaining input before extend_deferred (p_h = L̂_h).
    assert_eq!(co.begin_write(h, 1, Drafts::Deferred(2), false).err(), Some(Error::InvalidArgument));
    co.extend_deferred(h).unwrap();
    // The producer has no propose: there are no device drafts.
    assert_eq!(co.begin_write(h, 1, Drafts::Deferred(2), false).err(), Some(Error::InvalidArgument));
    // More than λ deferred drafts.
    assert_eq!(co.begin_write(h, 1, Drafts::Deferred(3), false).err(), Some(Error::InvalidArgument));
    // Known([]) is a plain continuation, with the producer's drafts as slack.
    let (t2, p2) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    assert_eq!((p2.lo, p2.slack, p2.num_drafts), (7, 2, 0));
    assert_eq!(p2.write_slots[0].len(), 3);
    co.finish_write(t1, comp(t1, 2, Some(201), vec![])).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed), (10, 10));
    co.release(h).unwrap();
}

#[test]
fn continuation_without_extend_deferred_finishes_with_a_known_token() {
    // If extend_deferred fails, the caller waits for t1, appends its token with extend, and
    // plans the next verify with host-known drafts (C2b).
    let mut co = spec_coord();
    let h = lease_l7(&mut co);
    let (t1, _) = co.begin_write(h, 1, Drafts::Known(vec![101, 102]), true).unwrap();
    // t1 does not head X_h, so its token is ignored.
    co.finish_write(t1, comp(t1, 2, Some(201), vec![])).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.reach), (9, 9, 13));
    co.extend(h, &[201]).unwrap();
    let (t2, _) = co.begin_write(h, 1, Drafts::Known(vec![103, 104]), true).unwrap();
    co.finish_write(t2, done_n(t2, 1)).unwrap();
    co.release(h).unwrap();
}

// ---- v0.6 stop and orphans (D25, I18) ----

fn stop_comp(t: pageproof_core::types::Ticket, n: usize, x: Option<u32>, drafts: Vec<u32>) -> CoordCompletion {
    CoordCompletion { ticket: t, accepted: n, token: x, drafts, stop: true }
}

/// The §7 setup: verify t1 with `propose`, extend_deferred, continuation t2 with `Deferred(2)`.
fn verify_and_continuation(co: &mut Coordinator) -> (Handle, pageproof_core::types::Ticket, pageproof_core::types::Ticket) {
    let h = lease_l7(co);
    let (t1, _) = co.begin_write(h, 1, Drafts::Known(vec![101, 102]), true).unwrap();
    co.extend_deferred(h).unwrap();
    let (t2, _) = co.begin_write(h, 1, Drafts::Deferred(2), true).unwrap();
    (h, t1, t2)
}

#[test]
fn stop_at_a_draft_orphans_the_continuation() {
    // EOS at d1 while the device accepted both drafts: finish_write(t1, n=1, stop).
    let mut co = spec_coord();
    let (h, t1, t2) = verify_and_continuation(&mut co);
    assert_eq!(co.finish_write(t1, stop_comp(t1, 1, None, vec![])).unwrap(), 8);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.deferred, iv.stopped), (8, 8, false, true));
    assert_eq!(iv.pending, Some(t2));
    // A stopped lease accepts no new work, before and after its queue empties.
    assert_eq!(co.begin_write(h, 1, Drafts::Known(vec![]), false).err(), Some(Error::InvalidPhase));
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::InvalidPhase));
    assert_eq!(co.extend_deferred(h).err(), Some(Error::InvalidPhase));
    assert_eq!(co.release(h).err(), Some(Error::Busy));
    // The orphan accepts any completion and changes nothing but the queue.
    let free = co.arena().free_units.clone();
    assert_eq!(co.finish_write(t2, comp(t2, 7, Some(9), vec![1, 2, 3])).unwrap(), 8);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.pending), (8, 8, None));
    assert_eq!(co.arena().free_units, free);
    assert_eq!(co.begin_write(h, 1, Drafts::Known(vec![]), false).err(), Some(Error::InvalidPhase));
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::InvalidPhase));
    // Release returns T_h, which ends at the committed prefix.
    let snap = co.release(h).unwrap();
    assert_eq!(&snap[7..], &[101]);
}

#[test]
fn stop_at_the_bonus_token_appends_it() {
    // EOS as t1's bonus: finish_write(t1, n=1, x=EOS, stop) appends d1, EOS; t2 is an orphan.
    let mut co = spec_coord();
    let (h, t1, t2) = verify_and_continuation(&mut co);
    assert_eq!(co.finish_write(t1, stop_comp(t1, 1, Some(999), vec![])).unwrap(), 8);
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.stopped), (9, 8, true));
    co.finish_write(t2, done(t2)).unwrap();
    let snap = co.release(h).unwrap();
    assert_eq!(&snap[7..], &[101, 999]);
}

#[test]
fn stop_with_an_empty_queue_behind() {
    // §7: stop with no ticket behind it (any δ): stopped with no orphans; release succeeds at once.
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 2, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(5, 41)).unwrap();
    let (t, _) = co.begin_write(h, 5, Drafts::Known(vec![]), false).unwrap();
    assert_eq!(co.finish_write(t, stop_comp(t, 0, Some(7), vec![])).unwrap(), 5);
    let iv = co.inspect(h).unwrap();
    // Without X_h the token is the caller's; the lease is stopped.
    assert_eq!((iv.len, iv.computed, iv.pending, iv.stopped), (5, 5, None, true));
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::InvalidPhase));
    co.release(h).unwrap();
}

#[test]
fn stop_still_checks_its_completion() {
    // A completion with stop that is not an orphan's still needs n <= k (C4).
    let mut co = spec_coord();
    let (h, t1, t2) = verify_and_continuation(&mut co);
    assert_eq!(co.finish_write(t1, stop_comp(t1, 3, None, vec![])).err(), Some(Error::InvalidArgument));
    // Out of order stays InvalidTicket, orphan or not.
    assert_eq!(co.finish_write(t2, stop_comp(t2, 0, None, vec![])).err(), Some(Error::InvalidTicket));
    co.finish_write(t1, stop_comp(t1, 2, None, vec![])).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn stopped_lease_keeps_what_it_committed() {
    // What was committed up to c'_h is kept and published: block 1 (4-7) is a cache hit.
    let mut co = spec_coord();
    let (h, t1, t2) = verify_and_continuation(&mut co);
    co.finish_write(t1, stop_comp(t1, 1, None, vec![])).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    let mut snap = co.release(h).unwrap();
    assert_eq!(snap.len(), 8);
    // A longer request over the same prefix hits both committed blocks.
    snap.push(1);
    let (h2, cached, _) = co.attach(&snap).unwrap();
    assert_eq!(cached, 8);
    co.release(h2).unwrap();
}

#[test]
fn stop_on_a_hybrid_lease() {
    // A hybrid lease (one state class): after stop, release still frees its slot.
    let mut co = Coordinator::create(8, 64, &[16], &[16], &[8], 4, 2, 1, NS).unwrap();
    let (h, _, _) = co.attach(&toks(4, 42)).unwrap();
    let (t1, _) = co.begin_write(h, 4, Drafts::Known(vec![]), true).unwrap();
    co.extend_deferred(h).unwrap();
    let (t2, p2) = co.begin_write(h, 1, Drafts::Deferred(1), false).unwrap();
    assert!(!p2.init);
    co.finish_write(t1, stop_comp(t1, 0, Some(5), vec![])).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    let free = co.arena().free_units.clone();
    co.release(h).unwrap();
    assert!(co.arena().free_units[2] > free[2]);
}

// ---- remaining §7 rows for v0.5 and v0.6 ----

#[test]
fn extend_deferred_without_a_unit_is_no_capacity() {
    // §7: the deferred position starts a new block and no unit can be had: NoCapacity, state
    // unchanged; the caller waits for t and then uses extend.
    let mut co = Coordinator::create(1, 64, &[16], &[], &[], 4, 0, 1, NS).unwrap();
    let (h, _, _) = co.attach(&toks(12, 50)).unwrap();
    let (h2, _, _) = co.attach(&toks(4, 51)).unwrap();
    let (t, _) = co.begin_write(h, 12, Drafts::Known(vec![]), false).unwrap();
    let before = co.inspect(h).unwrap();
    assert_eq!(co.extend_deferred(h).err(), Some(Error::NoCapacity));
    let after = co.inspect(h).unwrap();
    assert_eq!((after.len, after.reach, after.deferred), (before.len, before.reach, false));
    co.finish_write(t, done(t)).unwrap();
    co.release(h2).unwrap();
    co.extend(h, &[1]).unwrap();
    co.release(h).unwrap();
}

#[test]
fn eos_at_step_n_while_step_n_plus_1_is_pending() {
    // §7: finish_write(n) appends the EOS; finish_write(n+1) ignores its token and sets c = L.
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 0, 1, NS).unwrap();
    let (h, _, _) = co.attach(&toks(3, 52)).unwrap();
    let (t1, _) = co.begin_write(h, 3, Drafts::Known(vec![]), false).unwrap();
    co.extend_deferred(h).unwrap();
    let (t2, _) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    let eos = 2;
    co.finish_write(t1, tok(t1, eos)).unwrap();
    // The EOS completes block 0 (positions 0-3) when step n+1 completes.
    co.finish_write(t2, tok(t2, 77)).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.pending), (4, 4, None));
    let snap = co.release(h).unwrap();
    assert_eq!(snap[3], eos);
    // Block 0 is published under the real EOS token.
    let mut longer = snap.clone();
    longer.push(5);
    let (h2, cached, _) = co.attach(&longer).unwrap();
    assert_eq!(cached, 4);
    co.release(h2).unwrap();
}

#[test]
fn golden_token_behind_a_pending_step() {
    // §7: extend(h, [g]) succeeds with X_h empty, p_h = L_h and room in the queue.
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 0, 1, NS).unwrap();
    let (h, _, _) = co.attach(&toks(5, 53)).unwrap();
    let (t1, _) = co.begin_write(h, 5, Drafts::Known(vec![]), false).unwrap();
    co.extend(h, &[42]).unwrap();
    let (t2, p2) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    assert_eq!((p2.input_ids.clone(), p2.producer), (vec![42], None));
    co.finish_write(t1, done(t1)).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    assert_eq!(co.inspect(h).unwrap().computed, 6);
    co.release(h).unwrap();
}

#[test]
fn deferred_last_position_of_a_block() {
    // §7: a block whose last position is deferred is published only after the producer's
    // completion appended the token and the frontier passed it.
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 0, 1, NS).unwrap();
    let base = toks(3, 54);
    let (h, _, _) = co.attach(&base).unwrap();
    let (t1, _) = co.begin_write(h, 3, Drafts::Known(vec![]), false).unwrap();
    co.extend_deferred(h).unwrap();
    let (t2, _) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    co.finish_write(t1, tok(t1, 9)).unwrap();
    let mut probe = base.clone();
    probe.extend_from_slice(&[9, 1]);
    // Block 0 is not yet published: c = 3.
    let (hp, cached, _) = co.attach(&probe).unwrap();
    assert_eq!(cached, 0);
    co.release(hp).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    let (hp, cached, _) = co.attach(&probe).unwrap();
    assert_eq!(cached, 4);
    co.release(hp).unwrap();
    co.release(h).unwrap();
}

#[test]
fn attach_while_another_lease_has_two_tickets_pending() {
    // §7: the pending tickets' units are referenced by their lease, so their slabs are not
    // reclaimable; the other attach takes free slabs or fails with NoCapacity.
    let mut co = Coordinator::create(2, 64, &[16], &[], &[], 4, 0, 1, NS).unwrap();
    let (h, _, v) = co.attach(&toks(8, 55)).unwrap();
    let (t1, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    let (t2, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    let owner = co.arena().owner.clone();
    let (h2, _, _) = co.attach(&toks(4, 56)).unwrap();
    // 8 pages in all, 3 held: a 6-page request cannot reclaim the pending lease's slab.
    assert_eq!(co.attach(&toks(24, 57)).err(), Some(Error::NoCapacity));
    let v2 = co.inspect(h).unwrap();
    assert_eq!(v2.lease.tables, v.tables);
    assert_eq!(co.arena().owner[v.tables[0][0] / 4], owner[v.tables[0][0] / 4]);
    co.finish_write(t1, done(t1)).unwrap();
    co.finish_write(t2, done(t2)).unwrap();
    co.release(h2).unwrap();
    co.release(h).unwrap();
}

#[test]
fn extend_deferred_after_an_accepted_verify_needs_two_pages() {
    // §7: with 1 + λ > B, extend_deferred's demand can reach ceil((1 + δλ)/B) pages. That needs
    // L̂ to grow by δ·λ between two reach updates, which happens when a verify accepts all its
    // drafts. B = 4, λ = 4, δ = 1, μ = 8 (sequence from the review of PR 7).
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 4, 1, NS).unwrap();
    let (h, _, _) = co.attach(&[1, 2]).unwrap();
    compute_all(&mut co, h);
    co.extend(h, &[3]).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.reach, iv.lease.tables[0].len()), (11, 3));
    let (t1, _) = co.begin_write(h, 1, Drafts::Known(vec![4, 5, 6, 7]), false).unwrap();
    co.extend_deferred(h).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.reach, iv.lease.tables[0].len()), (12, 3));
    let (t2, _) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    // t1 accepts all four drafts: L̂ grows from 4 to 8 while the reach stays 12.
    co.finish_write(t1, comp(t1, 4, Some(8), vec![])).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.reach, iv.lease.tables[0].len()), (8, 12, 3));
    let before = iv.lease.tables[0].clone();
    // L̂' = 9 and ρ' = 17 need 5 pages: two new ones, the bound ceil((1 + δλ)/B) = 2.
    let lv = co.extend_deferred(h).unwrap();
    assert_eq!(lv.tables[0].len() - before.len(), 2);
    assert_eq!(&lv.tables[0][..before.len()], &before[..]);
    assert_eq!(co.inspect(h).unwrap().reach, 17);
    let (t3, _) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    // t2 computes the bonus 8 at position 7 and binds 9; t3 computes position 8.
    co.finish_write(t2, tok(t2, 9)).unwrap();
    co.finish_write(t3, done(t3)).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed), (9, 9));
    co.release(h).unwrap();
}

#[test]
fn create_rejects_a_configuration_without_room_for_one_lease() {
    // C0: one slab, one paged class and one state class pass `cfg_accepts`, but a one-token lease
    // needs a page and a slot, two slabs: `¬Fits(1)`. This is ConfigError, decided before any
    // identifier is taken (review of PR 7).
    assert_eq!(Coordinator::create(1, 64, &[64], &[], &[64], 4, 0, 0, NS).err(), Some(Error::ConfigError));
    // With a second slab the same classes fit.
    assert!(Coordinator::create(2, 64, &[64], &[], &[64], 4, 0, 0, NS).is_ok());
}

// ---- gaps from the coverage review of PR 7 ----

#[test]
fn drafter_slab_is_reclaimed_for_a_target_class() {
    // §7: drafter and target classes compete for slabs under one `Cap`. Every class has one unit
    // per slab, λ = 1, so μ = 2. A paged slab can change hands only after a state class has taken
    // slabs from the target class, which leaves the drafter class with more slabs than the target.
    let mut co = Coordinator::create(11, 64, &[64], &[64], &[64], 4, 1, 0, NS).unwrap();
    let ha = co.attach(&toks(18, 60)).unwrap().0;
    assert_eq!((count_owner(&co, 0), count_owner(&co, 1), count_owner(&co, 2)), (5, 5, 1));
    co.release(ha).unwrap();
    // Three short leases need three state slots: the state class takes two idle target slabs.
    let hs: Vec<Handle> = (0..3).map(|i| co.attach(&toks(2, 61 + i)).unwrap().0).collect();
    assert_eq!((count_owner(&co, 0), count_owner(&co, 1), count_owner(&co, 2)), (3, 5, 3));
    for h in hs {
        co.release(h).unwrap();
    }
    assert_eq!(free_slabs(&co), 0);
    // A 4-block lease: the target class is one slab short; the drafter class gives up an idle slab.
    let before = owners(&co);
    let (hd, _, vd) = co.attach(&toks(14, 64)).unwrap();
    assert_eq!((count_owner(&co, 0), count_owner(&co, 1), count_owner(&co, 2)), (4, 4, 3));
    let moved: Vec<usize> = (0..11).filter(|&s| before[s] != owners(&co)[s]).collect();
    assert_eq!(moved.len(), 1);
    assert_eq!((before[moved[0]], owners(&co)[moved[0]]), (2, 1), "a drafter slab became a target slab");
    check_disjoint(&co, &[64, 64, 64], &[1, 1, 1], &[&vd], 2);
    co.release(hd).unwrap();
}

#[test]
fn prefix_cached_in_the_target_class_only() {
    // §7: target prefix cached, drafter class not: k* stops at the first block missing in any
    // paged class. Target pages are 16 B (4 per slab), drafter pages 32 B (2 per slab).
    let mut co = Coordinator::create(6, 64, &[16], &[32], &[], 4, 1, 0, NS).unwrap();
    let t = toks(9, 70);
    let (ha, _, va) = co.attach(&t).unwrap();
    compute_all(&mut co, ha);
    co.release(ha).unwrap();
    let (tgt0, drf0) = (va.tables[0][0], va.tables[1][0]);
    let (_hx1, _, v1) = co.attach(&toks(4, 71)).unwrap();
    let (hx2, _, v2) = co.attach(&toks(8, 72)).unwrap();
    // Precondition (free-page order): the drafter page of block 0 is reused, the target's is not.
    assert!(!v1.tables[0].contains(&tgt0) && !v2.tables[0].contains(&tgt0), "target block 0 kept");
    assert!(v1.tables[1].contains(&drf0) || v2.tables[1].contains(&drf0), "drafter block 0 reused");
    co.release(hx2).unwrap();
    let (hc, cached, _) = co.attach(&t).unwrap();
    assert_eq!(cached, 0);
    co.release(hc).unwrap();
}

#[test]
fn mu_is_twelve_with_a_drafter_and_zos() {
    // §7: B = 64, λ = 4, a drafter class, δ = 1: μ = 12; tables cover ceil((L + 12)/64) blocks.
    // 4 pages of 64 tokens per slab and class; 8 slabs give Fits(m) for m <= 16 blocks.
    let mut co = Coordinator::create(8, 1024, &[256], &[256], &[], 64, 4, 1, NS).unwrap();
    let (h, _, v) = co.attach(&toks(52, 73)).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.mu, iv.reach, v.tables[0].len(), v.tables[1].len()), (12, 64, 1, 1));
    co.release(h).unwrap();
    let (h, _, v) = co.attach(&toks(53, 74)).unwrap();
    assert_eq!((v.tables[0].len(), v.tables[1].len()), (2, 2));
    co.release(h).unwrap();
    // Fits(16) holds and Fits(17) does not, so L + 12 <= 1024 fits and L = 1013 does not,
    // although its ceil(1013/64) = 16 blocks alone would.
    assert!(co.attach(&toks(1012, 75)).is_ok_and(|(h, _, _)| co.release(h).is_ok()));
    assert_eq!(co.attach(&toks(1013, 76)).err(), Some(Error::RequestTooLarge));
}

#[test]
fn drafts_at_lambda_zero_are_rejected() {
    // §7: with λ = 0, begin_write with non-empty drafts or with propose is InvalidArgument.
    let mut co = Coordinator::create(4, 64, &[16], &[], &[], 4, 0, 0, NS).unwrap();
    let (h, _, _) = co.attach(&toks(5, 77)).unwrap();
    let (t, _) = co.begin_write(h, 4, Drafts::Known(vec![]), false).unwrap();
    co.finish_write(t, done(t)).unwrap();
    assert_eq!(co.begin_write(h, 1, Drafts::Known(vec![1]), false).err(), Some(Error::InvalidArgument));
    assert_eq!(co.begin_write(h, 1, Drafts::Known(vec![]), true).err(), Some(Error::InvalidArgument));
    let (t, _) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    co.finish_write(t, done(t)).unwrap();
    co.release(h).unwrap();
}

#[test]
fn rejected_drafts_equal_to_a_cached_block_are_not_published() {
    // §7: rejected drafts that would complete a block equal to a cached block: no hit, no
    // publication. A publishes blocks 0 and 1; B feeds block 1's tokens as drafts and rejects them.
    let mut co = Coordinator::create(8, 64, &[16], &[], &[], 4, 3, 0, NS).unwrap();
    let t = toks(9, 78);
    let (ha, _, va) = co.attach(&t).unwrap();
    compute_all(&mut co, ha);
    let (hb, cached, vb) = co.attach(&t[..5]).unwrap();
    assert_eq!(cached, 4);
    assert_ne!(vb.tables[0][1], va.tables[0][1]);
    let (tb, _) = co.begin_write(hb, 1, Drafts::Known(t[5..8].to_vec()), false).unwrap();
    co.finish_write(tb, done_n(tb, 0)).unwrap();
    assert_eq!(co.inspect(hb).unwrap().len, 5);
    co.release(ha).unwrap();
    // If B's page held a key for block 1, it would be the active candidate and be preferred.
    let (hc, cached, vc) = co.attach(&t).unwrap();
    assert_eq!(cached, 8);
    assert_eq!(vc.tables[0][1], va.tables[0][1], "block 1 comes from A's page, not B's");
    co.release(hb).unwrap();
    co.release(hc).unwrap();
}

#[test]
fn bonus_token_extend_without_capacity() {
    // §7: extend with the bonus token after n = λ accepted drafts: the demand is
    // ceil((L' + μ)/B) - m_h; on NoCapacity the lease keeps its accepted drafts and c_h = L_h.
    // B = 4, λ = 2, μ = 2, one page per slab, two slabs.
    let mut co = Coordinator::create(2, 64, &[64], &[], &[], 4, 2, 0, NS).unwrap();
    let base = toks(2, 79);
    let (h, _, _) = co.attach(&base).unwrap();
    let h2 = co.attach(&toks(1, 80)).unwrap().0;
    assert_eq!(free_slabs(&co), 0);
    let (t, _) = co.begin_write(h, 1, Drafts::Known(vec![]), false).unwrap();
    co.finish_write(t, done(t)).unwrap();
    // Verify the last token with λ = 2 drafts, both accepted: L = ρ = 4, one page.
    let (t, _) = co.begin_write(h, 1, Drafts::Known(vec![91, 92]), false).unwrap();
    co.finish_write(t, done_n(t, 2)).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.reach, iv.lease.tables[0].len()), (4, 4, 4, 1));
    // The bonus token needs ρ' = 7, a second page, and no slab is free.
    let before = iv.lease.tables.clone();
    assert_eq!(co.extend(h, &[93]).err(), Some(Error::NoCapacity));
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.reach), (4, 4, 4));
    assert_eq!(iv.lease.tables, before);
    co.release(h2).unwrap();
    co.extend(h, &[93]).unwrap();
    assert_eq!(&co.release(h).unwrap()[2..], &[91, 92, 93]);
}

#[test]
fn walkthrough_block_two_and_the_ignored_bonus() {
    // §7 walk-through: after finish_write(t2, n = 2, x2) with extend_deferred, c_h = 11 and block
    // 2 (positions 8-11) is not published until a later ticket writes position 11.
    let mut co = spec_coord();
    let (h, t1, t2) = verify_and_continuation(&mut co);
    co.finish_write(t1, comp(t1, 1, Some(201), vec![])).unwrap();
    co.extend_deferred(h).unwrap();
    co.finish_write(t2, comp(t2, 2, Some(202), vec![301, 302])).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed), (12, 11));
    let mut probe = toks(7, 40);
    probe.extend_from_slice(&[101, 201, 301, 302, 202, 1]);
    let (hp, cached, _) = co.attach(&probe).unwrap();
    assert_eq!(cached, 8, "block 2 is not published");
    co.release(hp).unwrap();
    co.release(h).unwrap();

    // Without extend_deferred, t2 is not in X_h: x2 is ignored and the caller appends it.
    let mut co = spec_coord();
    let (h, t1, t2) = verify_and_continuation(&mut co);
    co.finish_write(t1, comp(t1, 1, Some(201), vec![])).unwrap();
    co.finish_write(t2, comp(t2, 2, Some(202), vec![301, 302])).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.deferred), (11, 11, false));
    co.extend(h, &[202]).unwrap();
    assert_eq!(&co.release(h).unwrap()[7..], &[101, 201, 301, 302, 202]);
}

#[test]
fn hybrid_continuation_behind_a_real_verify() {
    // §7: hybrid lease, t2 a continuation of verify t1 (k = 2): both plans name the one slot σ;
    // no second state slot is ever taken.
    let mut co = Coordinator::create(8, 64, &[16], &[16], &[64], 4, 2, 1, NS).unwrap();
    let (h, _, lv) = co.attach(&toks(7, 81)).unwrap();
    let (t0, _) = co.begin_write(h, 6, Drafts::Known(vec![]), false).unwrap();
    co.finish_write(t0, done(t0)).unwrap();
    let free = co.arena().free_units[2];
    let (t1, p1) = co.begin_write(h, 1, Drafts::Known(vec![11, 12]), true).unwrap();
    co.extend_deferred(h).unwrap();
    let (t2, p2) = co.begin_write(h, 1, Drafts::Deferred(2), true).unwrap();
    assert_eq!(p1.state_slots, lv.slots);
    assert_eq!(p2.state_slots, lv.slots);
    assert!(!p1.init && !p2.init);
    assert_eq!((p1.num_drafts, p2.num_drafts, p2.producer), (2, 2, Some(t1)));
    co.finish_write(t1, comp(t1, 1, Some(21), vec![])).unwrap();
    co.finish_write(t2, comp(t2, 2, None, vec![31, 32])).unwrap();
    let iv = co.inspect(h).unwrap();
    assert_eq!((iv.len, iv.computed, iv.lease.slots.clone()), (11, 11, lv.slots.clone()));
    assert_eq!(co.arena().free_units[2], free);
    co.release(h).unwrap();
}

#[test]
fn extend_behind_a_propose_only_ticket_is_busy() {
    // §7: a pending ticket with propose and no drafts makes extend Busy (C2 checks Busy first),
    // while extend_deferred is allowed (C2b) and a Deferred continuation may follow.
    let mut co = spec_coord();
    let h = lease_l7(&mut co);
    let (t1, _) = co.begin_write(h, 1, Drafts::Known(vec![]), true).unwrap();
    assert_eq!(co.extend(h, &[1]).err(), Some(Error::Busy));
    co.extend_deferred(h).unwrap();
    let (t2, p2) = co.begin_write(h, 1, Drafts::Deferred(2), true).unwrap();
    assert_eq!((p2.slack, p2.num_drafts), (0, 2));
    co.finish_write(t1, tok(t1, 21)).unwrap();
    co.finish_write(t2, comp(t2, 1, None, vec![31])).unwrap();
    assert_eq!(&co.release(h).unwrap()[7..], &[21, 31]);
}

#[test]
fn drafter_class_windows_lie_inside_the_listed_slots() {
    // §7: for n1 = 0, 1, 2, the continuation's drafter window (ℓ + k inputs plus λ proposal rows)
    // starts at index n1 of its listed drafter slots and ends at most at ρ_h = 14.
    for n1 in 0..=2usize {
        let mut co = spec_coord();
        let h = lease_l7(&mut co);
        let (t1, _) = co.begin_write(h, 1, Drafts::Known(vec![101, 102]), true).unwrap();
        co.extend_deferred(h).unwrap();
        let (t2, p2) = co.begin_write(h, 1, Drafts::Deferred(2), true).unwrap();
        let width = p2.num_inputs + p2.num_drafts + 2;
        assert_eq!(p2.write_slots[1].len(), 7);
        assert!(n1 + width <= p2.write_slots[1].len() && 7 + n1 + width <= 14);
        co.finish_write(t1, comp(t1, n1, Some(201), vec![])).unwrap();
        // The tables do not change, so the listed slots still name the window's positions.
        for i in 0..width {
            assert_eq!(p2.write_slots[1][n1 + i], co.slot_of(1, h, 7 + n1 + i).unwrap(), "n1 = {n1}, i = {i}");
        }
        co.finish_write(t2, comp(t2, 0, None, vec![])).unwrap();
        co.release(h).unwrap();
    }
}


#[test]
fn several_candidates_prefer_the_active_one() {
    // §7: several candidates for one key: prefer an active candidate, so a servable request is
    // not wrongly rejected. A and B attach the same prompt before either publishes, so block 0 is
    // published twice, on different pages. One page per slab, four slabs.
    let mut co = Coordinator::create(4, 64, &[64], &[], &[], 4, 0, 0, NS).unwrap();
    let t = toks(9, 82);
    let (ha, _, va) = co.attach(&t[..5]).unwrap();
    let (hb, cb, vb) = co.attach(&t[..5]).unwrap();
    assert_eq!(cb, 0);
    compute_all(&mut co, ha);
    compute_all(&mut co, hb);
    assert_ne!(va.tables[0][0], vb.tables[0][0]);
    co.release(ha).unwrap();
    // C needs 3 pages. Hitting B's active page takes 2 free units; reactivating A's cached page
    // would take 3, and only 2 are free.
    assert_eq!(co.arena().free_units, vec![2]);
    let (hc, cc, vc) = co.attach(&t).unwrap();
    assert_eq!(cc, 4);
    assert_eq!(vc.tables[0][0], vb.tables[0][0]);
    co.release(hb).unwrap();
    co.release(hc).unwrap();
}

#[test]
fn fragmented_paged_units_do_not_make_a_state_slot() {
    // §7 (D12): state class full, FS = ∅, and the paged class's free units are spread over partly
    // used slabs: NoCapacity, even though the free paged bytes exceed a state unit. Paged unit
    // 4 B (16 per slab), state unit 32 B (2 per slab), four slabs.
    let mut co = Coordinator::create(4, 64, &[4], &[], &[32], 4, 0, 0, NS).unwrap();
    let ha = co.attach(&toks(32, 83)).unwrap().0;
    let hb = co.attach(&toks(32, 84)).unwrap().0;
    let hc = co.attach(&toks(32, 85)).unwrap().0;
    let hd = co.attach(&toks(32, 86)).unwrap().0;
    assert_eq!((count_owner(&co, 0), count_owner(&co, 1), free_slabs(&co)), (2, 2, 0));
    co.release(ha).unwrap();
    co.release(hc).unwrap();
    let he = co.attach(&toks(4, 87)).unwrap().0;
    let hf = co.attach(&toks(4, 88)).unwrap().0;
    let a = co.arena();
    // 14 free paged units (56 B > 32 B), none of them an idle slab; no free state slot.
    assert_eq!((a.free_units.clone(), a.reclaimable.clone()), (vec![14, 0], vec![0, 0]));
    let before = co.arena();
    assert_eq!(co.attach(&toks(4, 89)).err(), Some(Error::NoCapacity));
    assert_eq!(co.arena().owner, before.owner);
    for h in [hb, hd, he, hf] {
        co.release(h).unwrap();
    }
}

#[test]
fn a_free_slab_is_used_before_a_reclaimable_one() {
    // §7: FS non-empty and a reclaimable slab exists: the free slab is used, nothing is
    // reclaimed. One unit per slab.
    let mut co = Coordinator::create(5, 64, &[64], &[], &[64], 4, 0, 0, NS).unwrap();
    let hx = co.attach(&toks(12, 90)).unwrap().0;
    compute_all(&mut co, hx);
    co.release(hx).unwrap();
    assert_eq!((count_owner(&co, 0), count_owner(&co, 1), free_slabs(&co)), (3, 1, 1));
    let hy = co.attach(&toks(4, 91)).unwrap().0;
    // The paged class has idle keyed slabs to give, but the state class takes the free slab.
    assert!(co.arena().reclaimable[0] >= 1);
    let hz = co.attach(&toks(4, 92)).unwrap().0;
    assert_eq!((count_owner(&co, 0), count_owner(&co, 1), free_slabs(&co)), (3, 2, 0));
    // With FS empty, the paged class's one remaining idle slab cannot go: the next lease needs its
    // page too, so NoCapacity, atomically.
    let before = co.arena();
    assert_eq!(co.attach(&toks(4, 93)).err(), Some(Error::NoCapacity));
    assert_eq!(co.arena().owner, before.owner);
    for h in [hy, hz] {
        co.release(h).unwrap();
    }
}
