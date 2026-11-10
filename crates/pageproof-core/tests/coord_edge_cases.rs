//! Runtime checks of the contract v0.3 §7 edge cases against the verified coordinator: slab arena,
//! several paged classes, state classes, reclaim, Prot, and the all-or-nothing operations.
use pageproof_core::coord::Coordinator;
use pageproof_core::coord_attach::LeaseView;
use pageproof_core::ops_write::Completion;
use pageproof_core::types::{Error, Handle};

const NS: &[u8] = b"dummy-v0.3";

fn toks(n: usize, seed: u32) -> Vec<u32> {
    (0..n as u32).map(|i| i.wrapping_mul(2654435761).wrapping_add(seed)).collect()
}

/// Computes the rest of a lease's input in one ticket.
fn compute_all(co: &mut Coordinator, h: Handle) {
    let v = co.inspect(h).unwrap();
    if v.computed < v.len {
        let (t, plan) = co.begin_write(h, v.len - v.computed).unwrap();
        assert_eq!(plan.ticket, t);
        co.finish_write(t, Completion { ticket: t }).unwrap();
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
    assert_eq!(Coordinator::create(4, 1000, &[96], &[], 4, NS).err(), Some(Error::ConfigError));
    assert_eq!(Coordinator::create(0, 960, &[96], &[], 4, NS).err(), Some(Error::ConfigError));
    assert_eq!(Coordinator::create(4, 960, &[], &[96], 4, NS).err(), Some(Error::ConfigError));
    assert_eq!(Coordinator::create(4, 960, &[0], &[], 4, NS).err(), Some(Error::ConfigError));
    assert!(Coordinator::create(4, 960, &[96], &[320], 4, NS).is_ok());
}

#[test]
fn lcm_slab_layout() {
    // S = lcm(96 KiB, 640 KiB) = 1.875 MiB: 20 pages and 3 state slots per slab.
    let (u_p, u_s) = (96 * 1024, 640 * 1024);
    let s = 1966080;
    let mut co = Coordinator::create(2, s, &[u_p], &[u_s], 4, NS).unwrap();
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
    let mut co = Coordinator::create(2, 64, &[16], &[], 4, NS).unwrap();
    assert_eq!(co.attach(&[]).err(), Some(Error::InvalidArgument));
    // 2 slabs x 4 pages x B=4 = 32 tokens fit; 33 do not.
    assert_eq!(co.attach(&toks(33, 0)).err(), Some(Error::RequestTooLarge));
    assert!(co.attach(&toks(32, 0)).is_ok());
}

#[test]
fn fits_counts_state_slabs() {
    // With a state class, one slab is reserved for its slot: 1 paged slab left => 16 tokens.
    let mut co = Coordinator::create(2, 64, &[16], &[64], 4, NS).unwrap();
    assert_eq!(co.attach(&toks(17, 0)).err(), Some(Error::RequestTooLarge));
    assert!(co.attach(&toks(16, 0)).is_ok());
}

#[test]
fn prefix_hit_without_state_class() {
    let mut co = Coordinator::create(4, 64, &[16], &[], 4, NS).unwrap();
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
    let mut co = Coordinator::create(4, 64, &[16], &[32], 4, NS).unwrap();
    let t = toks(12, 3);
    let (h1, _, v1) = co.attach(&t).unwrap();
    compute_all(&mut co, h1);
    let (h2, c2, v2) = co.attach(&t).unwrap();
    assert_eq!(c2, 0, "D13: no state checkpoints, no hits");
    assert_ne!(v1.slots[0], v2.slots[0], "distinct live slots");
    let (t2, plan) = co.begin_write(h2, 12).unwrap();
    assert!(plan.init, "first plan starts from the initial state (E10)");
    assert_eq!(plan.state_slots, v2.slots);
    co.finish_write(t2, Completion { ticket: t2 }).unwrap();
    check_disjoint(&co, &[16, 32], &[4, 2], &[&v1, &v2], 1);
}

#[test]
fn two_paged_classes_kstar_is_joint() {
    // Class 0 and class 1 share B and keys; a hit needs both classes.
    let mut co = Coordinator::create(6, 64, &[16, 32], &[], 4, NS).unwrap();
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
    let mut co = Coordinator::create(1, 48, &[16], &[], 4, NS).unwrap();
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
    let mut co = Coordinator::create(3, 64, &[16], &[64], 4, NS).unwrap();
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
    let mut co = Coordinator::create(4, 64, &[64], &[64], 4, NS).unwrap();
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
    let mut co = Coordinator::create(3, 64, &[64, 16], &[], 4, NS).unwrap();
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
    let mut co = Coordinator::create(3, 64, &[16, 64], &[], 4, NS).unwrap();
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
    let mut co = Coordinator::create(3, 64, &[16, 64], &[], 4, NS).unwrap();
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
    let mut co = Coordinator::create(3, 64, &[16, 32], &[], 4, NS).unwrap();
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
    let mut co = Coordinator::create(4, 64, &[16], &[64], 4, NS).unwrap();
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
    assert_eq!(co.begin_write(h, 0).err(), Some(Error::InvalidArgument));
    let v3 = co.extend(h, &toks(1, 4)).unwrap();
    assert_eq!(v3.tables[0].len(), 3);
    let (t, _) = co.begin_write(h, 1).unwrap();
    assert_eq!(co.extend(h, &toks(1, 5)).err(), Some(Error::Busy));
    assert_eq!(co.release(h).err(), Some(Error::Busy));
    co.finish_write(t, Completion { ticket: t }).unwrap();
    co.release(h).unwrap();
}

#[test]
fn state_plan_after_first_chunk() {
    let mut co = Coordinator::create(4, 64, &[16], &[64], 4, NS).unwrap();
    let (h, _, v) = co.attach(&toks(10, 1)).unwrap();
    let (t1, p1) = co.begin_write(h, 6).unwrap();
    assert!(p1.init);
    assert_eq!(p1.write_slots.len(), 1);
    assert_eq!(p1.write_slots[0].len(), 6);
    co.finish_write(t1, Completion { ticket: t1 }).unwrap();
    let (t2, p2) = co.begin_write(h, 4).unwrap();
    assert!(!p2.init, "later plans read the live slot");
    assert_eq!(p2.state_slots, v.slots);
    assert_eq!(p2.positions, (6..10).collect::<Vec<_>>());
    co.finish_write(t2, Completion { ticket: t2 }).unwrap();
    assert_eq!(co.inspect(h).unwrap().computed, 10);
}

#[test]
fn tickets_and_handles_are_single_use() {
    let mut co = Coordinator::create(4, 64, &[16], &[64], 4, NS).unwrap();
    let (h, _, _) = co.attach(&toks(4, 1)).unwrap();
    let (t, _) = co.begin_write(h, 4).unwrap();
    assert_eq!(co.begin_write(h, 1).err(), Some(Error::Busy));
    co.finish_write(t, Completion { ticket: t }).unwrap();
    assert_eq!(co.finish_write(t, Completion { ticket: t }).err(), Some(Error::InvalidTicket));
    co.release(h).unwrap();
    assert_eq!(co.release(h).err(), Some(Error::InvalidHandle));
    assert!(co.inspect(h).is_err());
    // Handles of another coordinator are rejected.
    let mut other = Coordinator::create(4, 64, &[16], &[64], 4, NS).unwrap();
    let (h2, _, _) = other.attach(&toks(4, 1)).unwrap();
    assert_eq!(co.release(h2).err(), Some(Error::InvalidHandle));
}

#[test]
fn release_keeps_slabs_and_makes_them_reclaimable() {
    let mut co = Coordinator::create(4, 64, &[16], &[64], 4, NS).unwrap();
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
    let mut co = Coordinator::create(12, 64, &units[..2], &units[2..], 4, NS).unwrap();
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
