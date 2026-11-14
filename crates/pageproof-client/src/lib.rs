//! A verified client of the public `pageproof-core` specs.
//!
//! It checks that the public contracts are strong enough to reason about a scheduler step. On a
//! freshly created manager, attaching a 3-token request (one block, B = 4) must succeed with
//! `cached == 0`, by the C1 capacity rule. Only `create` itself may fail (id exhaustion).
// Proof-only imports and bindings disappear from rustc's executable view.
#![allow(unused_imports, unused_variables)]
use vstd::prelude::*;
use pageproof_core::manager::*;
use pageproof_core::types::*;
use pageproof_core::ops_attach::*;
use pageproof_core::arith::*;
use pageproof_core::coord::*;
use pageproof_core::coord_attach::*;
use pageproof_core::coord_ops::*;

verus! {

/// Returns `None` only if `create` fails. Otherwise `attach` provably succeeds with nothing
/// cached; its `Err` branch is proved unreachable.
pub fn fresh_attach() -> (r: Option<usize>)
    ensures
        r matches Some(cached) ==> cached == 0,
{
    match Manager::create(4, 4, b"ns".as_slice()) {
        Ok(mut m) => {
            let toks: Vec<u32> = vec![1, 2, 3];
            let ghost v = m@;
            proof {
                lemma_cdiv_props(3, 4);
                assert(cdiv(3, 4) == 1) by (compute_only);
                assert(is_kstar(v, toks@, 1, 0));
            }
            match m.attach(toks.as_slice()) {
                Ok((h, cached, view)) => {
                    proof {
                        lemma_attach_capacity_iff(v, m@, toks@, Ok((h, cached, view)), 0);
                    }
                    Some(cached)
                },
                Err(e) => {
                    proof {
                        // |F| = P = 4 on a fresh manager, and d = m - u <= 1, so this is unreachable.
                        pageproof_core::types::lemma_free_of(4, v.refs, v.own);
                        assert forall|b: usize| #[trigger] v.free_set().contains(b) <==> (b as nat) < 4 by {}
                        vstd::set_lib::range_set_properties::<usize>(0usize, 4usize);
                        assert(v.free_set() =~= Set::<usize>::range(0usize, 4usize));
                        lemma_attach_capacity_iff(v, m@, toks@, Err(e), 0);
                        assert(false);
                    }
                    None
                },
            }
        },
        Err(_) => None,
    }
}

/// An arbitrary-length scheduler loop: attach, compute, release, repeated `n` times. Metadata
/// stays O(P) at every iteration, whatever the inputs and however the calls fail.
pub fn churn(m: &mut Manager, reqs: &Vec<Vec<u32>>)
    requires
        old(m).valid(),
    ensures
        final(m).valid(),
        final(m).index_buckets() <= final(m)@.p,
        final(m).num_leases() <= final(m)@.p,
{
    let mut i: usize = 0;
    while i < reqs.len()
        invariant
            m.valid(),
        decreases reqs.len() - i,
    {
        if let Ok((h, _, _)) = m.attach(reqs[i].as_slice()) {
            if let Ok((t, _)) = m.begin_write(h, 1) {
                let _ = m.finish_write(t, pageproof_core::ops_write::Completion { ticket: t });
            }
            let _ = m.release(h);
        }
        proof {
            m.lemma_bounded();
        }
        i += 1;
    }
    proof {
        m.lemma_bounded();
    }
}

/// A scheduler loop over the coordinator: chunks, a deferred decode step behind the first ticket
/// (v0.5), and a completion with `stop` that orphans it (v0.6). Validity and the metadata bound
/// hold at every iteration, whatever the inputs and however the calls fail.
pub fn coord_churn(co: &mut Coordinator, reqs: &Vec<Vec<u32>>)
    requires
        old(co).inv(),
    ensures
        final(co).inv(),
        final(co).num_slot_records() == final(co).num_leases(),
{
    let mut i: usize = 0;
    while i < reqs.len()
        invariant
            co.inv(),
        decreases reqs.len() - i,
    {
        if let Ok((h, _, _)) = co.attach(reqs[i].as_slice()) {
            if let Ok((t, _)) = co.begin_write(h, 1, Drafts::Known(Vec::new()), false) {
                let _ = co.finish_write(t, CoordCompletion { ticket: t, accepted: 0, token: None, drafts: Vec::new(), stop: false });
            }
            let _ = co.extend(h, reqs[i].as_slice());
            if let Ok((t1, _)) = co.begin_write(h, reqs[i].len(), Drafts::Known(Vec::new()), false) {
                let _ = co.extend_deferred(h);
                let r2 = co.begin_write(h, 1, Drafts::Known(Vec::new()), false);
                let _ = co.finish_write(t1, CoordCompletion { ticket: t1, accepted: 0, token: None, drafts: Vec::new(), stop: true });
                if let Ok((t2, _)) = r2 {
                    let _ = co.finish_write(t2, CoordCompletion { ticket: t2, accepted: 0, token: None, drafts: Vec::new(), stop: false });
                }
            }
            let _ = co.release(h);
        }
        proof {
            co.lemma_bounded();
        }
        i += 1;
    }
    proof {
        co.lemma_bounded();
    }
}

/// v0.3: `release` right after a successful `attach` of the same lease succeeds (the lease is live
/// and has no pending ticket) and returns the input. The `Err` branch is proved unreachable.
pub fn attach_release(co: &mut Coordinator, toks: &Vec<u32>) -> (r: Option<Vec<u32>>)
    requires
        old(co).inv(),
    ensures
        final(co).inv(),
        r matches Some(t) ==> t@ == toks@,
{
    let ghost o = co@;
    match co.attach(toks.as_slice()) {
        Ok((h, cached, view)) => {
            let ghost mid = choose|mid: CoordV| #[trigger] coord_attached(o, mid, co@, toks@, cached as nat / o.b, tables_view(view.tables@), view.slots@);
            proof {
                old(co).lemma_public_shape();
                let k = cached as nat / o.b;
                assert(coord_attached(o, mid, co@, toks@, k, tables_view(view.tables@), view.slots@));
                // Paged class 0 attached a fresh lease `h` with input `toks` and no ticket.
                assert(co@.paged[0] == attached(mid.paged[0], toks@, tables_view(view.tables@)[0], k));
                assert(h.id == o.next_handle());
                assert(mid.paged[0].next_handle == o.paged[0].next_handle);
                assert(co@.leases().contains_key(h.id));
                assert(co@.leases()[h.id].pending.len() == 0);
                assert(co@.leases()[h.id].toks == toks@);
                assert(h.mgr == co@.id);
            }
            match co.release(h) {
                Ok(t) => Some(t),
                Err(_) => {
                    proof {
                        assert(false);
                    }
                    None
                },
            }
        },
        Err(_) => None,
    }
}

} // verus!
