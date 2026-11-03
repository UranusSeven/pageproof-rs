//! A verified client of the public `pageproof-core` specs.
//!
//! It checks that the public contracts are strong enough to reason about a scheduler step. On a
//! freshly created manager, attaching a 3-token request (one block, B = 4) must succeed with
//! `cached == 0`, by the C1 capacity rule. Only `create` itself may fail (id exhaustion).
use vstd::prelude::*;
use pageproof_core::manager::*;
use pageproof_core::types::*;
use pageproof_core::ops_attach::*;
use pageproof_core::arith::*;

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
                        pageproof_core::types::lemma_free_of(4, v.refs);
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

} // verus!
