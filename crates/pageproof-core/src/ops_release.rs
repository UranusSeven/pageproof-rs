//! C5 `release` and C6 `inspect` / `slot_of`.
use vstd::prelude::*;
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::arith::*;
use crate::manager::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// Abstract effect of releasing lease `h` (C5): drop the lease, decrement each page once.
pub open spec fn released(v: MgrV, h: u64) -> MgrV {
    let tbl = v.leases[h].table;
    MgrV {
        leases: v.leases.remove(h),
        refs: dec_seq(v.refs, tbl, tbl.len() as int),
        holders: Seq::new(v.p, |x: int| v.holders[x].remove(h)),
        ..v
    }
}

impl Manager {
    pub fn handle_ok(&self, h: Handle) -> (r: bool)
        requires
            self.valid(),
        ensures
            r == (h.mgr == self@.id && self@.leases.contains_key(h.id)),
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        h.mgr == self.id && self.leases.contains_key(&h.id)
    }

    pub(crate) proof fn lemma_rep_dom(&self)
        requires
            self.rep(),
        ensures
            forall|h: u64| #[trigger] self.leases@.contains_key(h) <==> self@.leases.contains_key(h),
            forall|t: u64| #[trigger] self.pend@.contains_key(t) <==> self@.pend.contains_key(t),
            forall|h: u64| #[trigger] self.leases@.contains_key(h) ==> self@.leases.contains_key(h) && lease_view(self.leases@[h]) == self@.leases[h],
            forall|t: u64| #[trigger] self.pend@.contains_key(t) ==> self@.pend.contains_key(t) && pend_view(self.pend@[t]) == self@.pend[t],
            self.id == self@.id,
            self.p as nat == self@.p,
            self.b as nat == self@.b,
            self.refs@ == self@.refs,
            self.keys@ == self@.keys,
            self.next_handle == self@.next_handle,
            self.next_ticket == self@.next_ticket,
    {
        assert forall|h: u64| #[trigger] self.leases@.contains_key(h) <==> self@.leases.contains_key(h) by {
            assert(self.leases@.dom().contains(h) == self@.leases.dom().contains(h));
        }
        assert forall|t: u64| #[trigger] self.pend@.contains_key(t) <==> self@.pend.contains_key(t) by {
            assert(self.pend@.dom().contains(t) == self@.pend.dom().contains(t));
        }
    }

    /// C6. Read-only view of a lease. No side effects.
    pub fn inspect(&self, h: Handle) -> (r: Result<RequestView, Error>)
        requires
            self.valid(),
        ensures
            r is Err <==> !(h.mgr == self@.id && self@.leases.contains_key(h.id)),
            r is Err ==> r == Err::<RequestView, Error>(Error::InvalidHandle),
            r matches Ok(rv) ==> {
                let l = self@.leases[h.id];
                &&& rv.len as nat == l.toks.len()
                &&& rv.computed as nat == l.c
                &&& rv.pages@ == l.table
                &&& rv.block_size as nat == self@.b
                &&& (rv.pending is Some) == (l.pending.len() > 0)
                &&& rv.pending matches Some(t) ==> t.mgr == self@.id && t.id == l.pending[0]
            },
    {
        if !self.handle_ok(h) {
            return Err(Error::InvalidHandle);
        }
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        let l = self.leases.get(&h.id).unwrap();
        let pending = if l.pending.len() > 0 { Some(Ticket { mgr: self.id, id: l.pending[0] }) } else { None };
        Ok(RequestView {
            len: l.toks.len(),
            computed: l.c,
            pages: vstd::slice::slice_to_vec(l.table.as_slice()),
            pending,
            block_size: self.b,
        })
    }

    /// C6 `slot_of(h, j)`: the allocated slot of position `j < L_h`.
    pub fn slot_of(&self, h: Handle, j: usize) -> (r: Result<usize, Error>)
        requires
            self.valid(),
        ensures
            !(h.mgr == self@.id && self@.leases.contains_key(h.id)) ==> r == Err::<usize, Error>(Error::InvalidHandle),
            (h.mgr == self@.id && self@.leases.contains_key(h.id)) ==> {
                let l = self@.leases[h.id];
                // Any position of the reach has an allocated slot (C6); only `j < c_h` holds valid KV.
                &&& (j as nat) < l.rho ==> r == Ok::<usize, Error>(slot_of(self@.b, l.table, j as int) as usize)
                    && slot_of(self@.b, l.table, j as int) < self@.p * self@.b
                &&& (j as nat) >= l.rho ==> r == Err::<usize, Error>(Error::InvalidArgument)
            },
    {
        if !self.handle_ok(h) {
            return Err(Error::InvalidHandle);
        }
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        let l = self.leases.get(&h.id).unwrap();
        if j >= l.rho {
            return Err(Error::InvalidArgument);
        }
        let ghost v = self@;
        let ghost lv = v.leases[h.id];
        proof {
            reveal(lease_ok);
            assert(lease_ok(v, self.den_log(), h.id));
            lemma_div_bounds(j as nat, v.b);
            // j / b < m because j < ρ <= m*b.
            let m = lv.table.len();
            if (j as nat) / v.b >= m {
                lemma_mul_mono(m, (j as nat) / v.b, v.b);
            }
            lemma_slot_of_props(v.b, v.p, lv.table, j as int);
            lemma_slot_bound(lv.table[(j / self.b) as int] as nat, (j % self.b) as nat, v.b, v.p);
        }
        let pg = l.table[j / self.b];
        Ok(pg * self.b + j % self.b)
    }
}


/// Decrement loop for `release`: decrements each page of `tbl` once and returns freed pages to
/// the free set. Purely concrete; the abstract proof is in `lemma_release_inv`.
fn dec_pages(
    refs: &mut Vec<u64>,
    free: &mut crate::idxset::IdxSet,
    tbl: &Vec<PageId>,
    Ghost(p): Ghost<nat>,
    Ghost(own): Ghost<Seq<bool>>,
)
    requires
        p <= max_slots(),
        forall|i: int| 0 <= i < tbl@.len() ==> own[#[trigger] tbl@[i] as int],
        old(refs)@.len() == p,
        old(free).wf(),
        old(free).universe() == p,
        old(free)@ == free_of(p, old(refs)@, own),
        tbl@.no_duplicates(),
        forall|i: int| 0 <= i < tbl@.len() ==> (#[trigger] tbl@[i] as nat) < p,
        forall|i: int| 0 <= i < tbl@.len() ==> old(refs)@[#[trigger] tbl@[i] as int] >= 1,
    ensures
        final(refs)@ == dec_seq(old(refs)@, tbl@, tbl@.len() as int),
        final(free).wf(),
        final(free).universe() == p,
        final(free)@ == free_of(p, final(refs)@, own),
{
    let ghost r0 = refs@;
    let mut i: usize = 0;
    proof {
        assert(dec_seq(r0, tbl@, 0) =~= r0);
    }
    while i < tbl.len()
        invariant
            0 <= i <= tbl@.len(),
            p <= max_slots(),
            r0.len() == p,
            refs@ == dec_seq(r0, tbl@, i as int),
            free.wf(),
            free.universe() == p,
            free@ == free_of(p, refs@, own),
            tbl@.no_duplicates(),
            forall|k: int| 0 <= k < tbl@.len() ==> (#[trigger] tbl@[k] as nat) < p,
            forall|k: int| 0 <= k < tbl@.len() ==> r0[#[trigger] tbl@[k] as int] >= 1,
            forall|k: int| 0 <= k < tbl@.len() ==> own[#[trigger] tbl@[k] as int],
        decreases tbl@.len() - i,
    {
        let x = tbl[i];
        let ghost before = refs@;
        proof {
            // x has not been decremented yet.
            assert(!tbl@.subrange(0, i as int).contains(x)) by {
                if tbl@.subrange(0, i as int).contains(x) {
                    let k = choose|k: int| 0 <= k < i && tbl@.subrange(0, i as int)[k] == x;
                    assert(tbl@[k] == tbl@[i as int]);
                }
            }
            assert(refs@[x as int] == r0[x as int]);
            assert(r0[x as int] >= 1);
        }
        let nv = refs[x] - 1;
        refs.set(x, nv);
        proof {
            let pre = tbl@.subrange(0, i as int);
            let post = tbl@.subrange(0, i + 1);
            assert(post =~= pre.push(x));
            assert forall|y: int| 0 <= y < r0.len() implies refs@[y] == dec_seq(r0, tbl@, i + 1)[y] by {
                vstd::seq_lib::lemma_seq_contains_after_push(pre, x, y as PageId);
                if y == x as int {
                    assert(post.contains(x)) by {
                        assert(post[i as int] == x);
                    }
                } else {
                    assert((y as PageId) != x);
                    assert(before[y] == dec_seq(r0, tbl@, i as int)[y]);
                }
            }
            assert(refs@ =~= dec_seq(r0, tbl@, i + 1));
            lemma_free_of(p, before, own);
            lemma_free_of(p, refs@, own);
        }
        if nv == 0 {
            proof {
                assert(!free@.contains(x)) by {
                    assert(before[x as int] != 0);
                }
            }
            free.insert(x);
            proof {
                assert forall|y: PageId| #[trigger] free@.contains(y) <==> free_of(p, refs@, own).contains(y) by {
                    if y != x {
                        assert(refs@[y as int] == before[y as int]);
                    }
                }
                assert(free@ =~= free_of(p, refs@, own));
            }
        } else {
            proof {
                assert forall|y: PageId| #[trigger] free@.contains(y) <==> free_of(p, refs@, own).contains(y) by {
                    if y != x {
                        assert(refs@[y as int] == before[y as int]);
                    }
                }
                assert(free@ =~= free_of(p, refs@, own));
            }
        }
        i += 1;
    }
}

impl Manager {
    /// C5. `release(h)`: drop the lease, decrement each page once; keys/Index/KV are retained.
    pub fn release(&mut self, h: Handle) -> (r: Result<Vec<Token>, Error>)
        requires
            old(self).valid(),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            !(h.mgr == old(self)@.id && old(self)@.leases.contains_key(h.id)) ==> r == Err::<Vec<Token>, Error>(
                Error::InvalidHandle,
            ) && final(self)@ == old(self)@,
            (h.mgr == old(self)@.id && old(self)@.leases.contains_key(h.id) && old(self)@.leases[h.id].pending.len() > 0)
                ==> r == Err::<Vec<Token>, Error>(Error::Busy) && final(self)@ == old(self)@,
            r matches Ok(toks) ==> {
                &&& h.mgr == old(self)@.id
                &&& old(self)@.leases.contains_key(h.id)
                &&& old(self)@.leases[h.id].pending.len() == 0
                &&& toks@ == old(self)@.leases[h.id].toks
                &&& final(self)@ == released(old(self)@, h.id)
            },
            r is Err ==> final(self)@ == old(self)@,
            (h.mgr == old(self)@.id && old(self)@.leases.contains_key(h.id) && old(self)@.leases[h.id].pending.len() == 0)
                ==> r is Ok,
    {
        if !self.handle_ok(h) {
            return Err(Error::InvalidHandle);
        }
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        if self.leases.get(&h.id).unwrap().pending.len() > 0 {
            return Err(Error::Busy);
        }
        let ghost v = self@;
        let ghost log = self.den_log();
        let ghost lv = v.leases[h.id];
        proof {
            reveal(lease_ok);
            reveal(page_ok);
            assert(lease_ok(v, log, h.id));
            lemma_mul_mono(1, v.b, v.p);
            assert(v.p <= v.p * v.b) by (nonlinear_arith) requires v.b >= 1;
            assert forall|i: int| 0 <= i < lv.table.len() implies v.refs[#[trigger] lv.table[i] as int] >= 1 by {
                let x = lv.table[i];
                assert(page_ok(v, log, x));
                assert(v.holders[x as int].contains(h.id));
                vstd::set::lemma_set_contains_len(v.holders[x as int], h.id);
            }
            assert forall|i: int| 0 <= i < lv.table.len() implies v.own[#[trigger] lv.table[i] as int] by {
                let x = lv.table[i];
                assert(page_ok(v, log, x));
                assert(v.holders[x as int].contains(h.id));
                vstd::set::lemma_set_contains_len(v.holders[x as int], h.id);
            }
        }
        let l = self.leases.remove(&h.id).unwrap();
        dec_pages(&mut self.refs, &mut self.free, &l.table, Ghost(self.p as nat), Ghost(v.own));
        let ghost v2 = released(v, h.id);
        proof {
            lemma_release_inv(v, log, h.id);
        }
        self.g = Ghost(v2);
        proof {
            assert(self.leases@.dom() =~= v2.leases.dom());
            assert forall|h2: u64| #[trigger] self.leases@.contains_key(h2) implies Self::head_ok(v2, self.leases@[h2]) by {
                assert(Self::head_ok(v, self.leases@[h2]));
            }
            assert(self.free@ == v2.free_set());
            assert(self.refs@ == v2.refs);
        }
        Ok(l.toks)
    }
}

/// `Valid` is preserved by `released` (the lease has no pending ticket).
pub proof fn lemma_release_inv(v: MgrV, log: Log, h: u64)
    requires
        inv(v, log),
        v.leases.contains_key(h),
        v.leases[h].pending.len() == 0,
    ensures
        inv(released(v, h), log),
{
    let v2 = released(v, h);
    let tbl = v.leases[h].table;
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    assert(lease_ok(v, log, h));
    assert(tbl.subrange(0, tbl.len() as int) =~= tbl);
    // Leases: unchanged except removal; keys and vmap unchanged.
    assert forall|h2: u64| #[trigger] v2.leases.contains_key(h2) implies lease_ok(v2, log, h2) by {
        assert(v.leases.contains_key(h2));
        assert(lease_ok(v, log, h2));
        let l = v.leases[h2];
        assert forall|i: nat| i < l.table.len() implies #[trigger] blk_ok(v2, log, l, i) by {
            assert(blk_ok(v, log, l, i));
        }
        assert forall|i: int| 0 <= i < l.pending.len() implies v2.pend.contains_key(#[trigger] l.pending[i])
            && v2.pend[l.pending[i]].lease == h2 by {
            assert(v.pend.contains_key(l.pending[i]));
        }
    }
    // Pages.
    assert forall|x: PageId| (x as nat) < v2.p implies #[trigger] page_ok(v2, log, x) by {
        assert(page_ok(v, log, x));
        assert(hold_ok(v, x));
        let hs = v.holders[x as int];
        let hs2 = v2.holders[x as int];
        assert(hs2 == hs.remove(h));
        assert forall|h2: u64| #[trigger] hs2.contains(h2) <==> (v2.leases.contains_key(h2) && v2.leases[h2].table.contains(x)) by {
        }
        if tbl.contains(x) {
            assert(hs.contains(h));
            vstd::set::lemma_set_remove_len(hs, h);
            assert(v2.refs[x as int] == v.refs[x as int] - 1);
        } else {
            assert(!hs.contains(h));
            assert(hs2 =~= hs);
            assert(v2.refs[x as int] == v.refs[x as int]);
        }
        assert(hold_ok(v2, x));
        if v.keys[x as int] is Some {
            assert(pub_ok(v, log, x));
            lemma_pub_frame(v, v2, log, log, x);
        }
        if v2.refs[x as int] > 1 {
            assert(v.refs[x as int] > 1);
        }
    }
    lemma_last_frame(v, v2);
    // Pending: no ticket belongs to h.
    assert forall|t: u64| #[trigger] v2.pend.contains_key(t) implies pend_ok(v2, t) by {
        assert(pend_ok(v, t));
        let r = v.pend[t];
        assert(r.lease != h) by {
            if r.lease == h {
                assert(v.leases[h].pending.contains(t));
            }
        }
    }
}

} // verus!
