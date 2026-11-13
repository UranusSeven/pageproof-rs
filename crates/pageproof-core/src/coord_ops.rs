//! v0.3 C2–C7 on the coordinator: every operation is applied to each paged class in lockstep and
//! to each state class, and is all-or-nothing. No trusted content.
use vstd::prelude::*;
use std::collections::HashMap;
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::arith::*;
use crate::manager::*;
use crate::state::*;
use crate::coord::*;
use crate::ops_release::*;
use crate::ops_extend::*;
use crate::ops_write::*;
use crate::slabplan::*;
use crate::coord_attach::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// C5 success relation: lease `h` released in every paged class; its slots freed with `⊥`.
pub open spec fn coord_released(o: CoordV, n: CoordV, h: u64) -> bool {
    &&& n.id == o.id
    &&& n.nslab == o.nslab
    &&& n.sbytes == o.sbytes
    &&& n.b == o.b
    &&& n.unit == o.unit
    &&& n.per == o.per
    &&& n.np == o.np
    &&& n.owner == o.owner
    &&& n.paged.len() == o.paged.len()
    &&& n.state.len() == o.state.len()
    &&& n.slots == o.slots.remove(h)
    &&& forall|c: int| 0 <= c < o.np ==> #[trigger] n.paged[c] == released(o.paged[c], h)
    &&& forall|j: int|
        0 <= j < o.nst() ==> #[trigger] n.state[j] == (StateV {
            holder: o.state[j].holder.update(o.slots[h][j] as int, None),
            w: o.state[j].w.update(o.slots[h][j] as int, None),
            ..o.state[j]
        })
}

/// C2 demand: `m' - m` blocks in every paged class, nothing in state classes.
pub open spec fn extend_demand(o: CoordV, d: nat) -> Seq<usize> {
    Seq::new(o.ncls(), |c: int| if c < o.np { d as usize } else { 0usize })
}

pub open spec fn no_prot(o: CoordV) -> Seq<bool> {
    Seq::new(o.nslab, |s: int| false)
}

/// C2 success relation: `mid` is `o` after the slab plan; then every paged class extended `h` by
/// `suffix` with fresh pages `fresh[c]`.
pub open spec fn coord_grown(o: CoordV, mid: CoordV, n: CoordV, h: u64, suffix: Seq<Token>, dfr: bool, d: nat, tables: Seq<Seq<PageId>>) -> bool {
    let l = o.leases()[h];
    let m = l.table.len();
    &&& mid.plan_rel(o, extend_demand(o, d), no_prot(o))
    &&& tables.len() == o.np
    &&& n.id == o.id
    &&& n.nslab == o.nslab
    &&& n.sbytes == o.sbytes
    &&& n.b == o.b
    &&& n.unit == o.unit
    &&& n.per == o.per
    &&& n.np == o.np
    &&& n.owner == mid.owner
    &&& n.paged.len() == o.paged.len()
    &&& n.state == mid.state
    &&& n.slots == mid.slots
    &&& forall|c: int|
        0 <= c < o.np ==> {
            let fresh = (#[trigger] tables[c]).subrange(o.paged[c].leases[h].table.len() as int, tables[c].len() as int);
            &&& tables[c].len() == o.reach_blocks(glen(l, suffix, dfr))
            &&& tables[c].subrange(0, o.paged[c].leases[h].table.len() as int) == o.paged[c].leases[h].table
            &&& fresh.len() == d
            &&& fresh.no_duplicates()
            &&& forall|j: int| 0 <= j < fresh.len() ==> mid.paged[c].is_free(#[trigger] fresh[j])
            &&& n.paged[c] == grown(mid.paged[c], h, suffix, fresh, dfr)
        }
}

/// The complete C2 (`dfr` false) and C2b (`dfr`, empty suffix) contracts.
pub open spec fn coord_grow_result(o: CoordV, n: CoordV, h: Handle, suffix: Seq<Token>, dfr: bool, r: Result<LeaseView, Error>) -> bool {
    let live = h.mgr == o.id && o.leases().contains_key(h.id);
    let l = o.leases()[h.id];
    let l2 = glen(l, suffix, dfr);
    // The tables grow from the old reach ρ_h to the new reach L' + μ (D18).
    let m2 = o.reach_blocks(l2);
    let d = (m2 - cdiv(l.rho, o.b)) as nat;
    // D21: pending tickets may stay if the queue has room and its head has no drafts or proposal
    // rows; every input position is computed or covered by a pending ticket.
    // ...and none is deferred; extend_deferred needs a pending ticket whose bonus position it
    // appends (D22).
    let busy = grow_busy(o.paged[0], l, dfr);
    let ph = !l.dfr && pfront_x(o.paged[0], l) == l.toks.len() && (dfr ==> l.pending.len() > 0);
    let arg = dfr || suffix.len() > 0;
    let ok = live && !busy && ph && arg && o.fits_m(m2);
    &&& !live ==> r == Err::<LeaseView, Error>(Error::InvalidHandle)
    &&& (live && busy) ==> r == Err::<LeaseView, Error>(Error::Busy)
    &&& (live && !busy && !ph) ==> r == Err::<LeaseView, Error>(Error::InvalidPhase)
    &&& (live && !busy && ph && !arg) ==> r == Err::<LeaseView, Error>(
        Error::InvalidArgument,
    )
    &&& (live && !busy && ph && arg && !o.fits_m(m2)) ==> r == Err::<
        LeaseView,
        Error,
    >(Error::RequestTooLarge)
    &&& ok ==> (r is Ok <==> o.cap(extend_demand(o, d), no_prot(o)))
    &&& (ok && !o.cap(extend_demand(o, d), no_prot(o))) ==> r == Err::<LeaseView, Error>(Error::NoCapacity)
    &&& r is Err ==> n == o
    &&& r matches Ok(view) ==> ok && exists|mid: CoordV| #[trigger] coord_grown(o, mid, n, h.id, suffix, dfr, d, tables_view(view.tables@))
}

pub open spec fn coord_extend_result(o: CoordV, n: CoordV, h: Handle, suffix: Seq<Token>, r: Result<LeaseView, Error>) -> bool {
    coord_grow_result(o, n, h, suffix, false, r)
}

/// C2b: `extend_deferred(h)`.
pub open spec fn coord_extend_deferred_result(o: CoordV, n: CoordV, h: Handle, r: Result<LeaseView, Error>) -> bool {
    coord_grow_result(o, n, h, Seq::<Token>::empty(), true, r)
}

pub proof fn lemma_extend_ok(o: CoordV, mid: CoordV, n: CoordV, h: Handle, suffix: Seq<Token>, dfr: bool, view: LeaseView)
    requires
        h.mgr == o.id,
        o.leases().contains_key(h.id),
        !grow_busy(o.paged[0], o.leases()[h.id], dfr),
        !o.leases()[h.id].dfr,
        pfront_x(o.paged[0], o.leases()[h.id]) == o.leases()[h.id].toks.len(),
        dfr ==> o.leases()[h.id].pending.len() > 0,
        dfr || suffix.len() > 0,
        o.fits_m(o.reach_blocks(glen(o.leases()[h.id], suffix, dfr))),
        o.cap(
            extend_demand(o, (o.reach_blocks(glen(o.leases()[h.id], suffix, dfr)) - cdiv(o.leases()[h.id].rho, o.b)) as nat),
            no_prot(o),
        ),
        coord_grown(
            o,
            mid,
            n,
            h.id,
            suffix,
            dfr,
            (o.reach_blocks(glen(o.leases()[h.id], suffix, dfr)) - cdiv(o.leases()[h.id].rho, o.b)) as nat,
            tables_view(view.tables@),
        ),
    ensures
        coord_grow_result(o, n, h, suffix, dfr, Ok(view)),
{
    let l = o.leases()[h.id];
    let l2 = glen(l, suffix, dfr);
    let d = (o.reach_blocks(l2) - cdiv(l.rho, o.b)) as nat;
    assert(coord_grown(o, mid, n, h.id, suffix, dfr, d, tables_view(view.tables@)));
    let r = Ok::<LeaseView, Error>(view);
    assert(r->Ok_0 == view);
    assert(exists|m2: CoordV| #[trigger] coord_grown(o, m2, n, h.id, suffix, dfr, d, tables_view(view.tables@)));
}

impl Coordinator {
    /// Lease `h` is live and its pending flag, executable.
    pub(crate) fn lease_live(&self, h: Handle) -> (r: Option<bool>)
        requires
            self.valid(),
        ensures
            r is None <==> !(h.mgr == self@.id && self@.leases().contains_key(h.id)),
            r matches Some(p) ==> p == (self@.leases()[h.id].pending.len() > 0),
    {
        proof {
            self.lemma_view();
            assert(self.paged@[0].valid());
        }
        if h.mgr != self.id {
            return None;
        }
        self.paged[0].lease_state(h.id)
    }

    /// C5. `release(h)` across every class.
    pub fn release(&mut self, h: Handle) -> (r: Result<Vec<Token>, Error>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            !(h.mgr == old(self)@.id && old(self)@.leases().contains_key(h.id)) ==> r == Err::<Vec<Token>, Error>(
                Error::InvalidHandle,
            ),
            (h.mgr == old(self)@.id && old(self)@.leases().contains_key(h.id) && old(self)@.leases()[h.id].pending.len() > 0)
                ==> r == Err::<Vec<Token>, Error>(Error::Busy),
            r is Err ==> final(self)@ == old(self)@,
            (h.mgr == old(self)@.id && old(self)@.leases().contains_key(h.id) && old(self)@.leases()[h.id].pending.len() == 0)
                ==> r is Ok,
            r matches Ok(toks) ==> {
                &&& h.mgr == old(self)@.id
                &&& old(self)@.leases().contains_key(h.id)
                &&& old(self)@.leases()[h.id].pending.len() == 0
                &&& toks@ == old(self)@.leases()[h.id].toks
                &&& coord_released(old(self)@, final(self)@, h.id)
            },
    {
        match self.lease_live(h) {
            None => return Err(Error::InvalidHandle),
            Some(true) => return Err(Error::Busy),
            Some(false) => {},
        }
        let ghost o = *self;
        proof {
            o.lemma_view();
        }
        let mut toks: Vec<Token> = Vec::new();
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                o.valid(),
                o.pv(0).leases.contains_key(h.id),
                o.pv(0).leases[h.id].pending.len() == 0,
                self.npaged == o.npaged,
                self.paged@.len() == o.paged@.len(),
                self.state@ == o.state@,
                self.slots@ == o.slots@,
                self.id == o.id,
                self.nslab == o.nslab,
                self.sbytes == o.sbytes,
                self.b == o.b,
                self.unit@ == o.unit@,
                self.per@ == o.per@,
                self.owner@ == o.owner@,
                self.fs == o.fs,
                c <= self.npaged,
                c > 0 ==> toks@ == o.pv(0).leases[h.id].toks,
                forall|c2: int| c <= c2 < o.np() ==> #[trigger] self.paged@[c2] == o.paged@[c2],
                forall|c2: int|
                    0 <= c2 < c ==> (#[trigger] self.paged@[c2]).valid() && self.pv(c2) == released(o.pv(c2), h.id),
            decreases self.npaged - c,
        {
            proof {
                assert(self.paged@[c as int] == o.paged@[c as int]);
                assert(o.paged@[c as int].valid());
                assert(o.pv(c as int).leases.contains_key(h.id));
                assert(o.pv(c as int).leases[h.id].pending == o.pv(0).leases[h.id].pending);
            }
            let mid = self.paged[c].mgr_id();
            let ghost p0 = self.paged@;
            proof {
                assert(self.pv(c as int) == o.pv(c as int));
                assert(self.pv(c as int).leases.contains_key(h.id));
                assert(self.pv(c as int).leases[h.id].pending.len() == 0);
            }
            let r = self.paged[c].release(Handle { mgr: mid, id: h.id });
            proof {
                assert forall|c2: int| 0 <= c2 < p0.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
            }
            match r {
                Ok(t) => {
                    if c == 0 {
                        toks = t;
                    }
                },
                Err(_) => {
                    proof {
                        assert(false);
                    }
                },
            }
            proof {
                assert(o.pv(c as int).leases[h.id].toks == o.pv(0).leases[h.id].toks);
                assert forall|c2: int| 0 <= c2 < c + 1 implies (#[trigger] self.paged@[c2]).valid() && self.pv(c2) == released(
                    o.pv(c2),
                    h.id,
                ) by {
                    if c2 < c {
                        assert(self.paged@[c2] == p0[c2]);
                    }
                }
            }
            c += 1;
        }
        let ghost pg = self.paged@;
        let sl = self.slots.remove(&h.id).unwrap();
        let mut j: usize = 0;
        proof {
            assert(o.slots@.contains_key(h.id));
            assert(sl@ == o.slots@[h.id]@);
        }
        while j < self.state.len()
            invariant
                o.valid(),
                o.slots@.contains_key(h.id),
                sl@ == o.slots@[h.id]@,
                self.paged@ == pg,
                self.state@.len() == o.state@.len(),
                j <= self.state@.len(),
                forall|j2: int| j <= j2 < o.nst() ==> #[trigger] self.state@[j2] == o.state@[j2],
                forall|j2: int|
                    0 <= j2 < j ==> (#[trigger] self.state@[j2]).valid() && self.sv(j2) == (StateV {
                        holder: o.sv(j2).holder.update(sl@[j2] as int, None),
                        w: o.sv(j2).w.update(sl@[j2] as int, None),
                        ..o.sv(j2)
                    }),
            decreases self.state@.len() - j,
        {
            proof {
                assert(self.state@[j as int] == o.state@[j as int]);
                assert(o.state@[j as int].valid());
                assert(o.slots@[h.id]@.len() == o.nst());
            }
            let x = sl[j];
            let ghost s0 = self.state@;
            self.state[j].release_slot(x);
            proof {
                assert forall|j2: int| 0 <= j2 < s0.len() && j2 != j implies #[trigger] self.state@[j2] == s0[j2] by {}
                assert forall|j2: int|
                    0 <= j2 < j + 1 implies (#[trigger] self.state@[j2]).valid() && self.sv(j2) == (StateV {
                    holder: o.sv(j2).holder.update(sl@[j2] as int, None),
                    w: o.sv(j2).w.update(sl@[j2] as int, None),
                    ..o.sv(j2)
                }) by {
                    if j2 < j {
                        assert(self.state@[j2] == s0[j2]);
                    }
                }
            }
            j += 1;
        }
        proof {
            self.lemma_release_valid(&o, h.id);
        }
        Ok(toks)
    }

    proof fn lemma_release_valid(&self, o: &Coordinator, h: u64)
        requires
            o.valid(),
            o.pv(0).leases.contains_key(h),
            o.pv(0).leases[h].pending.len() == 0,
            self.id == o.id,
            self.nslab == o.nslab,
            self.sbytes == o.sbytes,
            self.b == o.b,
            self.npaged == o.npaged,
            self.unit@ == o.unit@,
            self.per@ == o.per@,
            self.owner@ == o.owner@,
            self.fs == o.fs,
            self.paged@.len() == o.paged@.len(),
            self.state@.len() == o.state@.len(),
            self.slots@ == o.slots@.remove(h),
            forall|c: int| 0 <= c < o.np() ==> (#[trigger] self.paged@[c]).valid() && self.pv(c) == released(o.pv(c), h),
            forall|j: int|
                0 <= j < o.nst() ==> (#[trigger] self.state@[j]).valid() && self.sv(j) == (StateV {
                    holder: o.sv(j).holder.update(o.slots@[h]@[j] as int, None),
                    w: o.sv(j).w.update(o.slots@[h]@[j] as int, None),
                    ..o.sv(j)
                }),
        ensures
            self.valid(),
            coord_released(o@, self@, h),
    {
        assert forall|c: int| 0 <= c < o.np() implies (#[trigger] self.pv(c)).own == o.pv(c).own && self.pv(c).p == o.pv(c).p
            && self.pv(c).b == o.pv(c).b && self.pv(c).ns == o.pv(c).ns && self.pv(c).cfg == o.pv(c).cfg && self.pv(c).leases == o.pv(c).leases.remove(h)
            && self.pv(c).pend == o.pv(c).pend && self.pv(c).next_handle == o.pv(c).next_handle && self.pv(c).next_ticket
            == o.pv(c).next_ticket by {
            assert(self.paged@[c].valid());
        }
        assert(self.cfg_ok());
        assert(self.pools_ok()) by {
            assert forall|i: int| 0 <= i < self.np() implies {
                &&& #[trigger] self.paged@[i].valid()
                &&& self.pv(i).p == self.cunits(i)
                &&& self.pv(i).b == self.b as nat
                &&& self.pv(i).ns == self.pv(0).ns
                &&& self.pv(i).cfg == self.pv(0).cfg
                &&& cfg_rel(self.pv(i).cfg, self.np())
            } by {
                assert(o.paged@[i].valid());
                assert(self.pv(i).p == o.pv(i).p);
                assert(self.pv(0).ns == o.pv(0).ns);
                assert(self.pv(0).cfg == o.pv(0).cfg);
            }
            assert forall|j: int| 0 <= j < self.nst() implies {
                &&& #[trigger] self.state@[j].valid()
                &&& self.sv(j).p == self.cunits(self.np() + j)
            } by {
                assert(o.state@[j].valid());
            }
        }
        assert(self.own_ok()) by {
            assert forall|c: int, x: int| 0 <= c < self.ncls() && 0 <= x < self.cunits(c) implies #[trigger] self.cown(c, x)
                == (self.owner@[x / (self.per_c(c) as int)] == c + 1) by {
                assert(o.cown(c, x) == (o.owner@[x / (o.per_c(c) as int)] == c + 1));
                if c < self.np() {
                    assert(self.pv(c).own == o.pv(c).own);
                } else {
                    assert(self.sv(c - self.np()).own == o.sv(c - self.np()).own);
                }
            }
        }
        assert(self.lock_ok()) by {
            assert forall|i: int| #![trigger self.paged@[i]] 0 <= i < self.np() implies {
                &&& self.pv(i).leases.dom() == self.pv(0).leases.dom()
                &&& self.pv(i).pend == self.pv(0).pend
                &&& self.pv(i).next_handle == self.pv(0).next_handle
                &&& self.pv(i).next_ticket == self.pv(0).next_ticket
            } by {
                assert(o.paged@[i] == o.paged@[i]);
                assert(self.pv(i).leases.dom() == o.pv(i).leases.dom().remove(h));
                assert(self.pv(0).leases.dom() == o.pv(0).leases.dom().remove(h));
            }
            assert forall|i: int, h2: u64| 0 <= i < self.np() && #[trigger] self.pv(i).leases.contains_key(h2) implies {
                &&& self.pv(i).leases[h2].toks == self.pv(0).leases[h2].toks
                &&& self.pv(i).leases[h2].c == self.pv(0).leases[h2].c
                &&& self.pv(i).leases[h2].pending == self.pv(0).leases[h2].pending
                &&& self.pv(i).leases[h2].rho == self.pv(0).leases[h2].rho
                &&& self.pv(i).leases[h2].dfr == self.pv(0).leases[h2].dfr
            } by {
                assert(o.pv(i).leases.contains_key(h2));
            }
            assert forall|h2: u64| #[trigger] self.pv(0).leases.contains_key(h2) implies self.fits_m(
                cdiv(self.pv(0).leases[h2].rho, self.b as nat),
            ) by {
                assert(o.pv(0).leases.contains_key(h2));
            }
        }
        assert(self.slots_ok()) by {
            assert(self.slots@.dom() =~= self.pv(0).leases.dom());
            assert forall|h2: u64| #[trigger] self.slots@.contains_key(h2) implies self.slots@[h2]@.len() == self.nst() by {
                assert(o.slots@.contains_key(h2));
            }
            assert forall|h2: u64, j: int|
                #![trigger self.slots@[h2]@[j]]
                self.slots@.contains_key(h2) && 0 <= j < self.nst() implies {
                let x = self.slots@[h2]@[j];
                let l2 = self.pv(0).leases[h2];
                &&& (x as nat) < self.sv(j).p
                &&& self.sv(j).holder[x as int] == Some(h2)
                &&& l2.c > 0 ==> self.sv(j).w[x as int] == Some(l2.toks.subrange(0, l2.c as int))
            } by {
                assert(o.slots@.contains_key(h2));
                let x = o.slots@[h2]@[j];
                assert(o.sv(j).holder[x as int] == Some(h2));
                let y = o.slots@[h]@[j];
                assert(o.sv(j).holder[y as int] == Some(h));
                assert(x != y);
            }
            assert forall|j: int, x: int|
                #![trigger self.sv(j).holder[x]]
                0 <= j < self.nst() && 0 <= x < self.sv(j).p && self.sv(j).holder[x] is Some implies {
                let h2 = self.sv(j).holder[x]->Some_0;
                &&& self.slots@.contains_key(h2)
                &&& self.slots@[h2]@[j] as int == x
            } by {
                assert(o.sv(j).holder[x] is Some);
                let h2 = o.sv(j).holder[x]->Some_0;
                if h2 == h {
                    assert(o.slots@[h]@[j] as int == x);
                }
            }
        }
        self.lemma_view();
        o.lemma_view();
        assert(self@.slots =~= o@.slots.remove(h));
        assert forall|c: int| 0 <= c < o@.np implies #[trigger] self@.paged[c] == released(o@.paged[c], h) by {}
        assert forall|j: int| 0 <= j < o@.nst() implies #[trigger] self@.state[j] == (StateV {
            holder: o@.state[j].holder.update(o@.slots[h][j] as int, None),
            w: o@.state[j].w.update(o@.slots[h][j] as int, None),
            ..o@.state[j]
        }) by {}
    }
}


impl Coordinator {
    /// Paged table length of a live lease is `cdiv(L, B)`.
    pub(crate) proof fn lemma_table_len(&self, c: int, h: u64)
        requires
            self.valid(),
            0 <= c < self.np(),
            self.pv(c).leases.contains_key(h),
        ensures
            self.pv(c).leases[h].table.len() == cdiv(self.pv(c).leases[h].rho, self.b as nat),
    {
        assert(self.paged@[c].valid());
        reveal(lease_ok);
        assert(lease_ok(self.pv(c), self.paged@[c].den_log(), h));
        let l = self.pv(c).leases[h];
        let m = l.table.len();
        let q = cdiv(l.rho, self.b as nat);
        lemma_cdiv_props(l.rho, self.b as nat);
        if m < q {
            lemma_mul_mono(m, (q - 1) as nat, self.b as nat);
        }
        if m > q {
            lemma_mul_mono(q, (m - 1) as nat, self.b as nat);
        }
    }

    /// `valid` after extending lease `h` in every paged class (state classes untouched).
    /// `pools_ok` carries over a step that keeps every pool valid, with its size, B, namespace and
    /// configuration. Kept small: the restatement is fragile inside large proof contexts.
    pub(crate) proof fn lemma_pools_frame(&self, o: &Coordinator)
        requires
            o.pools_ok(),
            self.npaged == o.npaged,
            self.paged@.len() == o.paged@.len(),
            self.state@.len() == o.state@.len(),
            self.unit@ == o.unit@,
            self.per@ == o.per@,
            self.nslab == o.nslab,
            self.b == o.b,
            forall|i: int|
                0 <= i < o.np() ==> {
                    &&& (#[trigger] self.paged@[i]).valid()
                    &&& self.pv(i).p == o.pv(i).p
                    &&& self.pv(i).b == o.pv(i).b
                    &&& self.pv(i).ns == o.pv(i).ns
                    &&& self.pv(i).cfg == o.pv(i).cfg
                },
            forall|j: int|
                0 <= j < o.nst() ==> {
                    &&& (#[trigger] self.state@[j]).valid()
                    &&& self.sv(j).p == o.sv(j).p
                },
        ensures
            self.pools_ok(),
    {
        assert forall|i: int| 0 <= i < self.np() implies {
            &&& #[trigger] self.paged@[i].valid()
            &&& self.pv(i).p == self.cunits(i)
            &&& self.pv(i).b == self.b as nat
            &&& self.pv(i).ns == self.pv(0).ns
            &&& self.pv(i).cfg == self.pv(0).cfg
            &&& cfg_rel(self.pv(i).cfg, self.np())
        } by {
            assert(o.paged@[i].valid());
            assert(o.paged@[0].valid());
            assert(self.paged@[0].valid());
        }
        assert forall|j: int| 0 <= j < self.nst() implies {
            &&& #[trigger] self.state@[j].valid()
            &&& self.sv(j).p == self.cunits(self.np() + j)
        } by {
            assert(o.state@[j].valid());
        }
    }

    proof fn lemma_extend_valid(&self, mid: &Coordinator, h: u64, suffix: Seq<Token>, dfr: bool)
        requires
            mid.valid(),
            mid.pv(0).leases.contains_key(h),
            mid.fits_m(cdiv(glen(mid.pv(0).leases[h], suffix, dfr) + mid.pv(0).cfg.mu, mid.b as nat)),
            self.id == mid.id,
            self.nslab == mid.nslab,
            self.sbytes == mid.sbytes,
            self.b == mid.b,
            self.npaged == mid.npaged,
            self.unit@ == mid.unit@,
            self.per@ == mid.per@,
            self.owner@ == mid.owner@,
            self.fs == mid.fs,
            self.paged@.len() == mid.paged@.len(),
            self.state@ == mid.state@,
            self.slots@ == mid.slots@,
            forall|c: int|
                0 <= c < mid.np() ==> {
                    &&& (#[trigger] self.paged@[c]).valid()
                    &&& self.pv(c).own == mid.pv(c).own
                    &&& self.pv(c).p == mid.pv(c).p
                    &&& self.pv(c).b == mid.pv(c).b
                    &&& self.pv(c).ns == mid.pv(c).ns
                    &&& self.pv(c).cfg == mid.pv(c).cfg
                    &&& self.pv(c).pend == mid.pv(c).pend
                    &&& self.pv(c).next_handle == mid.pv(c).next_handle
                    &&& self.pv(c).next_ticket == mid.pv(c).next_ticket
                    &&& self.pv(c).leases == mid.pv(c).leases.insert(
                        h,
                        LeaseV {
                            toks: mid.pv(c).leases[h].toks + suffix,
                            table: self.pv(c).leases[h].table,
                            rho: glen(mid.pv(c).leases[h], suffix, dfr) + mid.pv(c).cfg.mu,
                            dfr: mid.pv(c).leases[h].dfr || dfr,
                            ..mid.pv(c).leases[h]
                        },
                    )
                },
        ensures
            self.valid(),
    {
        assert(self.cfg_ok());
        self.lemma_pools_frame(mid);
        assert(self.own_ok()) by {
            assert forall|c: int, x: int| 0 <= c < self.ncls() && 0 <= x < self.cunits(c) implies #[trigger] self.cown(c, x)
                == (self.owner@[x / (self.per_c(c) as int)] == c + 1) by {
                assert(mid.cown(c, x) == (mid.owner@[x / (mid.per_c(c) as int)] == c + 1));
                if c < self.np() {
                    assert(self.paged@[c].valid());
                }
            }
        }
        assert(self.paged@[0].valid());
        assert(self.lock_ok()) by {
            assert forall|i: int| #![trigger self.paged@[i]] 0 <= i < self.np() implies {
                &&& self.pv(i).leases.dom() == self.pv(0).leases.dom()
                &&& self.pv(i).pend == self.pv(0).pend
                &&& self.pv(i).next_handle == self.pv(0).next_handle
                &&& self.pv(i).next_ticket == self.pv(0).next_ticket
            } by {
                assert(mid.paged@[i] == mid.paged@[i]);
                assert(self.pv(i).leases.dom() =~= mid.pv(i).leases.dom());
                assert(self.pv(0).leases.dom() =~= mid.pv(0).leases.dom());
            }
            assert forall|i: int, h2: u64| 0 <= i < self.np() && #[trigger] self.pv(i).leases.contains_key(h2) implies {
                &&& self.pv(i).leases[h2].toks == self.pv(0).leases[h2].toks
                &&& self.pv(i).leases[h2].c == self.pv(0).leases[h2].c
                &&& self.pv(i).leases[h2].pending == self.pv(0).leases[h2].pending
                &&& self.pv(i).leases[h2].rho == self.pv(0).leases[h2].rho
                &&& self.pv(i).leases[h2].dfr == self.pv(0).leases[h2].dfr
            } by {
                assert(self.paged@[i].valid());
                assert(mid.pv(i).leases.contains_key(h2));
                assert(mid.paged@[i] == mid.paged@[i]);
                assert(mid.pv(i).leases.contains_key(h));
                // Every class shares the configuration, so they agree on the new reach.
                assert(mid.pv(i).cfg == mid.pv(0).cfg);
                assert(mid.pv(i).leases[h].toks == mid.pv(0).leases[h].toks);
                assert(mid.pv(i).leases[h].dfr == mid.pv(0).leases[h].dfr);
            }
            assert forall|h2: u64| #[trigger] self.pv(0).leases.contains_key(h2) implies self.fits_m(
                cdiv(self.pv(0).leases[h2].rho, self.b as nat),
            ) by {
                assert(mid.pv(0).leases.contains_key(h2));
            }
        }
        assert(self.slots_ok()) by {
            assert(self.slots@.dom() =~= self.pv(0).leases.dom());
            assert forall|h2: u64, j: int|
                #![trigger self.slots@[h2]@[j]]
                self.slots@.contains_key(h2) && 0 <= j < self.nst() implies {
                let x = self.slots@[h2]@[j];
                let l2 = self.pv(0).leases[h2];
                &&& (x as nat) < self.sv(j).p
                &&& self.sv(j).holder[x as int] == Some(h2)
                &&& l2.c > 0 ==> self.sv(j).w[x as int] == Some(l2.toks.subrange(0, l2.c as int))
            } by {
                assert(mid.slots@.contains_key(h2));
                if h2 == h {
                    let l0 = mid.pv(0).leases[h];
                    let l2 = self.pv(0).leases[h];
                    if l2.c > 0 {
                        assert(l2.c == l0.c);
                        assert(l2.toks == l0.toks + suffix);
                        reveal(lease_ok);
                        assert(mid.paged@[0].valid());
                        assert(lease_ok(mid.pv(0), mid.paged@[0].den_log(), h));
                        assert(l2.toks.subrange(0, l2.c as int) =~= l0.toks.subrange(0, l0.c as int));
                    }
                }
            }
            assert forall|j: int, x: int|
                #![trigger self.sv(j).holder[x]]
                0 <= j < self.nst() && 0 <= x < self.sv(j).p && self.sv(j).holder[x] is Some implies {
                let h2 = self.sv(j).holder[x]->Some_0;
                &&& self.slots@.contains_key(h2)
                &&& self.slots@[h2]@[j] as int == x
            } by {
                assert(self.state@[j] == mid.state@[j]);
                assert(mid.sv(j).holder[x] is Some);
            }
        }
    }

    /// C2. `extend(h, suffix)` across every class.
    pub fn extend(&mut self, h: Handle, suffix: &[Token]) -> (r: Result<LeaseView, Error>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            coord_extend_result(old(self)@, final(self)@, h, suffix@, r),
    {
        self.grow(h, suffix, false)
    }

    /// C2b. `extend_deferred(h)`: append the bonus position of the newest pending ticket, whose
    /// token is not yet on the host (D22).
    pub fn extend_deferred(&mut self, h: Handle) -> (r: Result<LeaseView, Error>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            coord_extend_deferred_result(old(self)@, final(self)@, h, r),
    {
        let none: Vec<Token> = Vec::new();
        proof {
            assert(none@ =~= Seq::<Token>::empty());
        }
        self.grow(h, none.as_slice(), true)
    }

    /// C2 and C2b.
    fn grow(&mut self, h: Handle, suffix: &[Token], dfr: bool) -> (r: Result<LeaseView, Error>)
        requires
            old(self).inv(),
            dfr ==> suffix@.len() == 0,
        ensures
            final(self).inv(),
            coord_grow_result(old(self)@, final(self)@, h, suffix@, dfr, r),
    {
        let ghost o = *self;
        let ghost ov = o@;
        if self.lease_live(h).is_none() {
            return Err(Error::InvalidHandle);
        }
        proof {
            o.lemma_view();
            assert(self.paged@[0].valid());
            assert(ov.paged[0] == o.pv(0));
        }
        let (busy0, pf) = self.paged[0].extend_gate(h.id);
        let (q, _pf) = self.paged[0].queue_info(h.id);
        let cfg = self.cfg_exec();
        // C2b: extend_deferred needs only room in the queue; extend also a head without drafts or
        // proposal rows (D21).
        let busy = if dfr { q > cfg.delta } else { busy0 };
        if busy {
            return Err(Error::Busy);
        }
        let (len, _c0, _) = self.paged[0].lease_info(h.id);
        if self.paged[0].lease_dfr(h.id) || pf != len || (dfr && q == 0) {
            return Err(Error::InvalidPhase);
        }
        if !dfr && suffix.len() == 0 {
            return Err(Error::InvalidArgument);
        }
        // The input grows by the suffix, or by the deferred position (D22).
        let add: usize = if dfr { 1 } else { suffix.len() };
        let b = self.b;
        let rho = self.paged[0].lease_rho(h.id);
        let mu = cfg.mu;
        proof {
            self.lemma_table_len(0, h.id);
            reveal(lease_ok);
            assert(lease_ok(self.pv(0), self.paged@[0].den_log(), h.id));
            // No deferred position yet: L̂_h = L_h, so ρ <= L + μ (I16).
            assert(rho <= len + mu);
            self.lemma_nslab_bound();
            assert(self.fits_m(cdiv(rho as nat, b as nat)));
            lemma_fits_bound(self.per@, self.np(), self.nst(), self.nslab as nat, cdiv(rho as nat, b as nat), 0);
            assert(self.unit@[0] >= 1);
            lemma_cdiv_props(rho as nat, b as nat);
            lemma_mul_mono(cdiv(rho as nat, b as nat), self.cunits(0), b as nat);
            assert(len <= rho);
            assert(mu as nat == ov.mu());
            assert(ov.leases()[h.id].rho == rho as nat);
        }
        // The new reach L' + μ past the slot space cannot fit (D18).
        if add > MAX_SLOTS as usize - len || mu > MAX_SLOTS as usize - len - add {
            proof {
                assert(!ov.fits_m(ov.reach_blocks((len + add) as nat))) by {
                    if ov.fits_m(ov.reach_blocks((len + add) as nat)) {
                        lemma_fits_bound(self.per@, self.np(), self.nst(), self.nslab as nat, ov.reach_blocks((len + add) as nat), 0);
                        lemma_cdiv_props((len + add) as nat + mu as nat, b as nat);
                        lemma_mul_mono(ov.reach_blocks((len + add) as nat), self.cunits(0), b as nat);
                    }
                }
            }
            return Err(Error::RequestTooLarge);
        }
        let l2 = len + add;
        let nr2 = l2 + mu;
        let m = (rho - 1) / b + 1;
        let m2 = (nr2 - 1) / b + 1;
        proof {
            assert(rho >= 1);
            vstd::arithmetic::div_mod::lemma_div_plus_one((rho - 1) as int, b as int);
            vstd::arithmetic::div_mod::lemma_div_plus_one((nr2 - 1) as int, b as int);
            assert(((rho - 1 + b) as int) / (b as int) == ((rho - 1) as int) / (b as int) + 1);
            assert(((nr2 - 1 + b) as int) / (b as int) == ((nr2 - 1) as int) / (b as int) + 1);
            assert(m as nat == cdiv(rho as nat, b as nat));
            assert(m2 as nat == cdiv(nr2 as nat, b as nat));
            assert(m2 as nat == ov.reach_blocks(l2 as nat));
            // ρ <= L + μ < L' + μ (I16).
            assert(rho <= len + mu);
            lemma_cdiv_mono(rho as nat, nr2 as nat, b as nat);
        }
        if !self.fits_exec(m2) {
            return Err(Error::RequestTooLarge);
        }
        let dd = m2 - m;
        let k_all = self.unit.len();
        let mut d: Vec<usize> = Vec::new();
        let mut c: usize = 0;
        while c < k_all
            invariant
                k_all as nat == self.ncls(),
                self.npaged as nat == self.np(),
                c <= k_all,
                d@.len() == c,
                forall|c2: int| 0 <= c2 < c ==> #[trigger] d@[c2] == extend_demand(ov, dd as nat)[c2],
                ov.ncls() == self.ncls(),
                ov.np == self.np(),
            decreases k_all - c,
        {
            d.push(if c < self.npaged { dd } else { 0 });
            c += 1;
        }
        let prot: Vec<bool> = vec![false; self.nslab];
        proof {
            assert(d@ =~= extend_demand(ov, dd as nat));
            assert(prot@ =~= no_prot(ov));
            assert forall|c2: int| 0 <= c2 < d@.len() implies #[trigger] d@[c2] <= max_slots() by {
                lemma_cdiv_le(nr2 as nat, b as nat, max_slots());
                assert(nr2 as nat <= max_slots() * (b as nat)) by (nonlinear_arith) requires nr2 <= max_slots(), b >= 1;
            }
        }
        if !self.check_cap(&d, &prot) {
            return Err(Error::NoCapacity);
        }
        let ghost pre = *self;
        self.run_plan(&d, &prot);
        let ghost mid = *self;
        proof {
            mid.lemma_view();
            pre.lemma_view();
            mid.lemma_view_cls();
            assert forall|c2: int| 0 <= c2 < mid.np() implies (#[trigger] mid.pv(c2)).leases == pre.pv(c2).leases
                && mid.pv(c2).free_set().len() >= dd && mid.pv(c2).id == pre.pv(c2).id by {
                assert(mid.paged@[c2] == mid.paged@[c2]);
                assert(mid@.cfree(c2) >= d@[c2]);
            }
            // The slab plan changes only ownership and keys of paged classes.
            assert(mid@.paged[0] == (MgrV { own: mid@.paged[0].own, keys: mid@.paged[0].keys, ..pre@.paged[0] }));
            assert(mid.pv(0).pend == pre.pv(0).pend);
            assert(mid.pv(0).cfg == pre.pv(0).cfg);
            assert(pre.pv(0) == o.pv(0));
        }
        let mut tables: Vec<Vec<PageId>> = Vec::new();
        let ghost lv0 = mid.pv(0).leases[h.id];
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                mid.valid(),
                mid.pv(0).leases.contains_key(h.id),
                !grow_busy(mid.pv(0), mid.pv(0).leases[h.id], dfr),
                !mid.pv(0).leases[h.id].dfr,
                pfront_x(mid.pv(0), mid.pv(0).leases[h.id]) == len,
                dfr ==> mid.pv(0).leases[h.id].pending.len() > 0,
                dfr ==> suffix@.len() == 0,
                mid.pv(0).leases[h.id].toks.len() == len,
                add as nat == (if dfr { 1nat } else { suffix@.len() }),
                l2 == len + add,
                nr2 == l2 + mu,
                mu as nat == mid.pv(0).cfg.mu,
                rho as nat == mid.pv(0).leases[h.id].rho,
                dfr || suffix@.len() > 0,
                m2 as nat == cdiv(nr2 as nat, b as nat),
                m as nat == cdiv(rho as nat, b as nat),
                dd == m2 - m,
                b == mid.b,
                mid.fits_m(m2 as nat),
                forall|c2: int| 0 <= c2 < mid.np() ==> (#[trigger] mid.pv(c2)).free_set().len() >= dd,
                self.npaged == mid.npaged,
                self.paged@.len() == mid.paged@.len(),
                self.state@ == mid.state@,
                self.slots@ == mid.slots@,
                self.id == mid.id,
                self.nslab == mid.nslab,
                self.sbytes == mid.sbytes,
                self.b == mid.b,
                self.unit@ == mid.unit@,
                self.per@ == mid.per@,
                self.owner@ == mid.owner@,
                self.fs == mid.fs,
                c <= self.npaged,
                tables@.len() == c,
                forall|c2: int| c <= c2 < mid.np() ==> #[trigger] self.paged@[c2] == mid.paged@[c2],
                forall|c2: int|
                    0 <= c2 < c ==> (#[trigger] self.paged@[c2]).valid() && grow_result(
                        mid.pv(c2),
                        self.pv(c2),
                        Handle { mgr: mid.pv(c2).id, id: h.id },
                        suffix@,
                        dfr,
                        Ok(PageTableView { pages: tables@[c2] }),
                    ),
            decreases self.npaged - c,
        {
            proof {
                assert(self.paged@[c as int] == mid.paged@[c as int]);
                assert(mid.paged@[c as int].valid());
                mid.lemma_table_len(c as int, h.id);
                assert(mid.pv(c as int).leases[h.id].toks == mid.pv(0).leases[h.id].toks);
                assert(mid.pv(c as int).leases[h.id].c == mid.pv(0).leases[h.id].c);
                assert(mid.pv(c as int).leases[h.id].pending == mid.pv(0).leases[h.id].pending);
                assert(mid.pv(c as int).leases[h.id].rho == mid.pv(0).leases[h.id].rho);
                assert(mid.pv(c as int).cfg == mid.pv(0).cfg);
                assert(mid.pv(c as int).pend == mid.pv(0).pend);
                assert(grow_busy(mid.pv(c as int), mid.pv(c as int).leases[h.id], dfr) == grow_busy(mid.pv(0), mid.pv(0).leases[h.id], dfr));
                assert(mid.pv(c as int).leases[h.id].dfr == mid.pv(0).leases[h.id].dfr);
                assert(pfront_x(mid.pv(c as int), mid.pv(c as int).leases[h.id]) == pfront_x(mid.pv(0), mid.pv(0).leases[h.id]));
                assert(mid.unit@[c as int] >= 1);
                lemma_fits_bound(mid.per@, mid.np(), mid.nst(), mid.nslab as nat, m2 as nat, c as int);
                lemma_cdiv_props(nr2 as nat, b as nat);
                lemma_mul_mono(m2 as nat, mid.cunits(c as int), b as nat);
            }
            let mid_c = self.paged[c].mgr_id();
            let ghost p0 = self.paged@;
            let r = self.paged[c].grow(Handle { mgr: mid_c, id: h.id }, suffix, dfr);
            proof {
                assert forall|c2: int| 0 <= c2 < p0.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
            }
            match r {
                Ok(view) => {
                    let ghost tb = tables@;
                    tables.push(view.pages);
                    proof {
                        assert forall|c2: int| 0 <= c2 < c + 1 implies (#[trigger] self.paged@[c2]).valid() && grow_result(
                            mid.pv(c2),
                            self.pv(c2),
                            Handle { mgr: mid.pv(c2).id, id: h.id },
                            suffix@,
                            dfr,
                            Ok(PageTableView { pages: tables@[c2] }),
                        ) by {
                            if c2 < c {
                                assert(self.paged@[c2] == p0[c2]);
                                assert(tables@[c2] == tb[c2]);
                            }
                        }
                    }
                },
                Err(_) => {
                    proof {
                        assert(false);
                    }
                    return Err(Error::NoCapacity);
                },
            }
            c += 1;
        }
        proof {
            o.lemma_view();
            pre.lemma_view();
            assert(mid.pv(0).leases[h.id] == ov.leases()[h.id]) by {
                assert(ov.paged[0] == pre.pv(0));
            }
            Self::lemma_extend_post(&o, &pre, &mid, self, h.id, suffix@, dfr, dd as nat, d@, prot@, &tables);
            assert(self.slots@.contains_key(h.id)) by {
                assert(mid.slots@.dom() == mid.pv(0).leases.dom());
            }
        }
        let slv = vstd::slice::slice_to_vec(self.slots.get(&h.id).unwrap().as_slice());
        let lv = LeaseView { tables, slots: slv };
        proof {
            assert(ov.leases()[h.id].toks.len() == len);
            assert(ov.leases()[h.id].rho == rho as nat);
            assert(dd as nat == (ov.reach_blocks(l2 as nat) - cdiv(rho as nat, b as nat)) as nat);
            assert(ov.b == b as nat);
            lemma_extend_ok(ov, mid@, self@, h, suffix@, dfr, lv);
        }
        Ok(lv)
    }

    proof fn lemma_extend_post(
        o: &Coordinator,
        pre: &Coordinator,
        mid: &Coordinator,
        fin: &Coordinator,
        h: u64,
        suffix: Seq<Token>,
        dfr: bool,
        dd: nat,
        d: Seq<usize>,
        prot: Seq<bool>,
        tables: &Vec<Vec<PageId>>,
    )
        requires
            o.valid(),
            o@ == pre@,
            pre.valid(),
            mid.valid(),
            d == extend_demand(o@, dd),
            prot == no_prot(o@),
            mid@.plan_rel(pre@, d, prot),
            mid.pv(0).leases.contains_key(h),
            mid.fits_m(cdiv(glen(mid.pv(0).leases[h], suffix, dfr) + mid.pv(0).cfg.mu, mid.b as nat)),
            dd == cdiv(glen(mid.pv(0).leases[h], suffix, dfr) + mid.pv(0).cfg.mu, mid.b as nat) - cdiv(
                mid.pv(0).leases[h].rho,
                mid.b as nat,
            ),
            forall|c2: int| 0 <= c2 < mid.np() ==> (#[trigger] mid.pv(c2)).leases == pre.pv(c2).leases,
            fin.npaged == mid.npaged,
            fin.paged@.len() == mid.paged@.len(),
            fin.state@ == mid.state@,
            fin.slots@ == mid.slots@,
            fin.id == mid.id,
            fin.nslab == mid.nslab,
            fin.sbytes == mid.sbytes,
            fin.b == mid.b,
            fin.unit@ == mid.unit@,
            fin.per@ == mid.per@,
            fin.owner@ == mid.owner@,
            fin.fs == mid.fs,
            tables@.len() == mid.np(),
            forall|c2: int|
                0 <= c2 < mid.np() ==> (#[trigger] fin.paged@[c2]).valid() && grow_result(
                    mid.pv(c2),
                    fin.pv(c2),
                    Handle { mgr: mid.pv(c2).id, id: h },
                    suffix,
                    dfr,
                    Ok(PageTableView { pages: tables@[c2] }),
                ),
        ensures
            fin.valid(),
            coord_grown(o@, mid@, fin@, h, suffix, dfr, dd, tables_view(tables@)),
    {
        assert forall|c: int| 0 <= c < mid.np() implies {
            &&& (#[trigger] fin.paged@[c]).valid()
            &&& fin.pv(c).own == mid.pv(c).own
            &&& fin.pv(c).p == mid.pv(c).p
            &&& fin.pv(c).b == mid.pv(c).b
            &&& fin.pv(c).ns == mid.pv(c).ns
            &&& fin.pv(c).cfg == mid.pv(c).cfg
            &&& fin.pv(c).pend == mid.pv(c).pend
            &&& fin.pv(c).next_handle == mid.pv(c).next_handle
            &&& fin.pv(c).next_ticket == mid.pv(c).next_ticket
            &&& fin.pv(c).leases == mid.pv(c).leases.insert(
                h,
                LeaseV { toks: mid.pv(c).leases[h].toks + suffix, table: fin.pv(c).leases[h].table, rho: glen(mid.pv(c).leases[h], suffix, dfr) + mid.pv(c).cfg.mu, dfr: mid.pv(c).leases[h].dfr || dfr, ..mid.pv(c).leases[h] },
            )
        } by {
            let fresh = tables@[c]@.subrange(mid.pv(c).leases[h].table.len() as int, tables@[c]@.len() as int);
            assert(fin.pv(c) == grown(mid.pv(c), h, suffix, fresh, dfr));
        }
        assert(mid.pv(0).leases[h] == fin.pv(0).leases[h] || true);
        fin.lemma_extend_valid(mid, h, suffix, dfr);
        o.lemma_view();
        pre.lemma_view();
        mid.lemma_view();
        fin.lemma_view();
        let tv = tables_view(tables@);
        assert forall|c: int| 0 <= c < o@.np implies {
            let fresh = (#[trigger] tv[c]).subrange(o@.paged[c].leases[h].table.len() as int, tv[c].len() as int);
            &&& tv[c].len() == o@.reach_blocks(glen(o@.leases()[h], suffix, dfr))
            &&& tv[c].subrange(0, o@.paged[c].leases[h].table.len() as int) == o@.paged[c].leases[h].table
            &&& fresh.len() == dd
            &&& fresh.no_duplicates()
            &&& forall|j: int| 0 <= j < fresh.len() ==> mid@.paged[c].is_free(#[trigger] fresh[j])
            &&& fin@.paged[c] == grown(mid@.paged[c], h, suffix, fresh, dfr)
        } by {
            assert(tv[c] == tables@[c]@);
            assert(o@.paged[c] == pre.pv(c));
            assert(mid.pv(c).leases == pre.pv(c).leases);
            assert(mid.paged@[c].valid());
            assert(mid.pv(c).leases.contains_key(h));
            assert(mid.pv(c).leases[h].toks == mid.pv(0).leases[h].toks);
            assert(mid.pv(c).leases[h].rho == mid.pv(0).leases[h].rho);
            assert(mid.pv(c).cfg == mid.pv(0).cfg);
            assert(o@.mu() == mid.pv(0).cfg.mu) by {
                assert(o@.paged[0] == pre.pv(0));
                // The slab plan changes only ownership and keys of paged classes.
                assert(mid@.paged[0] == (MgrV { own: mid@.paged[0].own, keys: mid@.paged[0].keys, ..pre@.paged[0] }));
                assert(mid@.paged[0] == mid.pv(0));
                assert(pre@.paged[0] == pre.pv(0));
            }
            mid.lemma_table_len(c, h);
            mid.lemma_table_len(0, h);
            assert(o@.paged[0] == pre.pv(0));
            assert(o@.leases()[h] == mid.pv(0).leases[h]);
            assert(mid@.paged[c] == mid.pv(c));
            assert(fin@.paged[c] == fin.pv(c));
            let mv = mid.pv(c);
            let l = mv.leases[h];
            let r = Ok::<PageTableView, Error>(PageTableView { pages: tables@[c] });
            assert(grow_result(mv, fin.pv(c), Handle { mgr: mv.id, id: h }, suffix, dfr, r));
            let view = r->Ok_0;
            assert(view.pages@ == tables@[c]@);
            let fresh = view.pages@.subrange(l.table.len() as int, view.pages@.len() as int);
            assert(view.pages@.len() == cdiv(glen(l, suffix, dfr) + mv.cfg.mu, mv.b));
            assert(fresh.len() == cdiv(glen(l, suffix, dfr) + mv.cfg.mu, mv.b) - l.table.len());
            assert(forall|j: int| 0 <= j < fresh.len() ==> mv.is_free(#[trigger] fresh[j]));
            assert(fin.pv(c) == grown(mv, h, suffix, fresh, dfr));
            assert(l.toks.len() == o@.leases()[h].toks.len());
            assert(mid@.b == o@.b);
            assert(mv.b == o@.b);
        }
        assert(fin@.state =~= mid@.state);
        assert(fin@.slots =~= mid@.slots);
    }
}


/// Execution plan of the coordinator: one per paged class, plus the live state slots.
pub struct CoordPlan {
    pub ticket: Ticket,
    pub handle: Handle,
    /// `T_h[a:z] ++ D` at positions `[a, z + k)`.
    pub input_ids: Vec<Token>,
    pub positions: Vec<usize>,
    pub block_size: usize,
    /// `lo`: the start bound, `p_h` at issue (D24). The window starts at `lo + σ` with `σ <= slack`.
    pub lo: usize,
    /// `s`: the slack, the drafts the older pending tickets may accept; 0 with known inputs.
    pub slack: usize,
    /// `ℓ`: the input length.
    pub num_inputs: usize,
    /// `k`: the drafts after the input (D16); the sampler checks the outputs at `[z-1, z+k)`.
    pub num_drafts: usize,
    /// The drafter classes also write `λ` proposal rows after the drafts (D20).
    pub propose: bool,
    /// Per paged class: write slots of `[a, z + k)` (plus `λ` in a drafter class with
    /// `propose`) and the page mapping of the same range.
    pub write_slots: Vec<Vec<usize>>,
    pub page_tables: Vec<Vec<PageId>>,
    /// Per state class: `σ_h^c`.
    pub state_slots: Vec<usize>,
    /// The state slots start from the initial state (`a == 0`, E10).
    pub init: bool,
    /// For a continuation, the ticket whose bonus token is the input (D24); its `input_ids`
    /// are placeholders that the executor resolves on the device.
    pub producer: Option<Ticket>,
}

/// The drafts of a ticket (C3): tokens the host holds, or the number a continuation takes from
/// its producer's proposal on the device (D24).
pub enum Drafts {
    Known(Vec<Token>),
    Deferred(usize),
}

pub open spec fn drafts_known(d: Drafts) -> bool {
    d is Known
}

/// The drafts a plan feeds: the host's tokens, or `k` placeholders that the executor fills from
/// the producer's proposal (D24).
pub open spec fn drafts_seq(d: Drafts) -> Seq<Token> {
    match d {
        Drafts::Known(v) => v@,
        Drafts::Deferred(k) => Seq::new(k as nat, |q: int| 0u32),
    }
}

/// The plan's inputs: `T_h[a:z] ++ D`, or placeholders for a continuation, whose input is the
/// deferred position `z - 1 = L_h` (D24).
pub open spec fn cinputs(l: LeaseV, a: nat, z: nat, d: Seq<Token>) -> Seq<Token> {
    if z <= l.toks.len() { l.toks.subrange(a as int, z as int) + d } else { Seq::new(((z - a) as nat) + d.len(), |q: int| 0u32) }
}

/// C3 plan correctness across classes: inputs `T_h[p_h : p_h + n] ++ D` from the planned frontier.
pub open spec fn cplan_ok(o: CoordV, h: u64, n: nat, d: Seq<Token>, propose: bool, plan: CoordPlan) -> bool {
    let l = o.leases()[h];
    let a = pfront(o.paged[0], l);
    let z = a + n;
    let k = d.len();
    &&& plan.ticket == Ticket { mgr: o.id, id: o.next_ticket() }
    &&& plan.handle == Handle { mgr: o.id, id: h }
    &&& plan.block_size as nat == o.b
    &&& plan.input_ids@ == cinputs(l, a, z, d)
    // A continuation names its producer, the newest pending ticket (D24).
    &&& plan.producer == if z > l.toks.len() { Some(Ticket { mgr: o.id, id: l.pending[0] }) } else { None }
    &&& plan.positions@.len() == n + k
    &&& forall|q: int| 0 <= q < n + k ==> #[trigger] plan.positions@[q] as int == a + q
    &&& plan.lo as nat == a
    &&& plan.slack as nat == sdr(o.paged[0], l)
    &&& plan.num_inputs as nat == n
    &&& plan.num_drafts as nat == k
    &&& plan.propose == propose
    &&& plan.write_slots@.len() == o.np
    &&& plan.page_tables@.len() == o.np
    // Per paged class (`cplan_class`): write slots, page mapping, and §9.0 (b).
    &&& forall|c: int| 0 <= c < o.np ==> #[trigger] cplan_class(o, h, n, d, propose, plan, c)
    &&& plan.state_slots@ == o.slots[h]
    &&& plan.init == (a == 0)
    // The slot holds the state after the computed prefix; once the earlier tickets in Q_h have run,
    // it holds the state after T_h[0:a] (E13).
    &&& forall|j: int|
        0 <= j < o.nst() ==> {
            &&& o.state[j].holder[(#[trigger] plan.state_slots@[j]) as int] == Some(h)
            &&& l.c > 0 ==> o.state[j].w[plan.state_slots@[j] as int] == Some(l.toks.subrange(0, l.c as int))
        }
}

/// The same lease/ticket update in every paged class, everything else unchanged.
pub open spec fn paged_step(o: CoordV, n: CoordV) -> bool {
    &&& n.id == o.id
    &&& n.nslab == o.nslab
    &&& n.sbytes == o.sbytes
    &&& n.b == o.b
    &&& n.unit == o.unit
    &&& n.per == o.per
    &&& n.np == o.np
    &&& n.owner == o.owner
    &&& n.paged.len() == o.paged.len()
    &&& n.state.len() == o.state.len()
    &&& n.slots == o.slots
}

/// Arguments C3 accepts on a live lease whose queue can take the ticket: `0 < n <= L̂ - p_h`,
/// `k <= λ`, drafts only after the whole planned input, and `propose` only with drafter classes
/// and after the whole planned input. `Deferred` drafts only for a continuation (its input reaches
/// the deferred position, `p_h + n > L_h`), and `Deferred(k > 0)` only when the producer, the
/// newest pending ticket, has `propose` (D24).
pub open spec fn coord_begin_ok(o: CoordV, h: u64, n: nat, d: Drafts, propose: bool) -> bool {
    let l = o.leases()[h];
    let p = pfront(o.paged[0], l);
    let k = drafts_seq(d).len();
    &&& !drafts_known(d) ==> p + n > l.toks.len()
    &&& (!drafts_known(d) && k > 0) ==> o.pend()[l.pending[l.pending.len() - 1]].propose
    &&& 0 < n
    &&& p + n <= lhat(l)
    &&& k <= o.lam()
    &&& k > 0 ==> p + n == lhat(l)
    &&& propose ==> o.ntarget() < o.np && p + n == lhat(l)
}

/// Success relation of C3: the plan, and every paged class's ticket record.
pub open spec fn coord_begun(o: CoordV, n: CoordV, h: u64, k: nat, d: Seq<Token>, propose: bool, ddr: bool, plan: CoordPlan) -> bool {
    &&& cplan_ok(o, h, k, d, propose, plan)
    &&& paged_step(o, n)
    &&& n.state == o.state
    &&& forall|c: int| 0 <= c < o.np ==> #[trigger] n.paged[c] == began_d(o.paged[c], h, k, d, propose, ddr)
}

pub open spec fn coord_begin_result(
    o: CoordV,
    n: CoordV,
    h: Handle,
    k: usize,
    d: Drafts,
    propose: bool,
    r: Result<(Ticket, CoordPlan), Error>,
) -> bool {
    let live = h.mgr == o.id && o.leases().contains_key(h.id);
    let l = o.leases()[h.id];
    // D21: the queue is full, or host-known drafts would follow a pending ticket.
    let busy = l.pending.len() > o.delta() || (l.pending.len() > 0 && drafts_known(d) && drafts_seq(d).len() > 0);
    let ok = coord_begin_ok(o, h.id, k as nat, d, propose);
    &&& !live ==> r == Err::<(Ticket, CoordPlan), Error>(Error::InvalidHandle)
    &&& (live && busy) ==> r == Err::<(Ticket, CoordPlan), Error>(Error::Busy)
    &&& (live && !busy && !ok) ==> r == Err::<(Ticket, CoordPlan), Error>(Error::InvalidArgument)
    &&& (live && !busy && ok) ==> (r is Ok <==> o.next_ticket() < u64::MAX)
    &&& (live && !busy && ok && o.next_ticket() == u64::MAX) ==> r == Err::<(Ticket, CoordPlan), Error>(
        Error::IdentifierExhausted,
    )
    &&& r is Err ==> n == o
    &&& r matches Ok((t, plan)) ==> {
        &&& live
        &&& t == plan.ticket
        &&& coord_begun(o, n, h.id, k as nat, drafts_seq(d), propose, !drafts_known(d), plan)
    }
}

/// The executor's completion notice for a coordinator ticket (C4): its acceptance count, the token
/// it sampled after its input and accepted drafts, the drafts it accepted, and `stop` (D25, not
/// yet supported). Its truth is the external assumption E1/E5/E13.
pub struct CoordCompletion {
    pub ticket: Ticket,
    pub accepted: usize,
    pub token: Option<Token>,
    pub drafts: Vec<Token>,
    pub stop: bool,
}

/// The state after binding the deferred token `x` of lease `h` in every paged class (D22).
pub open spec fn coord_bound(o: CoordV, h: u64, x: Token) -> CoordV {
    CoordV { paged: Seq::new(o.paged.len(), |c: int| bound(o.paged[c], h, x)), ..o }
}

/// The state after committing the accepted drafts `xs` of `t` in every paged class (D17, D24).
pub open spec fn coord_committed_t(o: CoordV, t: u64, xs: Seq<Token>) -> CoordV {
    CoordV { paged: Seq::new(o.paged.len(), |c: int| committed_t(o.paged[c], t, xs)), ..o }
}

/// Success relation of the completion step: `finish_rel` in every paged class and the state after
/// `T_h[0:z]` in every live state slot.
pub open spec fn coord_finished(o: CoordV, n: CoordV, t: u64, z: usize) -> bool {
    let pr = o.pend()[t];
    let h = pr.lease;
    let l = o.leases()[h];
    &&& z as nat == pr.z
    &&& paged_step(o, n)
    &&& forall|c: int| 0 <= c < o.np ==> #[trigger] finish_rel(o.paged[c], n.paged[c], t)
    // §9.0 (c) for state classes: every live slot now holds the state after `T_h[0:z]`.
    &&& forall|j: int|
        0 <= j < o.nst() ==> #[trigger] n.state[j] == (StateV {
            w: o.state[j].w.update(o.slots[h][j] as int, Some(l.toks.subrange(0, pr.z as int))),
            ..o.state[j]
        })
}

/// C4: with acceptance count n, `T'_h = T_h ++ D[0:n]` and `c'_h = z + n` (D17); every state slot
/// then holds the state after `T'_h[0:z+n]` (D19, E11). A continuation with deferred drafts
/// reports the `n` drafts it accepted (D24). A ticket heading `X_h` must report the token `x` it
/// sampled after them: `T'_h = T_h ++ D[0:n] ++ [x]` (D22).
pub open spec fn coord_finish_result(o: CoordV, n: CoordV, t: Ticket, comp: CoordCompletion, r: Result<usize, Error>) -> bool {
    let live = t.mgr == o.id && o.pend().contains_key(t.id) && comp.ticket == t && o.leases()[o.pend()[t.id].lease].pending[0] == t.id;
    let pr = o.pend()[t.id];
    let h = pr.lease;
    let dfr = o.leases()[h].dfr;
    let na = comp.accepted as nat;
    // The drafts come from the completion only for a continuation with deferred drafts.
    let dk = pr.ddr && pr.drafts.len() > 0;
    let xs = if dk { comp.drafts@ } else { pr.drafts.subrange(0, na as int) };
    let ok = na <= pr.drafts.len() && !comp.stop && (dfr ==> comp.token is Some) && (dk ==> comp.drafts@.len() == na);
    // Commit the accepted drafts, then bind the deferred token after them.
    let oc = coord_committed_t(o, t.id, xs);
    let ob = if dfr { coord_bound(oc, h, comp.token->Some_0) } else { oc };
    &&& !live ==> r == Err::<usize, Error>(Error::InvalidTicket)
    &&& (live && !ok) ==> r == Err::<usize, Error>(Error::InvalidArgument)
    &&& (live && ok) ==> r is Ok
    &&& r is Err ==> n == o
    &&& r matches Ok(z) ==> live && ok && coord_finished(ob, n, t.id, z)
}

/// Plan facts of paged class `c` (one conjunct of `cplan_ok`), stated over class `c`'s own lease.
pub open spec fn cplan_class(o: CoordV, h: u64, n: nat, d: Seq<Token>, propose: bool, plan: CoordPlan, c: int) -> bool {
    let l = o.leases()[h];
    let lc = o.paged[c].leases[h];
    let a = pfront(o.paged[c], lc);
    let w = a + sdr(o.paged[c], lc) + n + d.len() + o.ext_of(c, propose);
    &&& plan.write_slots@[c]@.len() == w - a
    &&& forall|q: int| 0 <= q < w - a ==> #[trigger] plan.write_slots@[c]@[q] as int == slot_of(o.b, lc.table, a + q)
    &&& forall|q: int| 0 <= q < w - a ==> (#[trigger] plan.write_slots@[c]@[q] as nat) < o.paged[c].p * o.b
    &&& forall|q1: int, q2: int|
        0 <= q1 < w - a && 0 <= q2 < w - a && q1 != q2 ==> #[trigger] plan.write_slots@[c]@[q1] != #[trigger] plan.write_slots@[c]@[q2]
    &&& forall|q: int| 0 <= q < w - a ==> write_page_ok(o.paged[c], h, #[trigger] lc.table[(a + q) / (o.b as int)])
    &&& plan.page_tables@[c]@ == lc.table.subrange(0, cdiv(w, o.b) as int)
    // §9.0 (b): the computed prefix is valid KV; the rest of `[0, a)` once earlier tickets complete.
    &&& forall|j: int| 0 <= j < lc.c ==> (o.paged[c].vmap)(#[trigger] slot_of(o.b, lc.table, j)) == l.toks.subrange(0, j + 1)
}

impl Coordinator {
    /// Validity after a lockstep step that changes only leases (frontier/pending), tickets and the
    /// ghost KV state in every paged class, and only provenance of live slots in state classes.
    proof fn lemma_step_valid(&self, o: &Coordinator, h: u64)
        requires
            o.valid(),
            o.pv(0).leases.contains_key(h),
            self.id == o.id,
            self.nslab == o.nslab,
            self.sbytes == o.sbytes,
            self.b == o.b,
            self.npaged == o.npaged,
            self.unit@ == o.unit@,
            self.per@ == o.per@,
            self.owner@ == o.owner@,
            self.fs == o.fs,
            self.paged@.len() == o.paged@.len(),
            self.state@.len() == o.state@.len(),
            self.slots@ == o.slots@,
            forall|c: int|
                0 <= c < o.np() ==> {
                    &&& (#[trigger] self.paged@[c]).valid()
                    &&& self.pv(c).own == o.pv(c).own
                    &&& self.pv(c).p == o.pv(c).p
                    &&& self.pv(c).b == o.pv(c).b
                    &&& self.pv(c).ns == o.pv(c).ns
                    &&& self.pv(c).cfg == o.pv(c).cfg
                    &&& self.pv(c).next_handle == o.pv(c).next_handle
                    &&& self.pv(c).leases.dom() == o.pv(c).leases.dom()
                    &&& forall|h2: u64| #[trigger] o.pv(c).leases.contains_key(h2) && h2 != h ==> self.pv(c).leases[h2]
                        == o.pv(c).leases[h2]
                    &&& self.pv(c).leases[h].toks == self.pv(0).leases[h].toks
                    &&& self.pv(c).leases[h].rho == o.pv(c).leases[h].rho
                    &&& self.pv(c).leases[h].c == self.pv(0).leases[h].c
                    &&& self.pv(c).leases[h].pending == self.pv(0).leases[h].pending
                    &&& self.pv(c).leases[h].rho == self.pv(0).leases[h].rho
                    &&& self.pv(c).leases[h].dfr == self.pv(0).leases[h].dfr
                    &&& self.pv(c).pend == self.pv(0).pend
                    &&& self.pv(c).next_ticket == self.pv(0).next_ticket
                },
            forall|j: int|
                0 <= j < o.nst() ==> {
                    &&& (#[trigger] self.state@[j]).valid()
                    &&& self.sv(j).own == o.sv(j).own
                    &&& self.sv(j).holder == o.sv(j).holder
                    &&& self.sv(j).p == o.sv(j).p
                    &&& forall|x: int| 0 <= x < o.sv(j).p && x != o.slots@[h]@[j] ==> #[trigger] self.sv(j).w[x] == o.sv(j).w[x]
                    &&& (self.pv(0).leases[h].c > 0 ==> self.sv(j).w[o.slots@[h]@[j] as int] == Some(
                        self.pv(0).leases[h].toks.subrange(0, self.pv(0).leases[h].c as int),
                    ))
                },
        ensures
            self.valid(),
    {
        assert(self.paged@[0].valid());
        assert(self.cfg_ok());
        assert(self.pools_ok()) by {
            assert forall|i: int| 0 <= i < self.np() implies {
                &&& #[trigger] self.paged@[i].valid()
                &&& self.pv(i).p == self.cunits(i)
                &&& self.pv(i).b == self.b as nat
                &&& self.pv(i).ns == self.pv(0).ns
                &&& self.pv(i).cfg == self.pv(0).cfg
                &&& cfg_rel(self.pv(i).cfg, self.np())
            } by {
                assert(o.paged@[i].valid());
            }
            assert forall|j: int| 0 <= j < self.nst() implies {
                &&& #[trigger] self.state@[j].valid()
                &&& self.sv(j).p == self.cunits(self.np() + j)
            } by {
                assert(o.state@[j].valid());
            }
        }
        assert(self.own_ok()) by {
            assert forall|c: int, x: int| 0 <= c < self.ncls() && 0 <= x < self.cunits(c) implies #[trigger] self.cown(c, x)
                == (self.owner@[x / (self.per_c(c) as int)] == c + 1) by {
                assert(o.cown(c, x) == (o.owner@[x / (o.per_c(c) as int)] == c + 1));
                if c < self.np() {
                    assert(self.paged@[c].valid());
                } else {
                    assert(self.state@[c - self.np()].valid());
                }
            }
        }
        assert(self.lock_ok()) by {
            assert forall|i: int| #![trigger self.paged@[i]] 0 <= i < self.np() implies {
                &&& self.pv(i).leases.dom() == self.pv(0).leases.dom()
                &&& self.pv(i).pend == self.pv(0).pend
                &&& self.pv(i).next_handle == self.pv(0).next_handle
                &&& self.pv(i).next_ticket == self.pv(0).next_ticket
            } by {
                assert(o.paged@[i] == o.paged@[i]);
            }
            assert forall|i: int, h2: u64| 0 <= i < self.np() && #[trigger] self.pv(i).leases.contains_key(h2) implies {
                &&& self.pv(i).leases[h2].toks == self.pv(0).leases[h2].toks
                &&& self.pv(i).leases[h2].c == self.pv(0).leases[h2].c
                &&& self.pv(i).leases[h2].pending == self.pv(0).leases[h2].pending
                &&& self.pv(i).leases[h2].rho == self.pv(0).leases[h2].rho
                &&& self.pv(i).leases[h2].dfr == self.pv(0).leases[h2].dfr
            } by {
                assert(self.paged@[i].valid());
                assert(o.pv(i).leases.contains_key(h2));
                assert(o.paged@[i] == o.paged@[i]);
                if h2 != h {
                    assert(o.pv(0).leases.contains_key(h2));
                    assert(self.pv(0).leases[h2] == o.pv(0).leases[h2]);
                }
            }
            assert forall|h2: u64| #[trigger] self.pv(0).leases.contains_key(h2) implies self.fits_m(
                cdiv(self.pv(0).leases[h2].rho, self.b as nat),
            ) by {
                assert(o.pv(0).leases.contains_key(h2));
                if h2 != h {
                    assert(self.pv(0).leases[h2] == o.pv(0).leases[h2]);
                } else {
                    assert(self.pv(0).leases[h].rho == o.pv(0).leases[h].rho);
                }
            }
        }
        assert(self.slots_ok()) by {
            assert(self.slots@.dom() =~= self.pv(0).leases.dom());
            assert forall|h2: u64, j: int|
                #![trigger self.slots@[h2]@[j]]
                self.slots@.contains_key(h2) && 0 <= j < self.nst() implies {
                let x = self.slots@[h2]@[j];
                let l2 = self.pv(0).leases[h2];
                &&& (x as nat) < self.sv(j).p
                &&& self.sv(j).holder[x as int] == Some(h2)
                &&& l2.c > 0 ==> self.sv(j).w[x as int] == Some(l2.toks.subrange(0, l2.c as int))
            } by {
                assert(o.slots@.contains_key(h2));
                assert(self.state@[j].valid());
                if h2 != h {
                    let x = o.slots@[h2]@[j];
                    assert(o.sv(j).holder[x as int] == Some(h2));
                    let y = o.slots@[h]@[j];
                    assert(o.sv(j).holder[y as int] == Some(h));
                    assert(x != y);
                    assert(self.pv(0).leases[h2] == o.pv(0).leases[h2]);
                }
            }
            assert forall|j: int, x: int|
                #![trigger self.sv(j).holder[x]]
                0 <= j < self.nst() && 0 <= x < self.sv(j).p && self.sv(j).holder[x] is Some implies {
                let h2 = self.sv(j).holder[x]->Some_0;
                &&& self.slots@.contains_key(h2)
                &&& self.slots@[h2]@[j] as int == x
            } by {
                assert(self.state@[j].valid());
                assert(o.sv(j).holder[x] is Some);
            }
        }
    }
}


impl Coordinator {
    /// C3. `begin_write(h, n, drafts, propose)`: one ticket whose plan feeds `T_h[c : c+n] ++ D` and
    /// covers every class; with `propose`, the drafter classes also get `λ` proposal rows (D20).
    pub fn begin_write(&mut self, h: Handle, n: usize, drafts: Drafts, propose: bool) -> (r: Result<(Ticket, CoordPlan), Error>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            coord_begin_result(old(self)@, final(self)@, h, n, drafts, propose, r),
    {
        let ghost o = *self;
        let ghost ov = o@;
        let ghost dseq = drafts_seq(drafts);
        let ghost dknown = drafts_known(drafts);
        if self.lease_live(h).is_none() {
            return Err(Error::InvalidHandle);
        }
        proof {
            o.lemma_view();
            assert(self.paged@[0].valid());
            assert(ov.paged[0] == o.pv(0));
        }
        let (q, pf) = self.paged[0].queue_info(h.id);
        let cfg = self.cfg_exec();
        // D21: at most δ + 1 tickets in flight.
        if q > cfg.delta {
            return Err(Error::Busy);
        }
        // Host-known drafts need an empty queue (D21).
        if let Drafts::Known(v) = &drafts {
            if q > 0 && v.len() > 0 {
                return Err(Error::Busy);
            }
        }
        // A continuation's deferred drafts: k placeholders, filled on the device (D24).
        let (dv, ddr): (Vec<Token>, bool) = match drafts {
            Drafts::Known(v) => (v, false),
            Drafts::Deferred(kk) => {
                if kk > cfg.lam {
                    return Err(Error::InvalidArgument);
                }
                (vec![0u32; kk], true)
            },
        };
        proof {
            assert(dv@ =~= dseq);
            assert(ddr == !dknown);
        }
        let (len, _c0, _) = self.paged[0].lease_info(h.id);
        proof {
            reveal(lease_ok);
            assert(lease_ok(self.pv(0), self.paged@[0].den_log(), h.id));
            assert(self.pv(0).p * self.pv(0).b <= max_slots());
        }
        // L̂_h: a continuation's input is the deferred position (D22, D24).
        let lh = if self.paged[0].lease_dfr(h.id) { len + 1 } else { len };
        let k = dv.len();
        proof {
            reveal(lease_ok);
            assert(lease_ok(self.pv(0), self.paged@[0].den_log(), h.id));
            assert(lh as nat == lhat(o.pv(0).leases[h.id]));
        }
        if n == 0 || n > lh - pf || k > cfg.lam || (k > 0 && pf + n != lh) || (propose && (cfg.ntarget >= self.npaged
            || pf + n != lh)) || (ddr && pf + n <= len) {
            return Err(Error::InvalidArgument);
        }
        // Deferred drafts come from the producer's proposal forward (D24).
        if ddr && k > 0 {
            proof {
                reveal(lease_ok);
                assert(o.pv(0).leases[h.id].dfr);
                assert(q == 1);
                assert(o.pv(0).pend.contains_key(o.pv(0).leases[h.id].pending[0]));
            }
            let t0 = self.paged[0].queue_head(h.id);
            if !self.paged[0].pend_propose(t0) {
                return Err(Error::InvalidArgument);
            }
        }
        let ghost a: usize = pf;
        let tid = self.paged[0].next_ticket_exec();
        if tid == u64::MAX {
            return Err(Error::IdentifierExhausted);
        }
        // A continuation's producer is the head of the queue, whose bonus token is its input (D24).
        let producer = if pf + n > len {
            proof {
                assert(o.pv(0).leases[h.id].dfr);
                assert(o.pv(0).leases[h.id].pending.len() > 0);
            }
            Some(Ticket { mgr: self.id, id: self.paged[0].queue_head(h.id) })
        } else {
            None
        };
        let slack = self.paged[0].queue_slack(h.id);
        let mut wslots: Vec<Vec<usize>> = Vec::new();
        let mut ptabs: Vec<Vec<PageId>> = Vec::new();
        let mut input_ids: Vec<Token> = Vec::new();
        let mut positions: Vec<usize> = Vec::new();
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                o.valid(),
                ov == o@,
                ov.paged[0] == o.pv(0),
                o.pv(0).leases.contains_key(h.id),
                q as nat == o.pv(0).leases[h.id].pending.len(),
                q as nat <= o.pv(0).cfg.delta,
                q > 0 && !ddr ==> k == 0,
                ddr ==> a + n > len,
                a as nat == pfront(o.pv(0), o.pv(0).leases[h.id]),
                o.pv(0).leases[h.id].toks.len() == len,
                lh as nat == lhat(o.pv(0).leases[h.id]),
                slack as nat == sdr(o.pv(0), o.pv(0).leases[h.id]),
                producer == if a + n > len { Some(Ticket { mgr: o.id, id: o.pv(0).leases[h.id].pending[0] }) } else { None::<Ticket> },
                0 < n <= lh - a,
                k == dv@.len(),
                k as nat <= ov.lam(),
                k > 0 ==> a + n == lh,
                propose ==> ov.ntarget() < ov.np && a + n == lh,
                cfg@ == ov.paged[0].cfg,
                tid == o.pv(0).next_ticket,
                tid < u64::MAX,
                h.mgr == o.id,
                self.npaged == o.npaged,
                self.paged@.len() == o.paged@.len(),
                self.state@ == o.state@,
                self.slots@ == o.slots@,
                self.id == o.id,
                self.nslab == o.nslab,
                self.sbytes == o.sbytes,
                self.b == o.b,
                self.unit@ == o.unit@,
                self.per@ == o.per@,
                self.owner@ == o.owner@,
                self.fs == o.fs,
                c <= self.npaged,
                wslots@.len() == c,
                ptabs@.len() == c,
                c > 0 ==> input_ids@ == cinputs(o.pv(0).leases[h.id], a as nat, (a + n) as nat, dv@)
                    && positions@.len() == n + k && forall|q: int| 0 <= q < n + k ==> #[trigger] positions@[q] as int == a + q,
                forall|c2: int| c <= c2 < o.np() ==> #[trigger] self.paged@[c2] == o.paged@[c2],
                forall|c2: int|
                    0 <= c2 < c ==> {
                        let plan = ExecutionPlan {
                            ticket: Ticket { mgr: o.pv(c2).id, id: tid },
                            handle: Handle { mgr: o.pv(c2).id, id: h.id },
                            input_ids: input_ids,
                            positions: positions,
                            write_slots: wslots@[c2],
                            page_table: ptabs@[c2],
                            block_size: o.b,
                        };
                        &&& (#[trigger] self.paged@[c2]).valid()
                        &&& self.pv(c2) == began_d(o.pv(c2), h.id, n as nat, dv@, propose, ddr)
                        &&& plan_ok_d(o.pv(c2), h.id, n as nat, dv@, ov.ext_of(c2, propose), plan)
                        &&& forall|j: int|
                            0 <= j < o.pv(c2).leases[h.id].c ==> (o.pv(c2).vmap)(#[trigger] slot_of(
                                o.pv(c2).b,
                                o.pv(c2).leases[h.id].table,
                                j,
                            )) == o.pv(c2).leases[h.id].toks.subrange(0, j + 1)
                    },
            decreases self.npaged - c,
        {
            let ext: usize = if propose && c >= cfg.ntarget { cfg.lam } else { 0 };
            proof {
                assert(self.paged@[c as int] == o.paged@[c as int]);
                assert(o.paged@[c as int].valid());
                assert(o.paged@[0].valid());
                assert(o.pv(c as int).leases.contains_key(h.id));
                assert(o.pv(c as int).leases[h.id].toks == o.pv(0).leases[h.id].toks);
                assert(o.pv(c as int).leases[h.id].c == o.pv(0).leases[h.id].c);
                assert(o.pv(c as int).leases[h.id].pending == o.pv(0).leases[h.id].pending);
                assert(o.pv(c as int).leases[h.id].rho == o.pv(0).leases[h.id].rho);
                assert(o.pv(c as int).next_ticket == tid);
                assert(o.pv(c as int).cfg == o.pv(0).cfg);
                assert(o.pv(c as int).pend == o.pv(0).pend);
                assert(o.pv(c as int).leases[h.id].dfr == o.pv(0).leases[h.id].dfr);
                assert(pfront(o.pv(c as int), o.pv(c as int).leases[h.id]) == a);
                assert(cfg_rel(o.pv(0).cfg, o.np()));
                assert(ext as nat == ov.ext_of(c as int, propose));
                reveal(lease_ok);
                assert(lease_ok(o.pv(0), o.paged@[0].den_log(), h.id));
                // The reservation covers the slack, the drafts and the proposal rows (D18): with
                // input left, I16's room clause gives L̂ + s_h + μ <= ρ + δλ, and
                // μ − δλ = λ + λ·[Cx ≠ ∅] covers k and ext.
                assert(a < lh);
                let l0 = o.pv(0).leases[h.id];
                let cf = o.pv(0).cfg;
                assert(lh + sdr(o.pv(0), l0) + cf.mu <= l0.rho + dlam(cf));
                assert(cfg_room(cf));
                assert(cf.mu == dlam(cf) + cf.lam + (if cf.ntarget < o.np() { cf.lam } else { 0 }));
                if a + n < lh {
                    assert(k == 0 && ext == 0);
                } else {
                    assert(k + ext <= cf.mu - dlam(cf));
                }
                assert(a + sdr(o.pv(0), l0) + n + k + ext <= l0.rho);
                assert(sdr(o.pv(c as int), o.pv(c as int).leases[h.id]) == sdr(o.pv(0), l0));
                assert(lhat(o.pv(c as int).leases[h.id]) == lh);
                assert(begin_args_ok(o.pv(c as int), o.pv(c as int).leases[h.id], n as nat, k as nat, ext as nat, propose));
            }
            let mid_c = self.paged[c].mgr_id();
            let ghost p0 = self.paged@;
            let r = self.paged[c].begin_write_v(Handle { mgr: mid_c, id: h.id }, n, dv.as_slice(), ext, propose, ddr);
            proof {
                assert forall|c2: int| 0 <= c2 < p0.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
            }
            match r {
                Ok((_t, plan)) => {
                    let ghost wb = wslots@;
                    let ghost pb = ptabs@;
                    if c == 0 {
                        input_ids = vstd::slice::slice_to_vec(plan.input_ids.as_slice());
                        positions = vstd::slice::slice_to_vec(plan.positions.as_slice());
                    }
                    proof {
                        assert(plan.input_ids@ == cinputs(o.pv(c as int).leases[h.id], a as nat, (a + n) as nat, dv@));
                        assert(input_ids@ == plan.input_ids@);
                        assert(positions@ == plan.positions@);
                    }
                    wslots.push(plan.write_slots);
                    ptabs.push(plan.page_table);
                    proof {
                        assert forall|c2: int| 0 <= c2 < c + 1 implies {
                            let pl = ExecutionPlan {
                                ticket: Ticket { mgr: o.pv(c2).id, id: tid },
                                handle: Handle { mgr: o.pv(c2).id, id: h.id },
                                input_ids: input_ids,
                                positions: positions,
                                write_slots: wslots@[c2],
                                page_table: ptabs@[c2],
                                block_size: o.b,
                            };
                            &&& (#[trigger] self.paged@[c2]).valid()
                            &&& self.pv(c2) == began_d(o.pv(c2), h.id, n as nat, dv@, propose, ddr)
                            &&& plan_ok_d(o.pv(c2), h.id, n as nat, dv@, ov.ext_of(c2, propose), pl)
                            &&& forall|j: int|
                                0 <= j < o.pv(c2).leases[h.id].c ==> (o.pv(c2).vmap)(#[trigger] slot_of(
                                    o.pv(c2).b,
                                    o.pv(c2).leases[h.id].table,
                                    j,
                                )) == o.pv(c2).leases[h.id].toks.subrange(0, j + 1)
                        } by {
                            if c2 < c {
                                assert(self.paged@[c2] == p0[c2]);
                                assert(wslots@[c2] == wb[c2]);
                                assert(ptabs@[c2] == pb[c2]);
                            } else {
                                assert(o.pv(c2).b == o.b as nat);
                            }
                        }
                    }
                },
                Err(_) => {
                    proof {
                        assert(false);
                    }
                    return Err(Error::Busy);
                },
            }
            c += 1;
        }
        let sl = vstd::slice::slice_to_vec(self.slots.get(&h.id).unwrap().as_slice());
        let plan = CoordPlan {
            ticket: Ticket { mgr: self.id, id: tid },
            handle: h,
            input_ids,
            positions,
            block_size: self.b,
            lo: pf,
            slack,
            num_inputs: n,
            num_drafts: k,
            propose,
            write_slots: wslots,
            page_tables: ptabs,
            state_slots: sl,
            init: pf == 0,
            producer,
        };
        proof {
            Self::lemma_begin_post(&o, self, h.id, n as nat, dv@, propose, ddr, tid, &plan);
        }
        Ok((Ticket { mgr: self.id, id: tid }, plan))
    }

    proof fn lemma_begin_post(o: &Coordinator, fin: &Coordinator, h: u64, n: nat, d: Seq<Token>, propose: bool, ddr: bool, tid: u64, plan: &CoordPlan)
        requires
            o.valid(),
            o.pv(0).leases.contains_key(h),
            o.pv(0).leases[h].pending.len() <= o.pv(0).cfg.delta,
            tid == o.pv(0).next_ticket,
            tid < u64::MAX,
            0 < n,
            pfront(o.pv(0), o.pv(0).leases[h]) + n <= lhat(o.pv(0).leases[h]),
            fin.npaged == o.npaged,
            fin.paged@.len() == o.paged@.len(),
            fin.state@ == o.state@,
            fin.slots@ == o.slots@,
            fin.id == o.id,
            fin.nslab == o.nslab,
            fin.sbytes == o.sbytes,
            fin.b == o.b,
            fin.unit@ == o.unit@,
            fin.per@ == o.per@,
            fin.owner@ == o.owner@,
            fin.fs == o.fs,
            plan.ticket == (Ticket { mgr: o.id, id: tid }),
            plan.handle.id == h,
            plan.handle.mgr == o.id,
            plan.block_size == o.b,
            plan.lo as nat == pfront(o.pv(0), o.pv(0).leases[h]),
            plan.slack as nat == sdr(o.pv(0), o.pv(0).leases[h]),
            plan.num_inputs as nat == n,
            plan.num_drafts as nat == d.len(),
            plan.propose == propose,
            plan.state_slots@ == o.slots@[h]@,
            plan.init == (pfront(o.pv(0), o.pv(0).leases[h]) == 0),
            plan.write_slots@.len() == o.np(),
            plan.page_tables@.len() == o.np(),
            plan.input_ids@ == cinputs(o.pv(0).leases[h], pfront(o.pv(0), o.pv(0).leases[h]), pfront(o.pv(0), o.pv(0).leases[h]) + n, d),
            plan.producer == if pfront(o.pv(0), o.pv(0).leases[h]) + n > o.pv(0).leases[h].toks.len() {
                Some(Ticket { mgr: o.id, id: o.pv(0).leases[h].pending[0] })
            } else {
                None::<Ticket>
            },
            plan.positions@.len() == n + d.len(),
            forall|q: int| 0 <= q < n + d.len() ==> #[trigger] plan.positions@[q] as int == pfront(o.pv(0), o.pv(0).leases[h]) + q,
            forall|c2: int|
                0 <= c2 < o.np() ==> {
                    let pl = ExecutionPlan {
                        ticket: Ticket { mgr: o.pv(c2).id, id: tid },
                        handle: Handle { mgr: o.pv(c2).id, id: h },
                        input_ids: plan.input_ids,
                        positions: plan.positions,
                        write_slots: plan.write_slots@[c2],
                        page_table: plan.page_tables@[c2],
                        block_size: o.b,
                    };
                    &&& (#[trigger] fin.paged@[c2]).valid()
                    &&& fin.pv(c2) == began_d(o.pv(c2), h, n, d, propose, ddr)
                    &&& plan_ok_d(o.pv(c2), h, n, d, o@.ext_of(c2, propose), pl)
                    &&& forall|j: int|
                        0 <= j < o.pv(c2).leases[h].c ==> (o.pv(c2).vmap)(#[trigger] slot_of(
                            o.pv(c2).b,
                            o.pv(c2).leases[h].table,
                            j,
                        )) == o.pv(c2).leases[h].toks.subrange(0, j + 1)
                },
        ensures
            fin.valid(),
            coord_begun(o@, fin@, h, n, d, propose, ddr, *plan),
    {
        assert forall|c: int| 0 <= c < o.np() implies {
            &&& (#[trigger] fin.paged@[c]).valid()
            &&& fin.pv(c).own == o.pv(c).own
            &&& fin.pv(c).p == o.pv(c).p
            &&& fin.pv(c).b == o.pv(c).b
            &&& fin.pv(c).ns == o.pv(c).ns
            &&& fin.pv(c).cfg == o.pv(c).cfg
            &&& fin.pv(c).next_handle == o.pv(c).next_handle
            &&& fin.pv(c).leases.dom() == o.pv(c).leases.dom()
            &&& forall|h2: u64| #[trigger] o.pv(c).leases.contains_key(h2) && h2 != h ==> fin.pv(c).leases[h2] == o.pv(c).leases[h2]
            &&& fin.pv(c).leases[h].toks == fin.pv(0).leases[h].toks
            &&& fin.pv(c).leases[h].rho == o.pv(c).leases[h].rho
            &&& fin.pv(c).leases[h].c == fin.pv(0).leases[h].c
            &&& fin.pv(c).leases[h].pending == fin.pv(0).leases[h].pending
            &&& fin.pv(c).leases[h].rho == fin.pv(0).leases[h].rho
            &&& fin.pv(c).leases[h].dfr == fin.pv(0).leases[h].dfr
            &&& fin.pv(c).pend == fin.pv(0).pend
            &&& fin.pv(c).next_ticket == fin.pv(0).next_ticket
        } by {
            assert(o.paged@[c].valid());
            assert(o.pv(c).leases.contains_key(h));
            assert(o.pv(c).leases[h].toks == o.pv(0).leases[h].toks);
            assert(o.pv(c).leases[h].c == o.pv(0).leases[h].c);
            assert(o.pv(c).leases[h].rho == o.pv(0).leases[h].rho);
            assert(o.pv(c).leases[h].pending == o.pv(0).leases[h].pending);
            assert(o.pv(c).pend == o.pv(0).pend);
            assert(pfront(o.pv(c), o.pv(c).leases[h]) == pfront(o.pv(0), o.pv(0).leases[h]));
            assert(o.pv(c).next_ticket == o.pv(0).next_ticket);
            assert(fin.pv(c).leases.dom() =~= o.pv(c).leases.dom());
            assert(fin.pv(0).leases.dom() =~= o.pv(0).leases.dom());
            assert(fin.paged@[0].valid());
        }
        assert forall|j: int| 0 <= j < o.nst() implies {
            &&& (#[trigger] fin.state@[j]).valid()
            &&& fin.sv(j).own == o.sv(j).own
            &&& fin.sv(j).holder == o.sv(j).holder
            &&& fin.sv(j).p == o.sv(j).p
            &&& forall|x: int| 0 <= x < o.sv(j).p && x != o.slots@[h]@[j] ==> #[trigger] fin.sv(j).w[x] == o.sv(j).w[x]
            &&& (fin.pv(0).leases[h].c > 0 ==> fin.sv(j).w[o.slots@[h]@[j] as int] == Some(
                fin.pv(0).leases[h].toks.subrange(0, fin.pv(0).leases[h].c as int),
            ))
        } by {
            assert(o.state@[j].valid());
            assert(fin.paged@[0].valid());
            assert(o.slots@.contains_key(h));
        }
        fin.lemma_step_valid(o, h);
        o.lemma_view();
        fin.lemma_view();
        let ov = o@;
        let l = ov.leases()[h];
        assert(ov.paged[0] == o.pv(0));
        assert forall|c2: int| 0 <= c2 < ov.np implies #[trigger] cplan_class(ov, h, n, d, propose, *plan, c2) by {
            assert(ov.paged[c2] == o.pv(c2));
            assert(o.pv(c2).leases[h].pending == o.pv(0).leases[h].pending);
            assert(o.pv(c2).pend == o.pv(0).pend);
            assert(o.paged@[c2].valid());
            assert(o.pv(c2).b == o.b as nat);
            assert(o.pv(c2).leases.contains_key(h));
            assert(o.pv(c2).leases[h].toks == o.pv(0).leases[h].toks);
            assert(o.pv(c2).leases[h].c == o.pv(0).leases[h].c);
            let pl = ExecutionPlan {
                ticket: Ticket { mgr: o.pv(c2).id, id: tid },
                handle: Handle { mgr: o.pv(c2).id, id: h },
                input_ids: plan.input_ids,
                positions: plan.positions,
                write_slots: plan.write_slots@[c2],
                page_table: plan.page_tables@[c2],
                block_size: o.b,
            };
            assert(fin.paged@[c2].valid());
            assert(plan_ok_d(o.pv(c2), h, n, d, ov.ext_of(c2, propose), pl));
            assert(pl.write_slots@ == plan.write_slots@[c2]@);
            assert(pl.page_table@ == plan.page_tables@[c2]@);
        }
        assert forall|j: int| 0 <= j < ov.nst() implies {
            &&& ov.state[j].holder[(#[trigger] plan.state_slots@[j]) as int] == Some(h)
            &&& l.c > 0 ==> ov.state[j].w[plan.state_slots@[j] as int] == Some(l.toks.subrange(0, l.c as int))
        } by {
            assert(o.slots@.contains_key(h));
            assert(ov.state[j] == o.sv(j));
        }
        assert(plan.state_slots@ == ov.slots[h]);
        assert(ov.next_ticket() == tid);
        assert(ov.id == o.id);
        assert(ov.b == o.b as nat);
        assert(ov.leases()[h] == o.pv(0).leases[h]);
        assert(cplan_ok(ov, h, n, d, propose, *plan));
        assert forall|c: int| 0 <= c < ov.np implies #[trigger] fin@.paged[c] == began_d(ov.paged[c], h, n, d, propose, ddr) by {}
        assert(fin@.state =~= ov.state);
        assert(fin@.slots =~= ov.slots);
    }
}


impl Coordinator {
    /// C4. `finish_write(ticket, completion)`: commits the first `accepted` drafts in every paged
    /// class (D17), then consumes the ticket, publishes new blocks over `T_h ++ D[0:n]`, and records
    /// the state after `T'_h[0:z+n]` in every live state slot (D19).
    pub fn finish_write(&mut self, t: Ticket, completion: CoordCompletion) -> (r: Result<usize, Error>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            coord_finish_result(old(self)@, final(self)@, t, completion, r),
    {
        let ghost o = *self;
        let ghost ov = o@;
        proof {
            o.lemma_view();
            assert(self.paged@[0].valid());
        }
        if t.mgr != self.id || completion.ticket.mgr != t.mgr || completion.ticket.id != t.id {
            return Err(Error::InvalidTicket);
        }
        if self.paged[0].pend_info(t.id).is_none() || !self.paged[0].is_head(t.id) {
            return Err(Error::InvalidTicket);
        }
        let k = self.paged[0].pend_drafts_len(t.id);
        // `stop` (D25) is not yet supported.
        if completion.accepted > k || completion.stop {
            return Err(Error::InvalidArgument);
        }
        let dfr = self.paged[0].ticket_dfr(t.id);
        // A ticket heading X_h must report its token (D22).
        if dfr && completion.token.is_none() {
            return Err(Error::InvalidArgument);
        }
        // A continuation's deferred drafts are known only from its completion (D24).
        let dk = self.paged[0].pend_ddr(t.id) && k > 0;
        if dk && completion.drafts.len() != completion.accepted {
            return Err(Error::InvalidArgument);
        }
        let xs: Vec<Token> = if dk {
            vstd::slice::slice_to_vec(completion.drafts.as_slice())
        } else {
            self.paged[0].pend_drafts_prefix(t.id, completion.accepted)
        };
        proof {
            assert(self.paged@[0].valid());
            lemma_finish_facts(self.pv(0), self.paged@[0].den_log(), t.id);
        }
        // Commit the accepted drafts in every class, then the deferred token after them.
        self.commit_all(t.id, xs.as_slice());
        if dfr {
            let x = match completion.token {
                Some(x) => x,
                None => {
                    proof {
                        assert(false);
                    }
                    return Err(Error::InvalidArgument);
                },
            };
            self.bind_all(t.id, x);
        }
        let z = self.finish_core(t);
        proof {
            assert(completion.ticket == t);
        }
        Ok(z)
    }

    /// D22 in every paged class: bind the deferred token `x` of the lease of head ticket `t`.
    fn bind_all(&mut self, t: u64, x: Token)
        requires
            old(self).valid(),
            old(self).pv(0).pend.contains_key(t),
            old(self).pv(0).leases[old(self).pv(0).pend[t].lease].pending[0] == t,
            old(self).pv(0).leases.contains_key(old(self).pv(0).pend[t].lease),
            old(self).pv(0).leases[old(self).pv(0).pend[t].lease].dfr,
            old(self).pv(0).pend[t].drafts.len() == 0,
        ensures
            final(self).valid(),
            final(self)@ == coord_bound(old(self)@, old(self).pv(0).pend[t].lease, x),
            final(self).pv(0).pend == old(self).pv(0).pend,
            final(self).pv(0).leases[final(self).pv(0).pend[t].lease].pending[0] == t,
            !final(self).pv(0).leases[final(self).pv(0).pend[t].lease].dfr,
            final(self).id == old(self).id,
    {
        let ghost o = *self;
        let ghost h = o.pv(0).pend[t].lease;
        proof {
            o.lemma_view();
            assert(self.paged@[0].valid());
        }
        let hid = match self.paged[0].pend_info(t) {
            Some((hh, _, _)) => hh,
            None => {
                proof {
                    assert(false);
                }
                return;
            },
        };
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                o.valid(),
                o.pv(0).pend.contains_key(t),
                h == o.pv(0).pend[t].lease,
                hid == h,
                o.pv(0).leases.contains_key(h),
                o.pv(0).leases[h].dfr,
                o.pv(0).leases[h].pending[0] == t,
                o.pv(0).pend[t].drafts.len() == 0,
                self.npaged == o.npaged,
                self.paged@.len() == o.paged@.len(),
                self.state@ == o.state@,
                self.slots@ == o.slots@,
                self.id == o.id,
                self.nslab == o.nslab,
                self.sbytes == o.sbytes,
                self.b == o.b,
                self.unit@ == o.unit@,
                self.per@ == o.per@,
                self.owner@ == o.owner@,
                self.fs == o.fs,
                c <= self.npaged,
                forall|c2: int| c <= c2 < o.np() ==> #[trigger] self.paged@[c2] == o.paged@[c2],
                forall|c2: int| 0 <= c2 < c ==> (#[trigger] self.paged@[c2]).valid() && self.pv(c2) == bound(o.pv(c2), h, x),
            decreases self.npaged - c,
        {
            proof {
                assert(self.paged@[c as int] == o.paged@[c as int]);
                assert(o.paged@[c as int].valid());
                assert(o.paged@[0].valid());
                assert(o.pv(c as int).leases.contains_key(h));
                assert(o.pv(c as int).leases[h].dfr == o.pv(0).leases[h].dfr);
                assert(o.pv(c as int).leases[h].pending == o.pv(0).leases[h].pending);
                assert(o.pv(c as int).pend == o.pv(0).pend);
            }
            let ghost p0 = self.paged@;
            self.paged[c].bind_deferred(hid, x);
            proof {
                assert forall|c2: int| 0 <= c2 < p0.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
                assert forall|c2: int| 0 <= c2 < c + 1 implies (#[trigger] self.paged@[c2]).valid() && self.pv(c2) == bound(
                    o.pv(c2),
                    h,
                    x,
                ) by {
                    if c2 < c {
                        assert(self.paged@[c2] == p0[c2]);
                    }
                }
            }
            c += 1;
        }
        proof {
            Self::lemma_bind_post(&o, self, t, h, x);
        }
    }

    proof fn lemma_bind_post(o: &Coordinator, fin: &Coordinator, t: u64, h: u64, x: Token)
        requires
            o.valid(),
            o.pv(0).pend.contains_key(t),
            h == o.pv(0).pend[t].lease,
            o.pv(0).leases.contains_key(h),
            o.pv(0).leases[h].dfr,
            fin.npaged == o.npaged,
            fin.paged@.len() == o.paged@.len(),
            fin.state@ == o.state@,
            fin.slots@ == o.slots@,
            fin.id == o.id,
            fin.nslab == o.nslab,
            fin.sbytes == o.sbytes,
            fin.b == o.b,
            fin.unit@ == o.unit@,
            fin.per@ == o.per@,
            fin.owner@ == o.owner@,
            fin.fs == o.fs,
            forall|c2: int| 0 <= c2 < o.np() ==> (#[trigger] fin.paged@[c2]).valid() && fin.pv(c2) == bound(o.pv(c2), h, x),
        ensures
            fin.valid(),
            fin@ == coord_bound(o@, h, x),
            fin.pv(0).pend == o.pv(0).pend,
            fin.pv(0).leases[h].pending == o.pv(0).leases[h].pending,
            !fin.pv(0).leases[h].dfr,
    {
        assert(o.paged@[0].valid());
        assert forall|c: int| 0 <= c < o.np() implies {
            &&& (#[trigger] fin.paged@[c]).valid()
            &&& fin.pv(c).own == o.pv(c).own
            &&& fin.pv(c).p == o.pv(c).p
            &&& fin.pv(c).b == o.pv(c).b
            &&& fin.pv(c).ns == o.pv(c).ns
            &&& fin.pv(c).cfg == o.pv(c).cfg
            &&& fin.pv(c).next_handle == o.pv(c).next_handle
            &&& fin.pv(c).leases.dom() == o.pv(c).leases.dom()
            &&& forall|h2: u64| #[trigger] o.pv(c).leases.contains_key(h2) && h2 != h ==> fin.pv(c).leases[h2] == o.pv(c).leases[h2]
            &&& fin.pv(c).leases[h].toks == fin.pv(0).leases[h].toks
            &&& fin.pv(c).leases[h].rho == o.pv(c).leases[h].rho
            &&& fin.pv(c).leases[h].c == fin.pv(0).leases[h].c
            &&& fin.pv(c).leases[h].pending == fin.pv(0).leases[h].pending
            &&& fin.pv(c).leases[h].rho == fin.pv(0).leases[h].rho
            &&& fin.pv(c).leases[h].dfr == fin.pv(0).leases[h].dfr
            &&& fin.pv(c).pend == fin.pv(0).pend
            &&& fin.pv(c).next_ticket == fin.pv(0).next_ticket
        } by {
            assert(o.paged@[c].valid());
            assert(o.pv(c).pend == o.pv(0).pend);
            assert(o.pv(c).next_ticket == o.pv(0).next_ticket);
            assert(o.pv(c).leases.contains_key(h));
            assert(o.pv(c).leases[h].toks == o.pv(0).leases[h].toks);
            assert(o.pv(c).leases[h].c == o.pv(0).leases[h].c);
            assert(o.pv(c).leases[h].rho == o.pv(0).leases[h].rho);
            assert(o.pv(c).leases[h].pending == o.pv(0).leases[h].pending);
            assert(fin.paged@[0].valid());
            assert(fin.pv(c).leases.dom() =~= o.pv(c).leases.dom());
            assert(fin.pv(0).leases.dom() =~= o.pv(0).leases.dom());
        }
        let l0 = o.pv(0).leases[h];
        reveal(lease_ok);
        assert(lease_ok(o.pv(0), o.paged@[0].den_log(), h));
        assert(fin.pv(0).leases[h].toks.subrange(0, l0.c as int) =~= l0.toks.subrange(0, l0.c as int));
        assert forall|j: int| 0 <= j < o.nst() implies {
            &&& (#[trigger] fin.state@[j]).valid()
            &&& fin.sv(j).own == o.sv(j).own
            &&& fin.sv(j).holder == o.sv(j).holder
            &&& fin.sv(j).p == o.sv(j).p
            &&& forall|x2: int| 0 <= x2 < o.sv(j).p && x2 != o.slots@[h]@[j] ==> #[trigger] fin.sv(j).w[x2] == o.sv(j).w[x2]
            &&& (fin.pv(0).leases[h].c > 0 ==> fin.sv(j).w[o.slots@[h]@[j] as int] == Some(
                fin.pv(0).leases[h].toks.subrange(0, fin.pv(0).leases[h].c as int),
            ))
        } by {
            assert(o.state@[j].valid());
            assert(fin.paged@[0].valid());
            assert(o.slots@.contains_key(h));
        }
        fin.lemma_step_valid(o, h);
        o.lemma_view();
        fin.lemma_view();
        assert(fin@.paged =~= coord_bound(o@, h, x).paged);
        assert(fin@.state =~= o@.state);
        assert(fin@.slots =~= o@.slots);
        assert(fin@ == coord_bound(o@, h, x));
    }

    /// D17, D24 in every paged class: commit the accepted drafts `xs` of `t`.
    fn commit_all(&mut self, t: u64, xs: &[Token])
        requires
            old(self).valid(),
            old(self).pv(0).pend.contains_key(t),
            old(self).pv(0).leases[old(self).pv(0).pend[t].lease].pending[0] == t,
            xs@.len() <= old(self).pv(0).pend[t].drafts.len(),
        ensures
            final(self).valid(),
            final(self)@ == coord_committed_t(old(self)@, t, xs@),
            final(self).pv(0).pend.contains_key(t),
            final(self).pv(0).pend[t].lease == old(self).pv(0).pend[t].lease,
            final(self).pv(0).leases.contains_key(final(self).pv(0).pend[t].lease),
            final(self).pv(0).leases[final(self).pv(0).pend[t].lease].pending[0] == t,
            final(self).pv(0).leases[final(self).pv(0).pend[t].lease].dfr == old(self).pv(0).leases[old(self).pv(0).pend[t].lease].dfr,
            final(self).pv(0).pend[t].drafts.len() == 0,
            final(self).id == old(self).id,
    {
        let ghost o = *self;
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                o.valid(),
                o.pv(0).pend.contains_key(t),
                o.pv(0).leases[o.pv(0).pend[t].lease].pending[0] == t,
                xs@.len() <= o.pv(0).pend[t].drafts.len(),
                self.npaged == o.npaged,
                self.paged@.len() == o.paged@.len(),
                self.state@ == o.state@,
                self.slots@ == o.slots@,
                self.id == o.id,
                self.nslab == o.nslab,
                self.sbytes == o.sbytes,
                self.b == o.b,
                self.unit@ == o.unit@,
                self.per@ == o.per@,
                self.owner@ == o.owner@,
                self.fs == o.fs,
                c <= self.npaged,
                forall|c2: int| c <= c2 < o.np() ==> #[trigger] self.paged@[c2] == o.paged@[c2],
                forall|c2: int| 0 <= c2 < c ==> (#[trigger] self.paged@[c2]).valid() && self.pv(c2) == committed_t(o.pv(c2), t, xs@),
            decreases self.npaged - c,
        {
            proof {
                assert(self.paged@[c as int] == o.paged@[c as int]);
                assert(o.paged@[c as int].valid());
                assert(o.pv(c as int).pend == o.pv(0).pend);
                assert(o.paged@[0].valid());
                lemma_finish_facts(o.pv(0), o.paged@[0].den_log(), t);
                assert(o.pv(c as int).leases.contains_key(o.pv(0).pend[t].lease));
                assert(o.pv(c as int).leases[o.pv(0).pend[t].lease].pending == o.pv(0).leases[o.pv(0).pend[t].lease].pending);
                assert(o.pv(c as int).leases[o.pv(0).pend[t].lease].dfr == o.pv(0).leases[o.pv(0).pend[t].lease].dfr);
            }
            let ghost p0 = self.paged@;
            self.paged[c].commit_toks(t, xs);
            proof {
                assert forall|c2: int| 0 <= c2 < p0.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
                assert forall|c2: int| 0 <= c2 < c + 1 implies (#[trigger] self.paged@[c2]).valid() && self.pv(c2) == committed_t(
                    o.pv(c2),
                    t,
                    xs@,
                ) by {
                    if c2 < c {
                        assert(self.paged@[c2] == p0[c2]);
                    }
                }
            }
            c += 1;
        }
        proof {
            Self::lemma_commit_post(&o, self, t, xs@);
        }
    }

    proof fn lemma_commit_post(o: &Coordinator, fin: &Coordinator, t: u64, xs: Seq<Token>)
        requires
            o.valid(),
            o.pv(0).pend.contains_key(t),
            o.pv(0).leases[o.pv(0).pend[t].lease].pending[0] == t,
            xs.len() <= o.pv(0).pend[t].drafts.len(),
            fin.npaged == o.npaged,
            fin.paged@.len() == o.paged@.len(),
            fin.state@ == o.state@,
            fin.slots@ == o.slots@,
            fin.id == o.id,
            fin.nslab == o.nslab,
            fin.sbytes == o.sbytes,
            fin.b == o.b,
            fin.unit@ == o.unit@,
            fin.per@ == o.per@,
            fin.owner@ == o.owner@,
            fin.fs == o.fs,
            forall|c2: int| 0 <= c2 < o.np() ==> (#[trigger] fin.paged@[c2]).valid() && fin.pv(c2) == committed_t(o.pv(c2), t, xs),
        ensures
            fin.valid(),
            fin@ == coord_committed_t(o@, t, xs),
            fin.pv(0).pend.contains_key(t),
            fin.pv(0).pend[t].lease == o.pv(0).pend[t].lease,
            fin.pv(0).leases.contains_key(fin.pv(0).pend[t].lease),
            fin.pv(0).leases[fin.pv(0).pend[t].lease].pending[0] == t,
            fin.pv(0).leases[fin.pv(0).pend[t].lease].dfr == o.pv(0).leases[o.pv(0).pend[t].lease].dfr,
            fin.pv(0).pend[t].drafts.len() == 0,
    {
        assert(o.paged@[0].valid());
        lemma_finish_facts(o.pv(0), o.paged@[0].den_log(), t);
        let h = o.pv(0).pend[t].lease;
        // The ticket behind the head is another ticket, so the head's record is the committed one.
        reveal(lease_ok);
        assert(lease_ok(o.pv(0), o.paged@[0].den_log(), h));
        if o.pv(0).leases[h].pending.len() == 2 {
            assert(o.pv(0).leases[h].pending[1] != t);
        }
        assert(fin.pv(0) == committed_t(o.pv(0), t, xs));
        assert(fin.pv(0).pend[t].drafts.len() == 0);
        assert forall|c: int| 0 <= c < o.np() implies {
            &&& (#[trigger] fin.paged@[c]).valid()
            &&& fin.pv(c).own == o.pv(c).own
            &&& fin.pv(c).p == o.pv(c).p
            &&& fin.pv(c).b == o.pv(c).b
            &&& fin.pv(c).ns == o.pv(c).ns
            &&& fin.pv(c).cfg == o.pv(c).cfg
            &&& fin.pv(c).next_handle == o.pv(c).next_handle
            &&& fin.pv(c).leases.dom() == o.pv(c).leases.dom()
            &&& forall|h2: u64| #[trigger] o.pv(c).leases.contains_key(h2) && h2 != h ==> fin.pv(c).leases[h2] == o.pv(c).leases[h2]
            &&& fin.pv(c).leases[h].toks == fin.pv(0).leases[h].toks
            &&& fin.pv(c).leases[h].rho == o.pv(c).leases[h].rho
            &&& fin.pv(c).leases[h].c == fin.pv(0).leases[h].c
            &&& fin.pv(c).leases[h].pending == fin.pv(0).leases[h].pending
            &&& fin.pv(c).leases[h].rho == fin.pv(0).leases[h].rho
            &&& fin.pv(c).leases[h].dfr == fin.pv(0).leases[h].dfr
            &&& fin.pv(c).pend == fin.pv(0).pend
            &&& fin.pv(c).next_ticket == fin.pv(0).next_ticket
        } by {
            assert(o.paged@[c].valid());
            assert(o.pv(c).pend == o.pv(0).pend);
            assert(o.pv(c).next_ticket == o.pv(0).next_ticket);
            assert(o.pv(c).leases.contains_key(h));
            assert(o.pv(c).leases[h].toks == o.pv(0).leases[h].toks);
            assert(o.pv(c).leases[h].c == o.pv(0).leases[h].c);
            assert(o.pv(c).leases[h].rho == o.pv(0).leases[h].rho);
            assert(fin.paged@[0].valid());
            assert(fin.pv(c).leases.dom() =~= o.pv(c).leases.dom());
            assert(fin.pv(0).leases.dom() =~= o.pv(0).leases.dom());
        }
        let l0 = o.pv(0).leases[h];
        assert(fin.pv(0).leases[h].toks.subrange(0, l0.c as int) =~= l0.toks.subrange(0, l0.c as int));
        assert forall|j: int| 0 <= j < o.nst() implies {
            &&& (#[trigger] fin.state@[j]).valid()
            &&& fin.sv(j).own == o.sv(j).own
            &&& fin.sv(j).holder == o.sv(j).holder
            &&& fin.sv(j).p == o.sv(j).p
            &&& forall|x: int| 0 <= x < o.sv(j).p && x != o.slots@[h]@[j] ==> #[trigger] fin.sv(j).w[x] == o.sv(j).w[x]
            &&& (fin.pv(0).leases[h].c > 0 ==> fin.sv(j).w[o.slots@[h]@[j] as int] == Some(
                fin.pv(0).leases[h].toks.subrange(0, fin.pv(0).leases[h].c as int),
            ))
        } by {
            assert(o.state@[j].valid());
            assert(fin.paged@[0].valid());
            assert(o.slots@.contains_key(h));
        }
        fin.lemma_step_valid(o, h);
        o.lemma_view();
        fin.lemma_view();
        assert(fin@.paged =~= coord_committed_t(o@, t, xs).paged);
        assert(fin@.state =~= o@.state);
        assert(fin@.slots =~= o@.slots);
        assert(fin@ == coord_committed_t(o@, t, xs));
    }

    /// The completion step of C4 (the unchanged v0.3 operation, on the committed state).
    fn finish_core(&mut self, t: Ticket) -> (z: usize)
        requires
            old(self).valid(),
            t.mgr == old(self).id,
            old(self).pv(0).pend.contains_key(t.id),
            old(self).pv(0).leases[old(self).pv(0).pend[t.id].lease].pending[0] == t.id,
            !old(self).pv(0).leases[old(self).pv(0).pend[t.id].lease].dfr,
        ensures
            final(self).valid(),
            coord_finished(old(self)@, final(self)@, t.id, z),
    {
        let ghost o = *self;
        let ghost ov = o@;
        proof {
            o.lemma_view();
            assert(self.paged@[0].valid());
        }
        let (hid, _a, z) = match self.paged[0].pend_info(t.id) {
            None => {
                proof {
                    assert(false);
                }
                return 0;
            },
            Some(x) => x,
        };
        proof {
            assert(self.paged@[0].valid());
            assert(inv(self.pv(0), self.paged@[0].den_log()));
            lemma_finish_facts(self.pv(0), self.paged@[0].den_log(), t.id);
        }
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                o.valid(),
                ov == o@,
                o.pv(0).pend.contains_key(t.id),
                o.pv(0).pend[t.id].lease == hid,
                o.pv(0).leases.contains_key(hid),
                o.pv(0).leases[hid].pending[0] == t.id,
                !o.pv(0).leases[hid].dfr,
                t.mgr == o.id,
                self.npaged == o.npaged,
                self.paged@.len() == o.paged@.len(),
                self.state@ == o.state@,
                self.slots@ == o.slots@,
                self.id == o.id,
                self.nslab == o.nslab,
                self.sbytes == o.sbytes,
                self.b == o.b,
                self.unit@ == o.unit@,
                self.per@ == o.per@,
                self.owner@ == o.owner@,
                self.fs == o.fs,
                c <= self.npaged,
                forall|c2: int| c <= c2 < o.np() ==> #[trigger] self.paged@[c2] == o.paged@[c2],
                forall|c2: int|
                    0 <= c2 < c ==> (#[trigger] self.paged@[c2]).valid() && finish_rel(o.pv(c2), self.pv(c2), t.id),
            decreases self.npaged - c,
        {
            proof {
                assert(self.paged@[c as int] == o.paged@[c as int]);
                assert(o.paged@[c as int].valid());
                assert(o.pv(c as int).pend == o.pv(0).pend);
                assert(o.pv(c as int).leases.contains_key(hid));
                assert(o.pv(c as int).leases[hid].pending == o.pv(0).leases[hid].pending);
                assert(o.pv(c as int).leases[hid].dfr == o.pv(0).leases[hid].dfr);
            }
            let mid_c = self.paged[c].mgr_id();
            let tc = Ticket { mgr: mid_c, id: t.id };
            let ghost p0 = self.paged@;
            let r = self.paged[c].finish_write(tc, Completion { ticket: tc });
            proof {
                assert forall|c2: int| 0 <= c2 < p0.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
            }
            match r {
                Ok(_) => {},
                Err(_) => {
                    proof {
                        assert(false);
                    }
                    return 0;
                },
            }
            proof {
                assert forall|c2: int| 0 <= c2 < c + 1 implies (#[trigger] self.paged@[c2]).valid() && finish_rel(
                    o.pv(c2),
                    self.pv(c2),
                    t.id,
                ) by {
                    if c2 < c {
                        assert(self.paged@[c2] == p0[c2]);
                    }
                }
            }
            c += 1;
        }
        // State classes: ghost provenance of each live slot becomes `T_h[0:z]`.
        let ghost tau = o.pv(0).leases[hid].toks.subrange(0, z as int);
        proof {
            assert(o.slots@.contains_key(hid)) by {
                assert(o.pv(0).leases.contains_key(hid));
            }
        }
        let sl = vstd::slice::slice_to_vec(self.slots.get(&hid).unwrap().as_slice());
        let ghost pg = self.paged@;
        let mut j: usize = 0;
        while j < self.state.len()
            invariant
                o.valid(),
                o.slots@.contains_key(hid),
                sl@ == o.slots@[hid]@,
                self.paged@ == pg,
                self.slots@ == o.slots@,
                self.state@.len() == o.state@.len(),
                j <= self.state@.len(),
                forall|j2: int| j <= j2 < o.nst() ==> #[trigger] self.state@[j2] == o.state@[j2],
                forall|j2: int|
                    0 <= j2 < j ==> (#[trigger] self.state@[j2]).valid() && self.sv(j2) == (StateV {
                        w: o.sv(j2).w.update(sl@[j2] as int, Some(tau)),
                        ..o.sv(j2)
                    }),
            decreases self.state@.len() - j,
        {
            proof {
                assert(self.state@[j as int] == o.state@[j as int]);
                assert(o.state@[j as int].valid());
                assert(o.slots@[hid]@.len() == o.nst());
            }
            let x = sl[j];
            let ghost s0 = self.state@;
            self.state[j].set_w(x, Ghost(tau));
            proof {
                assert forall|j2: int| 0 <= j2 < s0.len() && j2 != j implies #[trigger] self.state@[j2] == s0[j2] by {}
                assert forall|j2: int| 0 <= j2 < j + 1 implies (#[trigger] self.state@[j2]).valid() && self.sv(j2) == (StateV {
                    w: o.sv(j2).w.update(sl@[j2] as int, Some(tau)),
                    ..o.sv(j2)
                }) by {
                    if j2 < j {
                        assert(self.state@[j2] == s0[j2]);
                    }
                }
            }
            j += 1;
        }
        proof {
            Self::lemma_finish_post(&o, self, t.id, hid, z as nat, tau);
        }
        z
    }

    proof fn lemma_finish_post(o: &Coordinator, fin: &Coordinator, t: u64, h: u64, z: nat, tau: Seq<Token>)
        requires
            o.valid(),
            o.pv(0).pend.contains_key(t),
            o.pv(0).leases[o.pv(0).pend[t].lease].pending[0] == t,
            o.pv(0).pend[t].lease == h,
            o.pv(0).pend[t].z == z,
            tau == o.pv(0).leases[h].toks.subrange(0, z as int),
            o.slots@.contains_key(h),
            fin.npaged == o.npaged,
            fin.paged@.len() == o.paged@.len(),
            fin.slots@ == o.slots@,
            fin.id == o.id,
            fin.nslab == o.nslab,
            fin.sbytes == o.sbytes,
            fin.b == o.b,
            fin.unit@ == o.unit@,
            fin.per@ == o.per@,
            fin.owner@ == o.owner@,
            fin.fs == o.fs,
            fin.state@.len() == o.state@.len(),
            forall|c2: int| 0 <= c2 < o.np() ==> (#[trigger] fin.paged@[c2]).valid() && finish_rel(o.pv(c2), fin.pv(c2), t),
            forall|j2: int|
                0 <= j2 < o.nst() ==> (#[trigger] fin.state@[j2]).valid() && fin.sv(j2) == (StateV {
                    w: o.sv(j2).w.update(o.slots@[h]@[j2] as int, Some(tau)),
                    ..o.sv(j2)
                }),
        ensures
            fin.valid(),
            coord_finished(o@, fin@, t, z as usize),
    {
        assert(o.paged@[0].valid());
        lemma_finish_facts(o.pv(0), o.paged@[0].den_log(), t);
        assert forall|c: int| 0 <= c < o.np() implies {
            &&& (#[trigger] fin.paged@[c]).valid()
            &&& fin.pv(c).own == o.pv(c).own
            &&& fin.pv(c).p == o.pv(c).p
            &&& fin.pv(c).b == o.pv(c).b
            &&& fin.pv(c).ns == o.pv(c).ns
            &&& fin.pv(c).cfg == o.pv(c).cfg
            &&& fin.pv(c).next_handle == o.pv(c).next_handle
            &&& fin.pv(c).leases.dom() == o.pv(c).leases.dom()
            &&& forall|h2: u64| #[trigger] o.pv(c).leases.contains_key(h2) && h2 != h ==> fin.pv(c).leases[h2] == o.pv(c).leases[h2]
            &&& fin.pv(c).leases[h].toks == fin.pv(0).leases[h].toks
            &&& fin.pv(c).leases[h].rho == o.pv(c).leases[h].rho
            &&& fin.pv(c).leases[h].c == fin.pv(0).leases[h].c
            &&& fin.pv(c).leases[h].pending == fin.pv(0).leases[h].pending
            &&& fin.pv(c).leases[h].rho == fin.pv(0).leases[h].rho
            &&& fin.pv(c).leases[h].dfr == fin.pv(0).leases[h].dfr
            &&& fin.pv(c).pend == fin.pv(0).pend
            &&& fin.pv(c).next_ticket == fin.pv(0).next_ticket
        } by {
            assert(o.paged@[c].valid());
            assert(o.pv(c).pend == o.pv(0).pend);
            assert(o.pv(c).next_ticket == o.pv(0).next_ticket);
            assert(o.pv(c).leases.contains_key(h));
            assert(o.pv(c).leases[h].toks == o.pv(0).leases[h].toks);
            assert(fin.paged@[0].valid());
            assert(finish_rel(o.pv(0), fin.pv(0), t));
            assert(fin.pv(c).leases.dom() =~= o.pv(c).leases.dom());
        }
        assert(finish_rel(o.pv(0), fin.pv(0), t)) by {
            assert(fin.paged@[0].valid());
        }
        assert forall|j: int| 0 <= j < o.nst() implies {
            &&& (#[trigger] fin.state@[j]).valid()
            &&& fin.sv(j).own == o.sv(j).own
            &&& fin.sv(j).holder == o.sv(j).holder
            &&& fin.sv(j).p == o.sv(j).p
            &&& forall|x: int| 0 <= x < o.sv(j).p && x != o.slots@[h]@[j] ==> #[trigger] fin.sv(j).w[x] == o.sv(j).w[x]
            &&& (fin.pv(0).leases[h].c > 0 ==> fin.sv(j).w[o.slots@[h]@[j] as int] == Some(
                fin.pv(0).leases[h].toks.subrange(0, fin.pv(0).leases[h].c as int),
            ))
        } by {
            assert(fin.state@[j].valid());
            assert(o.slots@[h]@.len() == o.nst());
            assert((o.slots@[h]@[j] as nat) < o.sv(j).p);
        }
        fin.lemma_step_valid(o, h);
        o.lemma_view();
        fin.lemma_view();
        assert(fin@.slots =~= o@.slots);
        assert forall|c: int| 0 <= c < o@.np implies #[trigger] finish_rel(o@.paged[c], fin@.paged[c], t) by {
            assert(fin.paged@[c].valid());
        }
        assert forall|j: int| 0 <= j < o@.nst() implies #[trigger] fin@.state[j] == (StateV {
            w: o@.state[j].w.update(o@.slots[h][j] as int, Some(o@.leases()[h].toks.subrange(0, o@.pend()[t].z as int))),
            ..o@.state[j]
        }) by {
            assert(fin.state@[j].valid());
        }
    }
}


/// Read-only view of a lease (C6).
pub struct CoordRequestView {
    pub len: usize,
    pub computed: usize,
    /// `ρ_h`: the reach the page tables cover (D18).
    pub reach: usize,
    pub pending: Option<Ticket>,
    /// `X_h` is non-empty: position `L_h` is deferred, so `L̂_h = L_h + 1` (D22).
    pub deferred: bool,
    /// `p_h`: the planned frontier, and `s_h`: the drafts of the pending tickets (§3.2).
    pub planned: usize,
    pub slack: usize,
    pub block_size: usize,
    /// This instance's `λ`, `μ` and `δ` (C6).
    pub lam: usize,
    pub mu: usize,
    pub delta: usize,
    pub lease: LeaseView,
}

/// Read-only view of the arena (C7).
pub struct ArenaView {
    /// `owner[s]`: 0 is free, `c + 1` is class `c`.
    pub owner: Vec<usize>,
    /// `|F_c|` per class.
    pub free_units: Vec<usize>,
    /// `|R_c|` (with `Prot = ∅`) per class.
    pub reclaimable: Vec<usize>,
}

impl Coordinator {
    /// C6. `inspect(h)`.
    pub fn inspect(&self, h: Handle) -> (r: Result<CoordRequestView, Error>)
        requires
            self.inv(),
        ensures
            r is Err <==> !(h.mgr == self@.id && self@.leases().contains_key(h.id)),
            r is Err ==> r == Err::<CoordRequestView, Error>(Error::InvalidHandle),
            r matches Ok(v) ==> {
                let l = self@.leases()[h.id];
                &&& v.len as nat == l.toks.len()
                &&& v.computed as nat == l.c
                &&& v.reach as nat == l.rho
                &&& v.deferred == l.dfr
                &&& v.planned as nat == pfront(self@.paged[0], l)
                &&& v.slack as nat == sdr(self@.paged[0], l)
                &&& v.block_size as nat == self@.b
                &&& v.lam as nat == self@.lam()
                &&& v.mu as nat == self@.mu()
                &&& v.delta as nat == self@.delta()
                &&& (v.pending is Some) == (l.pending.len() > 0)
                &&& v.pending matches Some(t) ==> t.mgr == self@.id && t.id == l.pending[0]
                &&& v.lease.tables@.len() == self@.np
                &&& forall|c: int| 0 <= c < self@.np ==> (#[trigger] v.lease.tables@[c])@ == self@.paged[c].leases[h.id].table
                &&& v.lease.slots@ == self@.slots[h.id]
            },
    {
        if self.lease_live(h).is_none() {
            return Err(Error::InvalidHandle);
        }
        proof {
            self.lemma_view();
        }
        let mut tables: Vec<Vec<PageId>> = Vec::new();
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                self.valid(),
                h.mgr == self.id,
                self.pv(0).leases.contains_key(h.id),
                c <= self.npaged,
                tables@.len() == c,
                forall|c2: int| 0 <= c2 < c ==> (#[trigger] tables@[c2])@ == self.pv(c2).leases[h.id].table,
            decreases self.npaged - c,
        {
            proof {
                assert(self.paged@[c as int].valid());
                assert(self.pv(c as int).leases.contains_key(h.id));
            }
            let mid_c = self.paged[c].mgr_id();
            let rv = self.paged[c].inspect(Handle { mgr: mid_c, id: h.id });
            match rv {
                Ok(v) => {
                    let ghost tb = tables@;
                    tables.push(v.pages);
                    proof {
                        assert forall|c2: int| 0 <= c2 < c + 1 implies (#[trigger] tables@[c2])@ == self.pv(c2).leases[h.id].table by {
                            if c2 < c {
                                assert(tables@[c2] == tb[c2]);
                            }
                        }
                    }
                },
                Err(_) => {
                    proof {
                        assert(false);
                    }
                    return Err(Error::InvalidHandle);
                },
            }
            c += 1;
        }
        proof {
            assert(self.paged@[0].valid());
        }
        let r0 = self.paged[0].inspect(Handle { mgr: self.paged[0].mgr_id(), id: h.id });
        let rv0 = match r0 {
            Ok(v) => v,
            Err(_) => {
                proof {
                    assert(false);
                }
                return Err(Error::InvalidHandle);
            },
        };
        proof {
            assert(self.slots@.contains_key(h.id));
        }
        let slots = vstd::slice::slice_to_vec(self.slots.get(&h.id).unwrap().as_slice());
        let pending = match rv0.pending {
            Some(t) => Some(Ticket { mgr: self.id, id: t.id }),
            None => None,
        };
        let reach = self.paged[0].lease_rho(h.id);
        let deferred = self.paged[0].lease_dfr(h.id);
        let (_q, planned) = self.paged[0].queue_info(h.id);
        let slack = self.paged[0].queue_slack(h.id);
        let cfg = self.cfg_exec();
        Ok(CoordRequestView {
            len: rv0.len,
            computed: rv0.computed,
            reach,
            pending,
            deferred,
            planned,
            slack,
            block_size: self.b,
            lam: cfg.lam,
            mu: cfg.mu,
            delta: cfg.delta,
            lease: LeaseView { tables, slots },
        })
    }

    /// C6 `slot_of(c, h, j)`: the token-slot index of position `j` in paged class `c`.
    pub fn slot_of(&self, c: usize, h: Handle, j: usize) -> (r: Result<usize, Error>)
        requires
            self.inv(),
        ensures
            !(h.mgr == self@.id && self@.leases().contains_key(h.id) && (c as nat) < self@.np) ==> r is Err,
            (h.mgr == self@.id && self@.leases().contains_key(h.id) && (c as nat) < self@.np) ==> {
                let l = self@.paged[c as int].leases[h.id];
                &&& (j as nat) < l.rho ==> r == Ok::<usize, Error>(slot_of(self@.b, l.table, j as int) as usize)
                    && slot_of(self@.b, l.table, j as int) < self@.paged[c as int].p * self@.b
                &&& (j as nat) >= l.rho ==> r == Err::<usize, Error>(Error::InvalidArgument)
            },
    {
        if self.lease_live(h).is_none() || c >= self.npaged {
            return Err(Error::InvalidHandle);
        }
        proof {
            self.lemma_view();
            assert(self.paged@[c as int].valid());
            assert(self.pv(c as int).leases.contains_key(h.id));
        }
        let mid_c = self.paged[c].mgr_id();
        self.paged[c].slot_of(Handle { mgr: mid_c, id: h.id }, j)
    }

    /// C7. `arena()`: slab owners, free units and reclaimable slabs per class.
    pub fn arena(&self) -> (r: ArenaView)
        requires
            self.inv(),
        ensures
            r.owner@ == self@.owner,
            r.free_units@.len() == self@.ncls(),
            r.reclaimable@.len() == self@.ncls(),
            forall|c: int| 0 <= c < self@.ncls() ==> #[trigger] r.free_units@[c] as nat == self@.cfree(c),
            forall|c: int| 0 <= c < self@.ncls() ==> #[trigger] r.reclaimable@[c] as nat == self@.rcount(c, no_prot(self@)),
    {
        proof {
            self.lemma_view();
        }
        let prot: Vec<bool> = vec![false; self.nslab];
        proof {
            assert(prot@ =~= no_prot(self@));
        }
        let mut fu: Vec<usize> = Vec::new();
        let mut rc: Vec<usize> = Vec::new();
        let k = self.unit.len();
        let mut c: usize = 0;
        while c < k
            invariant
                self.valid(),
                k as nat == self.ncls(),
                self@.ncls() == self.ncls(),
                prot@ == no_prot(self@),
                prot@.len() == self.nslab,
                c <= k,
                fu@.len() == c,
                rc@.len() == c,
                forall|c2: int| 0 <= c2 < c ==> #[trigger] fu@[c2] as nat == self@.cfree(c2),
                forall|c2: int| 0 <= c2 < c ==> #[trigger] rc@[c2] as nat == self@.rcount(c2, no_prot(self@)),
            decreases k - c,
        {
            fu.push(self.class_free(c));
            rc.push(self.count_reclaimable(c, &prot));
            c += 1;
        }
        ArenaView { owner: vstd::slice::slice_to_vec(self.owner.as_slice()), free_units: fu, reclaimable: rc }
    }
}

} // verus!

verus! {

/// Unit `g` of class `c` occupies arena bytes `[g·u_c, (g+1)·u_c)`.
pub open spec fn unit_bytes(o: CoordV, c: int, g: int) -> (int, int) {
    (g * (o.unit[c] as int), (g + 1) * (o.unit[c] as int))
}

/// Unit `g` is owned by class `c`.
pub open spec fn owns(o: CoordV, c: int, g: int) -> bool {
    if c < o.np {
        o.paged[c].own[g]
    } else {
        o.state[c - o.np].own[g]
    }
}

/// A1 places unit `g` of class `c` inside slab `g / n_c`.
pub proof fn lemma_unit_in_slab(u: nat, n: nat, sb: nat, g: nat)
    requires
        u >= 1,
        n >= 1,
        sb == n * u,
    ensures
        (g / n) * sb <= g * u,
        (g + 1) * u <= (g / n + 1) * sb,
{
    lemma_div_bounds(g, n);
    let s = g / n;
    let r = g % n;
    assert(g == s * n + r);
    assert(g * u == s * sb + r * u) by (nonlinear_arith) requires g == s * n + r, sb == n * u;
    assert((g + 1) * u == s * sb + (r + 1) * u) by (nonlinear_arith) requires g == s * n + r, sb == n * u;
    assert((r + 1) * u <= n * u) by (nonlinear_arith) requires r + 1 <= n;
    assert((s + 1) * sb == s * sb + sb) by (nonlinear_arith);
}

impl Coordinator {
    /// Arena disjointness (§4, §9.1 obligation 10): two distinct owned units, of the same or of
    /// different classes, occupy disjoint byte ranges, and every owned unit lies in `[0, N·S)`.
    pub proof fn theorem_arena_disjoint(&self, c1: int, g1: int, c2: int, g2: int)
        requires
            self.inv(),
            0 <= c1 < self@.ncls(),
            0 <= c2 < self@.ncls(),
            0 <= g1 < self@.nslab * (self@.per[c1] as nat),
            0 <= g2 < self@.nslab * (self@.per[c2] as nat),
            owns(self@, c1, g1),
            owns(self@, c2, g2),
            (c1, g1) != (c2, g2),
        ensures
            unit_bytes(self@, c1, g1).1 <= unit_bytes(self@, c2, g2).0 || unit_bytes(self@, c2, g2).1 <= unit_bytes(self@, c1, g1).0,
            0 <= unit_bytes(self@, c1, g1).0,
            unit_bytes(self@, c1, g1).1 <= self@.nslab * self@.sbytes,
    {
        self.lemma_view();
        let o = self@;
        let u1 = self.unit@[c1] as nat;
        let u2 = self.unit@[c2] as nat;
        let n1 = self.per_c(c1);
        let n2 = self.per_c(c2);
        let sb = self.sbytes as nat;
        assert(self.unit@[c1] >= 1 && self.per@[c1] == self.sbytes / self.unit@[c1]);
        assert(self.unit@[c2] >= 1 && self.per@[c2] == self.sbytes / self.unit@[c2]);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(sb as int, u1 as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(sb as int, u2 as int);
        assert(sb == n1 * u1) by (nonlinear_arith) requires sb as int == (u1 as int) * (n1 as int) + 0;
        assert(sb == n2 * u2) by (nonlinear_arith) requires sb as int == (u2 as int) * (n2 as int) + 0;
        lemma_unit_in_slab(u1, n1, sb, g1 as nat);
        lemma_unit_in_slab(u2, n2, sb, g2 as nat);
        let s1 = (g1 as nat) / n1;
        let s2 = (g2 as nat) / n2;
        // Ownership is the slab owner (I12/I13).
        assert(self.cown(c1, g1) == (self.owner@[g1 / (n1 as int)] == c1 + 1));
        assert(self.cown(c2, g2) == (self.owner@[g2 / (n2 as int)] == c2 + 1));
        assert(owns(o, c1, g1) == self.cown(c1, g1));
        assert(owns(o, c2, g2) == self.cown(c2, g2));
        lemma_div_bounds(g1 as nat, n1);
        if s1 >= self.nslab {
            lemma_mul_mono(self.nslab as nat, s1, n1);
        }
        assert((s1 + 1) * sb <= (self.nslab as nat) * sb) by (nonlinear_arith) requires s1 + 1 <= self.nslab;
        if c1 == c2 {
            assert(g1 != g2);
            if g1 < g2 {
                assert((g1 + 1) * (u1 as int) <= g2 * (u1 as int)) by (nonlinear_arith) requires g1 + 1 <= g2;
            } else {
                assert((g2 + 1) * (u1 as int) <= g1 * (u1 as int)) by (nonlinear_arith) requires g2 + 1 <= g1;
            }
        } else {
            // Different classes own different slabs.
            assert(s1 != s2);
            if s1 < s2 {
                assert((s1 + 1) * sb <= s2 * sb) by (nonlinear_arith) requires s1 + 1 <= s2;
            } else {
                assert((s2 + 1) * sb <= s1 * sb) by (nonlinear_arith) requires s2 + 1 <= s1;
            }
        }
    }
}

} // verus!

verus! {

impl Coordinator {
    /// Public facts about the configuration of a valid coordinator.
    pub proof fn lemma_public_shape(&self)
        requires
            self.inv(),
        ensures
            self@.np >= 1,
            self@.paged.len() == self@.np,
            self@.ncls() == self@.np + self@.nst(),
            self@.b >= 1,
            self@.slots.dom() == self@.leases().dom(),
            forall|c: int| 0 <= c < self@.np ==> (#[trigger] self@.paged[c]).leases.dom() == self@.leases().dom()
                && self@.paged[c].next_handle == self@.next_handle() && self@.paged[c].pend == self@.pend(),
    {
        self.lemma_view();
        assert forall|c: int| 0 <= c < self@.np implies (#[trigger] self@.paged[c]).leases.dom() == self@.leases().dom()
            && self@.paged[c].next_handle == self@.next_handle() && self@.paged[c].pend == self@.pend() by {
            assert(self.paged@[c] == self.paged@[c]);
        }
    }

    pub closed spec fn num_leases(&self) -> nat {
        self.paged@[0].num_leases()
    }

    pub closed spec fn num_pending(&self) -> nat {
        self.paged@[0].num_pending()
    }

    pub closed spec fn index_buckets(&self, c: int) -> nat {
        self.paged@[c].index_buckets()
    }

    pub closed spec fn num_slot_records(&self) -> nat {
        self.slots@.dom().len()
    }

    /// I11 (bounded metadata) for the coordinator: leases, slot records and pending tickets are
    /// bounded by the units of paged class 0; each class's key-index buckets by its unit count.
    pub proof fn lemma_bounded(&self)
        requires
            self.inv(),
        ensures
            self.num_leases() <= self@.nslab * (self@.per[0] as nat),
            self.num_slot_records() == self.num_leases(),
            self.num_pending() <= (self@.delta() + 1) * self.num_leases(),
            forall|c: int| 0 <= c < self@.np ==> #[trigger] self.index_buckets(c) <= self@.nslab * (self@.per[c] as nat),
    {
        self.lemma_view();
        assert(self.paged@[0].valid());
        self.paged@[0].lemma_bounded();
        assert(self@.paged[0] == self.pv(0));
        assert(self.slots@.dom() == self.pv(0).leases.dom());
        assert(self.paged@[0].num_leases() == self.pv(0).leases.dom().len());
        assert forall|c: int| 0 <= c < self@.np implies #[trigger] self.index_buckets(c) <= self@.nslab * (self@.per[c] as nat) by {
            assert(self.paged@[c].valid());
            self.paged@[c].lemma_bounded();
        }
    }
}

} // verus!
