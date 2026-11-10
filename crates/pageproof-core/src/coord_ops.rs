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
pub open spec fn coord_extended(o: CoordV, mid: CoordV, n: CoordV, h: u64, suffix: Seq<Token>, d: nat, tables: Seq<Seq<PageId>>) -> bool {
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
            &&& tables[c].len() == cdiv(l.toks.len() + suffix.len(), o.b)
            &&& tables[c].subrange(0, o.paged[c].leases[h].table.len() as int) == o.paged[c].leases[h].table
            &&& fresh.len() == d
            &&& fresh.no_duplicates()
            &&& forall|j: int| 0 <= j < fresh.len() ==> mid.paged[c].is_free(#[trigger] fresh[j])
            &&& n.paged[c] == extended(mid.paged[c], h, suffix, fresh)
        }
}

/// The complete C2 contract.
pub open spec fn coord_extend_result(o: CoordV, n: CoordV, h: Handle, suffix: Seq<Token>, r: Result<LeaseView, Error>) -> bool {
    let live = h.mgr == o.id && o.leases().contains_key(h.id);
    let l = o.leases()[h.id];
    let l2 = l.toks.len() + suffix.len();
    let d = (cdiv(l2, o.b) - cdiv(l.toks.len(), o.b)) as nat;
    let ok = live && l.pending is None && l.c == l.toks.len() && suffix.len() > 0 && o.fits_m(cdiv(l2, o.b));
    &&& !live ==> r == Err::<LeaseView, Error>(Error::InvalidHandle)
    &&& (live && l.pending is Some) ==> r == Err::<LeaseView, Error>(Error::Busy)
    &&& (live && l.pending is None && l.c != l.toks.len()) ==> r == Err::<LeaseView, Error>(Error::InvalidPhase)
    &&& (live && l.pending is None && l.c == l.toks.len() && suffix.len() == 0) ==> r == Err::<LeaseView, Error>(
        Error::InvalidArgument,
    )
    &&& (live && l.pending is None && l.c == l.toks.len() && suffix.len() > 0 && !o.fits_m(cdiv(l2, o.b))) ==> r == Err::<
        LeaseView,
        Error,
    >(Error::RequestTooLarge)
    &&& ok ==> (r is Ok <==> o.cap(extend_demand(o, d), no_prot(o)))
    &&& (ok && !o.cap(extend_demand(o, d), no_prot(o))) ==> r == Err::<LeaseView, Error>(Error::NoCapacity)
    &&& r is Err ==> n == o
    &&& r matches Ok(view) ==> ok && exists|mid: CoordV| #[trigger] coord_extended(o, mid, n, h.id, suffix, d, tables_view(view.tables@))
}

pub proof fn lemma_extend_ok(o: CoordV, mid: CoordV, n: CoordV, h: Handle, suffix: Seq<Token>, view: LeaseView)
    requires
        h.mgr == o.id,
        o.leases().contains_key(h.id),
        o.leases()[h.id].pending is None,
        o.leases()[h.id].c == o.leases()[h.id].toks.len(),
        suffix.len() > 0,
        o.fits_m(cdiv(o.leases()[h.id].toks.len() + suffix.len(), o.b)),
        o.cap(
            extend_demand(o, (cdiv(o.leases()[h.id].toks.len() + suffix.len(), o.b) - cdiv(o.leases()[h.id].toks.len(), o.b)) as nat),
            no_prot(o),
        ),
        coord_extended(
            o,
            mid,
            n,
            h.id,
            suffix,
            (cdiv(o.leases()[h.id].toks.len() + suffix.len(), o.b) - cdiv(o.leases()[h.id].toks.len(), o.b)) as nat,
            tables_view(view.tables@),
        ),
    ensures
        coord_extend_result(o, n, h, suffix, Ok(view)),
{
    let l = o.leases()[h.id];
    let l2 = l.toks.len() + suffix.len();
    let d = (cdiv(l2, o.b) - cdiv(l.toks.len(), o.b)) as nat;
    assert(coord_extended(o, mid, n, h.id, suffix, d, tables_view(view.tables@)));
    let r = Ok::<LeaseView, Error>(view);
    assert(r->Ok_0 == view);
    assert(exists|m2: CoordV| #[trigger] coord_extended(o, m2, n, h.id, suffix, d, tables_view(view.tables@)));
}

impl Coordinator {
    /// Lease `h` is live and its pending flag, executable.
    pub(crate) fn lease_live(&self, h: Handle) -> (r: Option<bool>)
        requires
            self.valid(),
        ensures
            r is None <==> !(h.mgr == self@.id && self@.leases().contains_key(h.id)),
            r matches Some(p) ==> p == (self@.leases()[h.id].pending is Some),
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
            (h.mgr == old(self)@.id && old(self)@.leases().contains_key(h.id) && old(self)@.leases()[h.id].pending is Some)
                ==> r == Err::<Vec<Token>, Error>(Error::Busy),
            r is Err ==> final(self)@ == old(self)@,
            r matches Ok(toks) ==> {
                &&& h.mgr == old(self)@.id
                &&& old(self)@.leases().contains_key(h.id)
                &&& old(self)@.leases()[h.id].pending is None
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
                o.pv(0).leases[h.id].pending is None,
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
                assert(self.pv(c as int).leases[h.id].pending is None);
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
            o.pv(0).leases[h].pending is None,
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
            && self.pv(c).b == o.pv(c).b && self.pv(c).ns == o.pv(c).ns && self.pv(c).leases == o.pv(c).leases.remove(h)
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
            } by {
                assert(o.paged@[i].valid());
                assert(self.pv(i).p == o.pv(i).p);
                assert(self.pv(0).ns == o.pv(0).ns);
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
            } by {
                assert(o.pv(i).leases.contains_key(h2));
            }
            assert forall|h2: u64| #[trigger] self.pv(0).leases.contains_key(h2) implies self.fits_m(
                cdiv(self.pv(0).leases[h2].toks.len(), self.b as nat),
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
            self.pv(c).leases[h].table.len() == cdiv(self.pv(c).leases[h].toks.len(), self.b as nat),
    {
        assert(self.paged@[c].valid());
        reveal(lease_ok);
        assert(lease_ok(self.pv(c), self.paged@[c].den_log(), h));
        let l = self.pv(c).leases[h];
        let m = l.table.len();
        let q = cdiv(l.toks.len(), self.b as nat);
        lemma_cdiv_props(l.toks.len(), self.b as nat);
        if m < q {
            lemma_mul_mono(m, (q - 1) as nat, self.b as nat);
        }
        if m > q {
            lemma_mul_mono(q, (m - 1) as nat, self.b as nat);
        }
    }

    /// `valid` after extending lease `h` in every paged class (state classes untouched).
    proof fn lemma_extend_valid(&self, mid: &Coordinator, h: u64, suffix: Seq<Token>)
        requires
            mid.valid(),
            mid.pv(0).leases.contains_key(h),
            mid.fits_m(cdiv(mid.pv(0).leases[h].toks.len() + suffix.len(), mid.b as nat)),
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
                    &&& self.pv(c).pend == mid.pv(c).pend
                    &&& self.pv(c).next_handle == mid.pv(c).next_handle
                    &&& self.pv(c).next_ticket == mid.pv(c).next_ticket
                    &&& self.pv(c).leases == mid.pv(c).leases.insert(
                        h,
                        LeaseV {
                            toks: mid.pv(c).leases[h].toks + suffix,
                            table: self.pv(c).leases[h].table,
                            ..mid.pv(c).leases[h]
                        },
                    )
                },
        ensures
            self.valid(),
    {
        assert(self.cfg_ok());
        assert(self.pools_ok()) by {
            assert forall|i: int| 0 <= i < self.np() implies {
                &&& #[trigger] self.paged@[i].valid()
                &&& self.pv(i).p == self.cunits(i)
                &&& self.pv(i).b == self.b as nat
                &&& self.pv(i).ns == self.pv(0).ns
            } by {
                assert(mid.paged@[i].valid());
                assert(self.paged@[0].valid());
            }
            assert forall|j: int| 0 <= j < self.nst() implies {
                &&& #[trigger] self.state@[j].valid()
                &&& self.sv(j).p == self.cunits(self.np() + j)
            } by {
                assert(mid.state@[j].valid());
            }
        }
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
            } by {
                assert(self.paged@[i].valid());
                assert(mid.pv(i).leases.contains_key(h2));
                assert(mid.paged@[i] == mid.paged@[i]);
                assert(mid.pv(i).leases.contains_key(h));
            }
            assert forall|h2: u64| #[trigger] self.pv(0).leases.contains_key(h2) implies self.fits_m(
                cdiv(self.pv(0).leases[h2].toks.len(), self.b as nat),
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
        let ghost o = *self;
        let ghost ov = o@;
        match self.lease_live(h) {
            None => return Err(Error::InvalidHandle),
            Some(true) => return Err(Error::Busy),
            Some(false) => {},
        }
        proof {
            o.lemma_view();
            assert(self.paged@[0].valid());
        }
        let (len, c0, _) = self.paged[0].lease_info(h.id);
        if c0 != len {
            return Err(Error::InvalidPhase);
        }
        if suffix.len() == 0 {
            return Err(Error::InvalidArgument);
        }
        let b = self.b;
        proof {
            self.lemma_table_len(0, h.id);
            reveal(lease_ok);
            assert(lease_ok(self.pv(0), self.paged@[0].den_log(), h.id));
            self.lemma_nslab_bound();
            assert(self.fits_m(cdiv(len as nat, b as nat)));
            lemma_fits_bound(self.per@, self.np(), self.nst(), self.nslab as nat, cdiv(len as nat, b as nat), 0);
            assert(self.unit@[0] >= 1);
            lemma_cdiv_props(len as nat, b as nat);
            lemma_mul_mono(cdiv(len as nat, b as nat), self.cunits(0), b as nat);
        }
        if suffix.len() > MAX_SLOTS as usize - len {
            proof {
                assert(!ov.fits_m(cdiv((len + suffix@.len()) as nat, b as nat))) by {
                    if ov.fits_m(cdiv((len + suffix@.len()) as nat, b as nat)) {
                        lemma_fits_bound(self.per@, self.np(), self.nst(), self.nslab as nat, cdiv((len + suffix@.len()) as nat, b as nat), 0);
                        lemma_cdiv_props((len + suffix@.len()) as nat, b as nat);
                        lemma_mul_mono(cdiv((len + suffix@.len()) as nat, b as nat), self.cunits(0), b as nat);
                    }
                }
            }
            return Err(Error::RequestTooLarge);
        }
        let l2 = len + suffix.len();
        let m = (len - 1) / b + 1;
        let m2 = (l2 - 1) / b + 1;
        proof {
            assert(len >= 1);
            vstd::arithmetic::div_mod::lemma_div_plus_one((len - 1) as int, b as int);
            vstd::arithmetic::div_mod::lemma_div_plus_one((l2 - 1) as int, b as int);
            assert(((len - 1 + b) as int) / (b as int) == ((len - 1) as int) / (b as int) + 1);
            assert(((l2 - 1 + b) as int) / (b as int) == ((l2 - 1) as int) / (b as int) + 1);
            assert(m as nat == cdiv(len as nat, b as nat));
            assert(m2 as nat == cdiv(l2 as nat, b as nat));
            lemma_cdiv_mono(len as nat, l2 as nat, b as nat);
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
                lemma_cdiv_le(l2 as nat, b as nat, max_slots());
                assert(l2 as nat <= max_slots() * (b as nat)) by (nonlinear_arith) requires l2 <= max_slots(), b >= 1;
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
        }
        let mut tables: Vec<Vec<PageId>> = Vec::new();
        let ghost lv0 = mid.pv(0).leases[h.id];
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                mid.valid(),
                mid.pv(0).leases.contains_key(h.id),
                mid.pv(0).leases[h.id].pending is None,
                mid.pv(0).leases[h.id].c == len,
                mid.pv(0).leases[h.id].toks.len() == len,
                l2 == len + suffix@.len(),
                suffix@.len() > 0,
                m2 as nat == cdiv(l2 as nat, b as nat),
                m as nat == cdiv(len as nat, b as nat),
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
                    0 <= c2 < c ==> (#[trigger] self.paged@[c2]).valid() && extend_result(
                        mid.pv(c2),
                        self.pv(c2),
                        Handle { mgr: mid.pv(c2).id, id: h.id },
                        suffix@,
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
                assert(mid.unit@[c as int] >= 1);
                lemma_fits_bound(mid.per@, mid.np(), mid.nst(), mid.nslab as nat, m2 as nat, c as int);
                lemma_cdiv_props(l2 as nat, b as nat);
                lemma_mul_mono(m2 as nat, mid.cunits(c as int), b as nat);
            }
            let mid_c = self.paged[c].mgr_id();
            let ghost p0 = self.paged@;
            let r = self.paged[c].extend(Handle { mgr: mid_c, id: h.id }, suffix);
            proof {
                assert forall|c2: int| 0 <= c2 < p0.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
            }
            match r {
                Ok(view) => {
                    let ghost tb = tables@;
                    tables.push(view.pages);
                    proof {
                        assert forall|c2: int| 0 <= c2 < c + 1 implies (#[trigger] self.paged@[c2]).valid() && extend_result(
                            mid.pv(c2),
                            self.pv(c2),
                            Handle { mgr: mid.pv(c2).id, id: h.id },
                            suffix@,
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
            Self::lemma_extend_post(&o, &pre, &mid, self, h.id, suffix@, dd as nat, d@, prot@, &tables);
            assert(self.slots@.contains_key(h.id)) by {
                assert(mid.slots@.dom() == mid.pv(0).leases.dom());
            }
        }
        let slv = vstd::slice::slice_to_vec(self.slots.get(&h.id).unwrap().as_slice());
        let lv = LeaseView { tables, slots: slv };
        proof {
            assert(ov.leases()[h.id].toks.len() == len);
            assert(dd as nat == (cdiv(l2 as nat, b as nat) - cdiv(len as nat, b as nat)) as nat);
            assert(ov.b == b as nat);
            lemma_extend_ok(ov, mid@, self@, h, suffix@, lv);
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
            mid.fits_m(cdiv(mid.pv(0).leases[h].toks.len() + suffix.len(), mid.b as nat)),
            dd == cdiv(mid.pv(0).leases[h].toks.len() + suffix.len(), mid.b as nat) - cdiv(
                mid.pv(0).leases[h].toks.len(),
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
                0 <= c2 < mid.np() ==> (#[trigger] fin.paged@[c2]).valid() && extend_result(
                    mid.pv(c2),
                    fin.pv(c2),
                    Handle { mgr: mid.pv(c2).id, id: h },
                    suffix,
                    Ok(PageTableView { pages: tables@[c2] }),
                ),
        ensures
            fin.valid(),
            coord_extended(o@, mid@, fin@, h, suffix, dd, tables_view(tables@)),
    {
        assert forall|c: int| 0 <= c < mid.np() implies {
            &&& (#[trigger] fin.paged@[c]).valid()
            &&& fin.pv(c).own == mid.pv(c).own
            &&& fin.pv(c).p == mid.pv(c).p
            &&& fin.pv(c).b == mid.pv(c).b
            &&& fin.pv(c).ns == mid.pv(c).ns
            &&& fin.pv(c).pend == mid.pv(c).pend
            &&& fin.pv(c).next_handle == mid.pv(c).next_handle
            &&& fin.pv(c).next_ticket == mid.pv(c).next_ticket
            &&& fin.pv(c).leases == mid.pv(c).leases.insert(
                h,
                LeaseV { toks: mid.pv(c).leases[h].toks + suffix, table: fin.pv(c).leases[h].table, ..mid.pv(c).leases[h] },
            )
        } by {
            let fresh = tables@[c]@.subrange(mid.pv(c).leases[h].table.len() as int, tables@[c]@.len() as int);
            assert(fin.pv(c) == extended(mid.pv(c), h, suffix, fresh));
        }
        assert(mid.pv(0).leases[h] == fin.pv(0).leases[h] || true);
        fin.lemma_extend_valid(mid, h, suffix);
        o.lemma_view();
        pre.lemma_view();
        mid.lemma_view();
        fin.lemma_view();
        let tv = tables_view(tables@);
        assert forall|c: int| 0 <= c < o@.np implies {
            let fresh = (#[trigger] tv[c]).subrange(o@.paged[c].leases[h].table.len() as int, tv[c].len() as int);
            &&& tv[c].len() == cdiv(o@.leases()[h].toks.len() + suffix.len(), o@.b)
            &&& tv[c].subrange(0, o@.paged[c].leases[h].table.len() as int) == o@.paged[c].leases[h].table
            &&& fresh.len() == dd
            &&& fresh.no_duplicates()
            &&& forall|j: int| 0 <= j < fresh.len() ==> mid@.paged[c].is_free(#[trigger] fresh[j])
            &&& fin@.paged[c] == extended(mid@.paged[c], h, suffix, fresh)
        } by {
            assert(tv[c] == tables@[c]@);
            assert(o@.paged[c] == pre.pv(c));
            assert(mid.pv(c).leases == pre.pv(c).leases);
            assert(mid.paged@[c].valid());
            assert(mid.pv(c).leases.contains_key(h));
            assert(mid.pv(c).leases[h].toks == mid.pv(0).leases[h].toks);
            mid.lemma_table_len(c, h);
            mid.lemma_table_len(0, h);
            assert(o@.paged[0] == pre.pv(0));
            assert(o@.leases()[h] == mid.pv(0).leases[h]);
            assert(mid@.paged[c] == mid.pv(c));
            assert(fin@.paged[c] == fin.pv(c));
            let mv = mid.pv(c);
            let l = mv.leases[h];
            let r = Ok::<PageTableView, Error>(PageTableView { pages: tables@[c] });
            assert(extend_result(mv, fin.pv(c), Handle { mgr: mv.id, id: h }, suffix, r));
            let view = r->Ok_0;
            assert(view.pages@ == tables@[c]@);
            let fresh = view.pages@.subrange(l.table.len() as int, view.pages@.len() as int);
            assert(view.pages@.len() == cdiv(l.toks.len() + suffix.len(), mv.b));
            assert(fresh.len() == cdiv(l.toks.len() + suffix.len(), mv.b) - l.table.len());
            assert(forall|j: int| 0 <= j < fresh.len() ==> mv.is_free(#[trigger] fresh[j]));
            assert(fin.pv(c) == extended(mv, h, suffix, fresh));
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
    pub input_ids: Vec<Token>,
    pub positions: Vec<usize>,
    pub block_size: usize,
    /// Per paged class: write slots of `[a, z)` and the page mapping of `[0, z)`.
    pub write_slots: Vec<Vec<usize>>,
    pub page_tables: Vec<Vec<PageId>>,
    /// Per state class: `σ_h^c`.
    pub state_slots: Vec<usize>,
    /// The state slots start from the initial state (`a == 0`, E10).
    pub init: bool,
}

/// C3 plan correctness across classes.
pub open spec fn cplan_ok(o: CoordV, h: u64, n: nat, plan: CoordPlan) -> bool {
    let l = o.leases()[h];
    let a = l.c;
    let z = l.c + n;
    &&& plan.ticket == Ticket { mgr: o.id, id: o.next_ticket() }
    &&& plan.handle == Handle { mgr: o.id, id: h }
    &&& plan.block_size as nat == o.b
    &&& plan.input_ids@ == l.toks.subrange(a as int, z as int)
    &&& plan.positions@.len() == n
    &&& forall|q: int| 0 <= q < n ==> #[trigger] plan.positions@[q] as int == a + q
    &&& plan.write_slots@.len() == o.np
    &&& plan.page_tables@.len() == o.np
    &&& forall|c: int|
        0 <= c < o.np ==> {
            let lc = o.paged[c].leases[h];
            &&& (#[trigger] plan.write_slots@[c])@.len() == n
            &&& forall|q: int| 0 <= q < n ==> #[trigger] plan.write_slots@[c]@[q] as int == slot_of(o.b, lc.table, a + q)
            &&& forall|q: int| 0 <= q < n ==> (#[trigger] plan.write_slots@[c]@[q] as nat) < o.paged[c].p * o.b
            &&& forall|q1: int, q2: int|
                0 <= q1 < n && 0 <= q2 < n && q1 != q2 ==> #[trigger] plan.write_slots@[c]@[q1] != #[trigger] plan.write_slots@[c]@[q2]
            &&& forall|q: int| 0 <= q < n ==> write_page_ok(o.paged[c], h, #[trigger] lc.table[(a + q) / (o.b as int)])
            &&& plan.page_tables@[c]@ == lc.table.subrange(0, cdiv(z, o.b) as int)
            // §9.0 (b) per class.
            &&& forall|j: int| 0 <= j < a ==> (o.paged[c].vmap)(#[trigger] slot_of(o.b, lc.table, j)) == l.toks.subrange(0, j + 1)
        }
    &&& plan.state_slots@ == o.slots[h]
    &&& plan.init == (a == 0)
    &&& forall|j: int|
        0 <= j < o.nst() ==> {
            &&& o.state[j].holder[(#[trigger] plan.state_slots@[j]) as int] == Some(h)
            &&& a > 0 ==> o.state[j].w[plan.state_slots@[j] as int] == Some(l.toks.subrange(0, a as int))
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

pub open spec fn coord_begin_result(o: CoordV, n: CoordV, h: Handle, k: usize, r: Result<(Ticket, CoordPlan), Error>) -> bool {
    let live = h.mgr == o.id && o.leases().contains_key(h.id);
    let l = o.leases()[h.id];
    &&& !live ==> r == Err::<(Ticket, CoordPlan), Error>(Error::InvalidHandle)
    &&& (live && l.pending is Some) ==> r == Err::<(Ticket, CoordPlan), Error>(Error::Busy)
    &&& (live && l.pending is None && !(0 < k && l.c + k <= l.toks.len())) ==> r == Err::<(Ticket, CoordPlan), Error>(
        Error::InvalidArgument,
    )
    &&& (live && l.pending is None && 0 < k && l.c + k <= l.toks.len()) ==> (r is Ok <==> o.next_ticket() < u64::MAX)
    &&& (live && l.pending is None && 0 < k && l.c + k <= l.toks.len() && o.next_ticket() == u64::MAX) ==> r == Err::<
        (Ticket, CoordPlan),
        Error,
    >(Error::IdentifierExhausted)
    &&& r is Err ==> n == o
    &&& r matches Ok((t, plan)) ==> {
        &&& live
        &&& t == plan.ticket
        &&& cplan_ok(o, h.id, k as nat, plan)
        &&& paged_step(o, n)
        &&& n.state == o.state
        &&& forall|c: int| 0 <= c < o.np ==> #[trigger] n.paged[c] == began(o.paged[c], h.id, k as nat)
    }
}

pub open spec fn coord_finish_result(o: CoordV, n: CoordV, t: Ticket, r: Result<usize, Error>) -> bool {
    let live = t.mgr == o.id && o.pend().contains_key(t.id);
    &&& !live ==> r == Err::<usize, Error>(Error::InvalidTicket)
    &&& live ==> r is Ok
    &&& r is Err ==> n == o
    &&& r matches Ok(z) ==> {
        let pr = o.pend()[t.id];
        let h = pr.lease;
        let l = o.leases()[h];
        &&& live
        &&& z as nat == pr.z
        &&& paged_step(o, n)
        &&& forall|c: int| 0 <= c < o.np ==> #[trigger] finish_rel(o.paged[c], n.paged[c], t.id)
        // §9.0 (c) for state classes: every live slot now holds the state after `T_h[0:z]`.
        &&& forall|j: int|
            0 <= j < o.nst() ==> #[trigger] n.state[j] == (StateV {
                w: o.state[j].w.update(o.slots[h][j] as int, Some(l.toks.subrange(0, pr.z as int))),
                ..o.state[j]
            })
    }
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
                    &&& self.pv(c).next_handle == o.pv(c).next_handle
                    &&& self.pv(c).leases.dom() == o.pv(c).leases.dom()
                    &&& forall|h2: u64| #[trigger] o.pv(c).leases.contains_key(h2) && h2 != h ==> self.pv(c).leases[h2]
                        == o.pv(c).leases[h2]
                    &&& self.pv(c).leases[h].toks == o.pv(c).leases[h].toks
                    &&& self.pv(c).leases[h].c == self.pv(0).leases[h].c
                    &&& self.pv(c).leases[h].pending == self.pv(0).leases[h].pending
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
            } by {
                assert(self.paged@[i].valid());
                assert(o.pv(i).leases.contains_key(h2));
                assert(o.paged@[i] == o.paged@[i]);
                if h2 != h {
                    assert(o.pv(0).leases.contains_key(h2));
                    assert(self.pv(0).leases[h2] == o.pv(0).leases[h2]);
                } else {
                    assert(o.pv(i).leases[h].toks == o.pv(0).leases[h].toks);
                    assert(self.pv(0).leases[h].toks == o.pv(0).leases[h].toks);
                }
            }
            assert forall|h2: u64| #[trigger] self.pv(0).leases.contains_key(h2) implies self.fits_m(
                cdiv(self.pv(0).leases[h2].toks.len(), self.b as nat),
            ) by {
                assert(o.pv(0).leases.contains_key(h2));
                if h2 != h {
                    assert(self.pv(0).leases[h2] == o.pv(0).leases[h2]);
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
    /// C3. `begin_write(h, n)`: one ticket whose plan covers every class.
    pub fn begin_write(&mut self, h: Handle, k: usize) -> (r: Result<(Ticket, CoordPlan), Error>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            coord_begin_result(old(self)@, final(self)@, h, k, r),
    {
        let ghost o = *self;
        let ghost ov = o@;
        match self.lease_live(h) {
            None => return Err(Error::InvalidHandle),
            Some(true) => return Err(Error::Busy),
            Some(false) => {},
        }
        proof {
            o.lemma_view();
            assert(self.paged@[0].valid());
        }
        let (len, a, _) = self.paged[0].lease_info(h.id);
        proof {
            reveal(lease_ok);
            assert(lease_ok(self.pv(0), self.paged@[0].den_log(), h.id));
        }
        if k == 0 || k > len - a {
            return Err(Error::InvalidArgument);
        }
        let tid = self.paged[0].next_ticket_exec();
        if tid == u64::MAX {
            return Err(Error::IdentifierExhausted);
        }
        let mut wslots: Vec<Vec<usize>> = Vec::new();
        let mut ptabs: Vec<Vec<PageId>> = Vec::new();
        let mut input_ids: Vec<Token> = Vec::new();
        let mut positions: Vec<usize> = Vec::new();
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                o.valid(),
                ov == o@,
                o.pv(0).leases.contains_key(h.id),
                o.pv(0).leases[h.id].pending is None,
                o.pv(0).leases[h.id].c == a,
                o.pv(0).leases[h.id].toks.len() == len,
                0 < k <= len - a,
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
                c > 0 ==> input_ids@ == o.pv(0).leases[h.id].toks.subrange(a as int, (a + k) as int) && positions@.len() == k
                    && forall|q: int| 0 <= q < k ==> #[trigger] positions@[q] as int == a + q,
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
                        &&& self.pv(c2) == began(o.pv(c2), h.id, k as nat)
                        &&& plan_ok(o.pv(c2), h.id, k as nat, plan)
                        &&& forall|j: int|
                            0 <= j < o.pv(c2).leases[h.id].c ==> (o.pv(c2).vmap)(#[trigger] slot_of(
                                o.pv(c2).b,
                                o.pv(c2).leases[h.id].table,
                                j,
                            )) == o.pv(c2).leases[h.id].toks.subrange(0, j + 1)
                    },
            decreases self.npaged - c,
        {
            proof {
                assert(self.paged@[c as int] == o.paged@[c as int]);
                assert(o.paged@[c as int].valid());
                assert(o.pv(c as int).leases.contains_key(h.id));
                assert(o.pv(c as int).leases[h.id].toks == o.pv(0).leases[h.id].toks);
                assert(o.pv(c as int).leases[h.id].c == o.pv(0).leases[h.id].c);
                assert(o.pv(c as int).leases[h.id].pending == o.pv(0).leases[h.id].pending);
                assert(o.pv(c as int).next_ticket == tid);
            }
            let mid_c = self.paged[c].mgr_id();
            let ghost p0 = self.paged@;
            let r = self.paged[c].begin_write(Handle { mgr: mid_c, id: h.id }, k);
            proof {
                assert forall|c2: int| 0 <= c2 < p0.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
            }
            match r {
                Ok((t, plan)) => {
                    let ghost wb = wslots@;
                    let ghost pb = ptabs@;
                    if c == 0 {
                        input_ids = vstd::slice::slice_to_vec(plan.input_ids.as_slice());
                        positions = vstd::slice::slice_to_vec(plan.positions.as_slice());
                    }
                    proof {
                        assert(plan.input_ids@ == o.pv(c as int).leases[h.id].toks.subrange(a as int, (a + k) as int));
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
                            &&& self.pv(c2) == began(o.pv(c2), h.id, k as nat)
                            &&& plan_ok(o.pv(c2), h.id, k as nat, pl)
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
            write_slots: wslots,
            page_tables: ptabs,
            state_slots: sl,
            init: a == 0,
        };
        proof {
            Self::lemma_begin_post(&o, self, h.id, k as nat, tid, &plan);
        }
        Ok((Ticket { mgr: self.id, id: tid }, plan))
    }

    proof fn lemma_begin_post(o: &Coordinator, fin: &Coordinator, h: u64, k: nat, tid: u64, plan: &CoordPlan)
        requires
            o.valid(),
            o.pv(0).leases.contains_key(h),
            o.pv(0).leases[h].pending is None,
            tid == o.pv(0).next_ticket,
            tid < u64::MAX,
            0 < k,
            k <= usize::MAX,
            o.pv(0).leases[h].c + k <= o.pv(0).leases[h].toks.len(),
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
            plan.state_slots@ == o.slots@[h]@,
            plan.init == (o.pv(0).leases[h].c == 0),
            plan.write_slots@.len() == o.np(),
            plan.page_tables@.len() == o.np(),
            plan.input_ids@ == o.pv(0).leases[h].toks.subrange(o.pv(0).leases[h].c as int, (o.pv(0).leases[h].c + k) as int),
            plan.positions@.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] plan.positions@[q] as int == o.pv(0).leases[h].c + q,
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
                    &&& fin.pv(c2) == began(o.pv(c2), h, k)
                    &&& plan_ok(o.pv(c2), h, k, pl)
                    &&& forall|j: int|
                        0 <= j < o.pv(c2).leases[h].c ==> (o.pv(c2).vmap)(#[trigger] slot_of(
                            o.pv(c2).b,
                            o.pv(c2).leases[h].table,
                            j,
                        )) == o.pv(c2).leases[h].toks.subrange(0, j + 1)
                },
        ensures
            fin.valid(),
            coord_begin_result(o@, fin@, plan.handle, k as usize, Ok((plan.ticket, *plan))),
    {
        assert forall|c: int| 0 <= c < o.np() implies {
            &&& (#[trigger] fin.paged@[c]).valid()
            &&& fin.pv(c).own == o.pv(c).own
            &&& fin.pv(c).p == o.pv(c).p
            &&& fin.pv(c).b == o.pv(c).b
            &&& fin.pv(c).ns == o.pv(c).ns
            &&& fin.pv(c).next_handle == o.pv(c).next_handle
            &&& fin.pv(c).leases.dom() == o.pv(c).leases.dom()
            &&& forall|h2: u64| #[trigger] o.pv(c).leases.contains_key(h2) && h2 != h ==> fin.pv(c).leases[h2] == o.pv(c).leases[h2]
            &&& fin.pv(c).leases[h].toks == o.pv(c).leases[h].toks
            &&& fin.pv(c).leases[h].c == fin.pv(0).leases[h].c
            &&& fin.pv(c).leases[h].pending == fin.pv(0).leases[h].pending
            &&& fin.pv(c).pend == fin.pv(0).pend
            &&& fin.pv(c).next_ticket == fin.pv(0).next_ticket
        } by {
            assert(o.paged@[c].valid());
            assert(o.pv(c).leases.contains_key(h));
            assert(o.pv(c).leases[h].c == o.pv(0).leases[h].c);
            assert(o.pv(c).pend == o.pv(0).pend);
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
        assert forall|c: int| 0 <= c < ov.np implies {
            let lc = ov.paged[c].leases[h];
            let a = l.c;
            let z = l.c + k;
            &&& (#[trigger] plan.write_slots@[c])@.len() == k
            &&& forall|q: int| 0 <= q < k ==> #[trigger] plan.write_slots@[c]@[q] as int == slot_of(ov.b, lc.table, a + q)
            &&& forall|q: int| 0 <= q < k ==> (#[trigger] plan.write_slots@[c]@[q] as nat) < ov.paged[c].p * ov.b
            &&& forall|q1: int, q2: int|
                0 <= q1 < k && 0 <= q2 < k && q1 != q2 ==> #[trigger] plan.write_slots@[c]@[q1] != #[trigger] plan.write_slots@[c]@[q2]
            &&& forall|q: int| 0 <= q < k ==> write_page_ok(ov.paged[c], h, #[trigger] lc.table[(a + q) / (ov.b as int)])
            &&& plan.page_tables@[c]@ == lc.table.subrange(0, cdiv(z, ov.b) as int)
            &&& forall|j: int| 0 <= j < a ==> (ov.paged[c].vmap)(#[trigger] slot_of(ov.b, lc.table, j)) == l.toks.subrange(0, j + 1)
        } by {
            assert(ov.paged[c] == o.pv(c));
            assert(o.paged@[c].valid());
            assert(o.pv(c).b == o.b as nat);
            assert(o.pv(c).leases.contains_key(h));
            assert(o.pv(c).leases[h].toks == o.pv(0).leases[h].toks);
            assert(o.pv(c).leases[h].c == o.pv(0).leases[h].c);
            let pl = ExecutionPlan {
                ticket: Ticket { mgr: o.pv(c).id, id: tid },
                handle: Handle { mgr: o.pv(c).id, id: h },
                input_ids: plan.input_ids,
                positions: plan.positions,
                write_slots: plan.write_slots@[c],
                page_table: plan.page_tables@[c],
                block_size: o.b,
            };
            assert(fin.paged@[c].valid());
            assert(plan_ok(o.pv(c), h, k, pl));
            assert(pl.write_slots@ == plan.write_slots@[c]@);
            assert(pl.page_table@ == plan.page_tables@[c]@);
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
        assert(plan.input_ids@ == l.toks.subrange(l.c as int, (l.c + k) as int));
        assert(plan.write_slots@.len() == ov.np);
        assert(plan.page_tables@.len() == ov.np);
        assert(plan.handle == Handle { mgr: ov.id, id: h });
        assert(plan.ticket == Ticket { mgr: ov.id, id: ov.next_ticket() });
        assert(cplan_ok(ov, h, k, *plan));
        assert forall|c: int| 0 <= c < ov.np implies #[trigger] fin@.paged[c] == began(ov.paged[c], h, k) by {}
        assert(fin@.state =~= ov.state);
        assert(fin@.slots =~= ov.slots);
    }
}

} // verus!
