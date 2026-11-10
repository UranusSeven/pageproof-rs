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

} // verus!
