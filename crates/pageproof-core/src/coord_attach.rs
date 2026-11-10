//! v0.3 C1 `attach` on the coordinator: joint `k*` across paged classes, exact `Prot`, demand,
//! `Cap`, the slab plan, and the all-or-nothing commit across every class. No trusted content.
use vstd::prelude::*;
use std::collections::HashMap;
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::arith::*;
use crate::manager::*;
use crate::state::*;
use crate::coord::*;
use crate::slabplan::*;
use crate::ops_attach::*;
#[cfg(verus_keep_ghost)]
use crate::index::in_index;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

impl Coordinator {
    /// Replacing paged pools by valid pools with the same views keeps `valid` and the view.
    pub(crate) proof fn lemma_paged_swap(&self, o: &Coordinator)
        requires
            o.valid(),
            self.id == o.id,
            self.nslab == o.nslab,
            self.sbytes == o.sbytes,
            self.b == o.b,
            self.npaged == o.npaged,
            self.unit@ == o.unit@,
            self.per@ == o.per@,
            self.owner@ == o.owner@,
            self.fs == o.fs,
            self.state@ == o.state@,
            self.slots@ == o.slots@,
            self.paged@.len() == o.paged@.len(),
            forall|c: int| 0 <= c < o.np() ==> (#[trigger] self.paged@[c]).valid() && self.pv(c) == o.pv(c),
        ensures
            self.valid(),
            self@ == o@,
    {
        assert forall|c: int| 0 <= c < o.np() implies #[trigger] self.pv(c) == o.pv(c) by {
            assert(self.paged@[c].valid());
        }
        assert(self.pv(0) == o.pv(0)) by {
            assert(self.paged@[0].valid());
        }
        assert forall|c: int, x: int| 0 <= c < self.ncls() && 0 <= x < self.cunits(c) implies #[trigger] self.cown(c, x)
            == (self.owner@[x / (self.per_c(c) as int)] == c + 1) by {
            assert(o.cown(c, x) == (o.owner@[x / (o.per_c(c) as int)] == c + 1));
            if c < self.np() {
                assert(self.pv(c) == o.pv(c));
            }
        }
        assert forall|i: int| 0 <= i < self.np() implies {
            &&& #[trigger] self.paged@[i].valid()
            &&& self.pv(i).p == self.cunits(i)
            &&& self.pv(i).b == self.b as nat
            &&& self.pv(i).ns == self.pv(0).ns
        } by {
            assert(o.paged@[i].valid());
            assert(self.pv(i) == o.pv(i));
        }
        assert forall|i: int| #![trigger self.paged@[i]] 0 <= i < self.np() implies {
            &&& self.pv(i).leases.dom() == self.pv(0).leases.dom()
            &&& self.pv(i).pend == self.pv(0).pend
            &&& self.pv(i).next_handle == self.pv(0).next_handle
            &&& self.pv(i).next_ticket == self.pv(0).next_ticket
        } by {
            assert(self.pv(i) == o.pv(i));
            assert(o.paged@[i] == o.paged@[i]);
        }
        assert forall|i: int, h: u64| 0 <= i < self.np() && #[trigger] self.pv(i).leases.contains_key(h) implies {
            &&& self.pv(i).leases[h].toks == self.pv(0).leases[h].toks
            &&& self.pv(i).leases[h].c == self.pv(0).leases[h].c
            &&& self.pv(i).leases[h].pending == self.pv(0).leases[h].pending
        } by {
            assert(self.pv(i) == o.pv(i));
            assert(o.pv(i).leases.contains_key(h));
        }
        assert(self.cfg_ok());
        assert(self.pools_ok());
        assert(self.own_ok());
        assert(self.lock_ok()) by {
            assert forall|h: u64| #[trigger] self.pv(0).leases.contains_key(h) implies self.fits_m(
                cdiv(self.pv(0).leases[h].toks.len(), self.b as nat),
            ) by {
                assert(o.pv(0).leases.contains_key(h));
            }
        }
        assert(self.slots_ok()) by {
            assert(self.pv(0).leases == o.pv(0).leases);
            assert(self.slots@.dom() == self.pv(0).leases.dom());
            assert forall|j: int| 0 <= j < self.nst() implies #[trigger] self.sv(j) == o.sv(j) by {}
            assert forall|h: u64, j: int|
                #![trigger self.slots@[h]@[j]]
                self.slots@.contains_key(h) && 0 <= j < self.nst() implies {
                let x = self.slots@[h]@[j];
                let l = self.pv(0).leases[h];
                &&& (x as nat) < self.sv(j).p
                &&& self.sv(j).holder[x as int] == Some(h)
                &&& l.c > 0 ==> self.sv(j).w[x as int] == Some(l.toks.subrange(0, l.c as int))
            } by {
                assert(o.slots@[h]@[j] == self.slots@[h]@[j]);
                assert(self.sv(j) == o.sv(j));
            }
            assert forall|j: int, x: int|
                #![trigger self.sv(j).holder[x]]
                0 <= j < self.nst() && 0 <= x < self.sv(j).p && self.sv(j).holder[x] is Some implies {
                let h = self.sv(j).holder[x]->Some_0;
                &&& self.slots@.contains_key(h)
                &&& self.slots@[h]@[j] as int == x
            } by {
                assert(self.sv(j) == o.sv(j));
                assert(o.sv(j).holder[x] is Some);
            }
        }
        self.lemma_view();
        o.lemma_view();
        assert(self@.paged =~= o@.paged);
        assert(self@.state =~= o@.state);
    }
}

} // verus!
