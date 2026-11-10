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

pub open spec fn kmin_ok(ks: Seq<nat>, n: int, k: nat) -> bool {
    &&& forall|c: int| 0 <= c < n ==> k <= #[trigger] ks[c]
    &&& n > 0 ==> exists|c: int| 0 <= c < n && #[trigger] ks[c] == k
}

impl Coordinator {
    /// `Fits(m)`, executable.
    pub(crate) fn fits_exec(&self, m: usize) -> (r: bool)
        requires
            self.valid(),
        ensures
            r == self@.fits_m(m as nat),
    {
        proof {
            self.lemma_view();
            self.lemma_shape();
        }
        let mut sum: u128 = 0;
        let mut i: usize = 0;
        while i < self.npaged
            invariant
                self.valid(),
                i <= self.npaged,
                sum as nat == psum(self.per@, i as int, m as nat),
                sum as nat <= i * (m as nat),
                self.npaged < 0x1_0000,
            decreases self.npaged - i,
        {
            let p = self.per[i];
            proof {
                assert(self.unit@[i as int] >= 1);
                if m > 0 {
                    vstd::arithmetic::div_mod::lemma_div_plus_one((m - 1) as int, p as int);
                    vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator((m - 1) as int, 1, p as int);
                }
            }
            let q: usize = if m == 0 { 0 } else { (m - 1) / p + 1 };
            proof {
                if m == 0 {
                    assert(cdiv(0, p as nat) == 0) by {
                        vstd::arithmetic::div_mod::lemma_basic_div((p - 1) as int, p as int);
                    }
                }
                assert(q as nat == cdiv(m as nat, p as nat));
                assert(q <= m);
                lemma_mul_succ(i as nat, m as nat);
                assert((i + 1) * (m as nat) <= 0x1_0000 * (m as nat)) by (nonlinear_arith) requires i + 1 <= 0x1_0000;
                assert(0x1_0000 * (m as nat) <= u128::MAX) by (nonlinear_arith) requires m as nat <= u64::MAX;
            }
            sum = sum + q as u128;
            i += 1;
        }
        proof {
            assert(self.npaged * (m as nat) <= 0x1_0000 * (m as nat)) by (nonlinear_arith) requires self.npaged <= 0x1_0000;
            assert(0x1_0000 * (m as nat) <= u64::MAX * 0x1_0000) by (nonlinear_arith) requires m as nat <= u64::MAX;
            assert(self.state@.len() < 0x1_0000);
        }
        sum + (self.state.len() as u128) <= self.nslab as u128
    }

    /// Joint probe of C1 over every paged class, each capped at `cap`. Only ghost E8 logs change.
    pub(crate) fn joint_probe(&mut self, toks: &[Token], cap: usize) -> (r: (Vec<Probe>, usize))
        requires
            old(self).valid(),
            1 <= toks@.len(),
            cap + 1 <= cdiv(toks@.len(), old(self).b as nat),
            old(self)@.fits_m(cdiv(toks@.len(), old(self).b as nat)),
        ensures
            final(self).valid(),
            final(self)@ == old(self)@,
            r.0@.len() == final(self).np(),
            r.1 <= cap,
            forall|c: int|
                0 <= c < final(self).np() ==> {
                    &&& probe_ok(final(self).pv(c), final(self).paged@[c].den_log(), toks@, #[trigger] r.0@[c])
                    &&& is_kcap(final(self).pv(c), toks@, cap as nat, r.0@[c].hits@.len() as nat)
                    &&& r.1 <= r.0@[c].hits@.len()
                },
            exists|c: int| 0 <= c < final(self).np() && #[trigger] r.0@[c].hits@.len() == r.1,
    {
        let ghost o = *self;
        let mut probes: Vec<Probe> = Vec::new();
        let mut kmin: usize = cap;
        let ghost mut arg: int = 0;
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                o.valid(),
                self.valid(),
                self@ == o@,
                self.npaged == o.npaged,
                self.b == o.b,
                1 <= toks@.len(),
                cap + 1 <= cdiv(toks@.len(), self.b as nat),
                self@.fits_m(cdiv(toks@.len(), self.b as nat)),
                c <= self.npaged,
                probes@.len() == c,
                kmin <= cap,
                forall|c2: int|
                    0 <= c2 < c ==> {
                        &&& probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks@, #[trigger] probes@[c2])
                        &&& is_kcap(self.pv(c2), toks@, cap as nat, probes@[c2].hits@.len() as nat)
                        &&& kmin <= probes@[c2].hits@.len()
                    },
                c > 0 ==> 0 <= arg < c && probes@[arg].hits@.len() == kmin,
            decreases self.npaged - c,
        {
            let ghost before = *self;
            proof {
                self.lemma_view();
                assert(self.paged@[c as int].valid());
                assert(self.unit@[c as int] >= 1);
                lemma_fits_bound(self.per@, self.np(), self.nst(), self.nslab as nat, cdiv(toks@.len(), self.b as nat), c as int);
                assert(self.unit@[c as int] >= 1);
                lemma_cdiv_props(toks@.len(), self.b as nat);
                lemma_mul_mono(cdiv(toks@.len(), self.b as nat), self.cunits(c as int), self.b as nat);
            }
            let pr = self.paged[c].probe_prefix(toks, cap);
            proof {
                self.lemma_paged_swap(&before);
                assert forall|c2: int| 0 <= c2 < c implies probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks@, #[trigger] probes@[c2]) by {
                    assert(self.paged@[c2] == before.paged@[c2]);
                }
            }
            if pr.hits.len() < kmin || c == 0 {
                kmin = pr.hits.len();
                proof {
                    arg = c as int;
                }
            }
            let ghost p0 = probes@;
            probes.push(pr);
            proof {
                assert forall|c2: int|
                    0 <= c2 < c + 1 implies {
                    &&& probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks@, #[trigger] probes@[c2])
                    &&& is_kcap(self.pv(c2), toks@, cap as nat, probes@[c2].hits@.len() as nat)
                    &&& kmin <= probes@[c2].hits@.len()
                } by {
                    if c2 < c {
                        assert(probes@[c2] == p0[c2]);
                    }
                }
            }
            c += 1;
        }
        (probes, kmin)
    }

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
