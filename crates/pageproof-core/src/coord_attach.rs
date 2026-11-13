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
#[cfg(verus_keep_ghost)]
use crate::ops_slab::in_range;
use crate::ops_attach::*;
#[cfg(verus_keep_ghost)]
use crate::index::in_index;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// Snapshot of a lease returned by C1/C2/C6: one page table per paged class, one live slot per
/// state class.
pub struct LeaseView {
    pub tables: Vec<Vec<PageId>>,
    pub slots: Vec<usize>,
}

pub open spec fn tables_view(t: Seq<Vec<PageId>>) -> Seq<Seq<PageId>> {
    t.map_values(|x: Vec<PageId>| x@)
}

/// C1 success relation: `mid` is `o` after the slab plan, and `n` is `mid` with the new lease
/// attached in every paged class and a fresh live slot taken in every state class.
pub open spec fn coord_attached(
    o: CoordV,
    mid: CoordV,
    n: CoordV,
    toks: Seq<Token>,
    k: nat,
    tables: Seq<Seq<PageId>>,
    slots: Seq<usize>,
) -> bool {
    let h = o.next_handle();
    let m = cdiv(toks.len(), o.b);
    &&& mid.plan_rel(o, o.attach_demand(toks, m, k), o.attach_prot(toks, k))
    &&& tables.len() == o.np
    &&& slots.len() == o.nst()
    &&& n.id == o.id
    &&& n.nslab == o.nslab
    &&& n.sbytes == o.sbytes
    &&& n.b == o.b
    &&& n.unit == o.unit
    &&& n.per == o.per
    &&& n.np == o.np
    &&& n.owner == mid.owner
    &&& n.paged.len() == o.paged.len()
    &&& n.state.len() == o.state.len()
    &&& n.slots == mid.slots.insert(h, slots)
    &&& forall|c: int|
        0 <= c < o.np ==> {
            &&& (#[trigger] tables[c]).len() == m
            &&& attach_choice_k(mid.paged[c], toks, tables[c], k)
            &&& n.paged[c] == attached(mid.paged[c], toks, tables[c], k)
            // Hits come from the call-time Index, and an active candidate is used whenever one exists.
            &&& forall|i: int|
                #![trigger tables[c][i]]
                0 <= i < k ==> in_index(o.paged[c].keys, o.paged[c].key_of(toks, i as nat), tables[c][i]) && (
                o.paged[c].has_active_hit(o.paged[c].key_of(toks, i as nat)) ==> o.paged[c].refs[tables[c][i] as int] > 0)
        }
    &&& forall|j: int|
        0 <= j < o.nst() ==> {
            &&& mid.state[j].free_set().contains(#[trigger] slots[j])
            &&& n.state[j] == (StateV {
                holder: mid.state[j].holder.update(slots[j] as int, Some(h)),
                w: mid.state[j].w.update(slots[j] as int, None),
                ..mid.state[j]
            })
        }
}

/// The complete C1 contract of the coordinator.
pub open spec fn coord_attach_result(o: CoordV, n: CoordV, toks: Seq<Token>, r: Result<(Handle, usize, LeaseView), Error>) -> bool {
    let m = cdiv(toks.len(), o.b);
    let ok_in = toks.len() >= 1 && o.fits_m(m);
    &&& toks.len() == 0 ==> r == Err::<(Handle, usize, LeaseView), Error>(Error::InvalidArgument)
    &&& (toks.len() > 0 && !o.fits_m(m)) ==> r == Err::<(Handle, usize, LeaseView), Error>(Error::RequestTooLarge)
    &&& (ok_in && o.next_handle() == u64::MAX) ==> r == Err::<(Handle, usize, LeaseView), Error>(
        Error::IdentifierExhausted,
    )
    &&& (ok_in && o.next_handle() < u64::MAX) ==> (r is Ok || r == Err::<(Handle, usize, LeaseView), Error>(
        Error::NoCapacity,
    ))
    &&& r is Err ==> n == o
    &&& r == Err::<(Handle, usize, LeaseView), Error>(Error::NoCapacity) ==> exists|k: nat|
        o.joint_k(toks, m, k) && !o.cap(o.attach_demand(toks, m, k), o.attach_prot(toks, k))
    &&& r matches Ok((h, cached, view)) ==> {
        let k = cached as nat / o.b;
        &&& ok_in
        &&& h == Handle { mgr: o.id, id: o.next_handle() }
        &&& cached as nat == k * o.b
        &&& o.joint_k(toks, m, k)
        &&& o.cap(o.attach_demand(toks, m, k), o.attach_prot(toks, k))
        &&& exists|mid: CoordV| #[trigger] coord_attached(o, mid, n, toks, k, tables_view(view.tables@), view.slots@)
    }
}

/// Assembles the success case of `coord_attach_result`.
pub proof fn lemma_attach_ok(o: CoordV, mid: CoordV, n: CoordV, toks: Seq<Token>, k: nat, h: Handle, cached: usize, view: LeaseView)
    requires
        toks.len() >= 1,
        o.b >= 1,
        o.fits_m(cdiv(toks.len(), o.b)),
        o.next_handle() < u64::MAX,
        h == (Handle { mgr: o.id, id: o.next_handle() }),
        cached as nat == k * o.b,
        o.joint_k(toks, cdiv(toks.len(), o.b), k),
        o.cap(o.attach_demand(toks, cdiv(toks.len(), o.b), k), o.attach_prot(toks, k)),
        coord_attached(o, mid, n, toks, k, tables_view(view.tables@), view.slots@),
    ensures
        coord_attach_result(o, n, toks, Ok((h, cached, view))),
{
    lemma_slot_decomp(k, 0, o.b);
    assert((cached as nat) / o.b == k);
    let r = Ok::<(Handle, usize, LeaseView), Error>((h, cached, view));
    let m = cdiv(toks.len(), o.b);
    assert(r is Ok);
    let (h2, c2, v2) = r->Ok_0;
    assert(c2 == cached);
    assert(v2 == view);
    assert(coord_attached(o, mid, n, toks, k, tables_view(v2.tables@), v2.slots@));
}

/// The joint `k*` is unique.
pub proof fn lemma_joint_k_unique(o: CoordV, toks: Seq<Token>, m: nat, k1: nat, k2: nat)
    requires
        o.joint_k(toks, m, k1),
        o.joint_k(toks, m, k2),
    ensures
        k1 == k2,
{
    if o.nst() == 0 {
        if k1 < k2 {
            let c = choose|c: int| 0 <= c < o.np && !#[trigger] o.paged[c].has_hit(o.paged[c].key_of(toks, k1));
            assert(o.paged[c].has_hit(o.paged[c].key_of(toks, k1)));
        }
        if k2 < k1 {
            let c = choose|c: int| 0 <= c < o.np && !#[trigger] o.paged[c].has_hit(o.paged[c].key_of(toks, k2));
            assert(o.paged[c].has_hit(o.paged[c].key_of(toks, k2)));
        }
    }
}

/// C1 success condition as an equivalence: for valid input and a free handle id, `attach`
/// succeeds iff `Cap(d, Prot)` holds at the unique joint `k*`, and otherwise returns NoCapacity.
pub proof fn lemma_coord_attach_capacity_iff(
    o: CoordV,
    n: CoordV,
    toks: Seq<Token>,
    r: Result<(Handle, usize, LeaseView), Error>,
    k: nat,
)
    requires
        coord_attach_result(o, n, toks, r),
        toks.len() >= 1,
        o.fits_m(cdiv(toks.len(), o.b)),
        o.next_handle() < u64::MAX,
        o.joint_k(toks, cdiv(toks.len(), o.b), k),
    ensures
        r is Ok <==> o.cap(o.attach_demand(toks, cdiv(toks.len(), o.b), k), o.attach_prot(toks, k)),
        r is Err ==> r == Err::<(Handle, usize, LeaseView), Error>(Error::NoCapacity),
        r matches Ok((h, cached, view)) ==> cached as nat == k * o.b,
{
    let m = cdiv(toks.len(), o.b);
    if r is Ok {
        let (h, cached, view) = r->Ok_0;
        lemma_joint_k_unique(o, toks, m, cached as nat / o.b, k);
    } else {
        let k2 = choose|k2: nat| o.joint_k(toks, m, k2) && !o.cap(o.attach_demand(toks, m, k2), o.attach_prot(toks, k2));
        lemma_joint_k_unique(o, toks, m, k2, k);
    }
}

impl Coordinator {
    /// The minimum of the per-class probe runs is the joint `k*`.
    pub(crate) proof fn lemma_joint_k(&self, toks: Seq<Token>, m: nat, cap: nat, probes: Seq<Probe>, k: nat)
        requires
            self.valid(),
            m >= 1,
            cap + 1 <= m,
            self.nst() > 0 ==> cap == 0,
            self.nst() == 0 ==> cap + 1 == m,
            probes.len() == self.np(),
            k <= cap,
            forall|c: int|
                0 <= c < self.np() ==> is_kcap(self.pv(c), toks, cap, (#[trigger] probes[c]).hits@.len() as nat) && k
                    <= probes[c].hits@.len(),
            exists|c: int| 0 <= c < self.np() && #[trigger] probes[c].hits@.len() == k,
        ensures
            self@.joint_k(toks, m, k),
    {
        self.lemma_view();
        if self.nst() == 0 {
            assert forall|c: int, i: nat| 0 <= c < self@.np && i < k implies #[trigger] self@.paged[c].has_hit(
                self@.paged[c].key_of(toks, i),
            ) by {
                assert(is_kcap(self.pv(c), toks, cap, probes[c].hits@.len() as nat));
                assert(self@.paged[c] == self.pv(c));
            }
            if k + 1 < m {
                let c0 = choose|c: int| 0 <= c < self.np() && #[trigger] probes[c].hits@.len() == k;
                assert(is_kcap(self.pv(c0), toks, cap, probes[c0].hits@.len() as nat));
                assert(self@.paged[c0] == self.pv(c0));
            }
        }
    }

    /// Facts for committing paged class `c` after the slab plan.
    pub(crate) proof fn lemma_commit_pre(
        &self,
        pre: &Coordinator,
        toks: Seq<Token>,
        tp: Seq<Probe>,
        k: nat,
        m: nat,
        d: Seq<usize>,
        prot: Seq<bool>,
        c: int,
    )
        requires
            pre.valid(),
            self.valid(),
            self.slab_frame(pre, prot),
            self@.plan_rel(pre@, d, prot),
            d == pre@.attach_demand(toks, m, k),
            tp.len() == pre.np(),
            0 <= c < pre.np(),
            probe_ok(pre.pv(c), pre.paged@[c].den_log(), toks, tp[c]),
            tp[c].hits@.len() == k,
            forall|j: int|
                #![trigger tp[c].hits@[j]]
                0 <= j < k && !tp[c].hits@[j].1 ==> prot[tp[c].hits@[j].0 as int / (pre.per_c(c) as int)],
            k <= m,
            m <= usize::MAX,
        ensures
            probe_ok(self.pv(c), self.paged@[c].den_log(), toks, tp[c]),
            self.pv(c).free_set().len() >= m - count_active(self.pv(c), toks, k),
            count_active(self.pv(c), toks, k) == count_active(pre.pv(c), toks, k),
            forall|key: Digest| #[trigger] self.pv(c).has_active_hit(key) == pre.pv(c).has_active_hit(key),
            forall|key: Digest, x: PageId| #[trigger] in_index(self.pv(c).keys, key, x) ==> in_index(pre.pv(c).keys, key, x),
    {
        assert(self.paged@[c] == self.paged@[c]);
        let v = pre.pv(c);
        let w = self.pv(c);
        assert(pre.paged@[c].valid());
        assert(self.paged@[c].valid());
        assert(pre.unit@[c] >= 1);
        lemma_probe_transfer(v, w, pre.paged@[c].den_log(), toks, tp[c], pre.per_c(c), prot);
        self.lemma_view();
        pre.lemma_view();
        self.lemma_view_cls();
        assert(self@.cfree(c) >= d[c]);
        assert(pre@.paged[c] == v);
        lemma_n_active_eq(v, toks, tp[c].hits@, k);
        assert(count_active(v, toks, k) <= k);
        assert(m as int - count_active(v, toks, k) as int <= usize::MAX) by {
            assert(m <= usize::MAX);
        }
        assert(d[c] as nat == m - count_active(v, toks, k));
        assert(self@.paged[c] == w);
    }

    /// `valid` after committing the new lease `h` in every class.
    pub(crate) proof fn lemma_attach_valid(
        &self,
        mid: &Coordinator,
        toks: Seq<Token>,
        k: nat,
        h: u64,
        tabs: Seq<Seq<PageId>>,
        sl: Seq<usize>,
    )
        requires
            mid.valid(),
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
            self.state@.len() == mid.state@.len(),
            h == mid.pv(0).next_handle,
            h < u64::MAX,
            tabs.len() == mid.np(),
            sl.len() == mid.nst(),
            mid.nst() > 0 ==> k == 0,
            mid@.fits_m(cdiv(toks.len(), mid.b as nat)),
            forall|c: int|
                0 <= c < mid.np() ==> {
                    &&& (#[trigger] self.paged@[c]).valid()
                    &&& attach_choice_k(mid.pv(c), toks, tabs[c], k)
                    &&& self.pv(c) == attached(mid.pv(c), toks, tabs[c], k)
                },
            forall|j: int|
                0 <= j < mid.nst() ==> {
                    &&& (#[trigger] self.state@[j]).valid()
                    &&& mid.sv(j).free_set().contains(sl[j])
                    &&& self.sv(j) == (StateV {
                        holder: mid.sv(j).holder.update(sl[j] as int, Some(h)),
                        w: mid.sv(j).w.update(sl[j] as int, None),
                        ..mid.sv(j)
                    })
                },
            self.slots@.dom() == mid.slots@.dom().insert(h),
            self.slots@[h]@ == sl,
            forall|h2: u64| #[trigger] mid.slots@.contains_key(h2) ==> self.slots@[h2] == mid.slots@[h2],
        ensures
            self.valid(),
    {
        mid.lemma_view();
        assert(mid.paged@[0].valid());
        mid.paged@[0].lemma_handles_lt();
        let l = LeaseV { toks, table: tabs[0], c: k * (mid.b as nat), pending: Seq::empty() };
        assert forall|c: int| 0 <= c < mid.np() implies (#[trigger] self.pv(c)).leases.dom() == mid.pv(0).leases.dom().insert(h)
            && self.pv(c).pend == mid.pv(0).pend && self.pv(c).next_handle == (h + 1) as u64 && self.pv(c).next_ticket
            == mid.pv(0).next_ticket && self.pv(c).p == mid.pv(c).p && self.pv(c).b == mid.pv(c).b && self.pv(c).ns == mid.pv(c).ns
            && self.pv(c).own == mid.pv(c).own by {
            assert(self.paged@[c].valid());
            assert(mid.paged@[c] == mid.paged@[c]);
            assert(self.pv(c).leases.dom() =~= mid.pv(c).leases.dom().insert(h));
        }
        // cfg_ok unchanged.
        assert(self.cfg_ok());
        assert(self.pools_ok()) by {
            assert forall|i: int| 0 <= i < self.np() implies {
                &&& #[trigger] self.paged@[i].valid()
                &&& self.pv(i).p == self.cunits(i)
                &&& self.pv(i).b == self.b as nat
                &&& self.pv(i).ns == self.pv(0).ns
            } by {
                assert(mid.paged@[i].valid());
                assert(self.pv(i).p == mid.pv(i).p);
                assert(self.pv(0).ns == mid.pv(0).ns);
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
                    assert(self.pv(c).own == mid.pv(c).own);
                } else {
                    assert(self.sv(c - self.np()).own == mid.sv(c - self.np()).own);
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
                assert(self.pv(i).leases.dom() == mid.pv(0).leases.dom().insert(h));
                assert(self.pv(0).leases.dom() == mid.pv(0).leases.dom().insert(h));
            }
            assert forall|i: int, h2: u64| 0 <= i < self.np() && #[trigger] self.pv(i).leases.contains_key(h2) implies {
                &&& self.pv(i).leases[h2].toks == self.pv(0).leases[h2].toks
                &&& self.pv(i).leases[h2].c == self.pv(0).leases[h2].c
                &&& self.pv(i).leases[h2].pending == self.pv(0).leases[h2].pending
            } by {
                assert(self.pv(i) == attached(mid.pv(i), toks, tabs[i], k));
                assert(self.pv(0) == attached(mid.pv(0), toks, tabs[0], k));
                if h2 != h {
                    assert(mid.pv(i).leases.contains_key(h2));
                    assert(mid.paged@[i] == mid.paged@[i]);
                }
            }
            assert forall|h2: u64| #[trigger] self.pv(0).leases.contains_key(h2) implies self.fits_m(
                cdiv(self.pv(0).leases[h2].toks.len(), self.b as nat),
            ) by {
                assert(self.pv(0) == attached(mid.pv(0), toks, tabs[0], k));
                if h2 != h {
                    assert(mid.pv(0).leases.contains_key(h2));
                }
            }
        }
        assert(self.slots_ok()) by {
            assert(self.pv(0) == attached(mid.pv(0), toks, tabs[0], k));
            assert(self.slots@.dom() =~= self.pv(0).leases.dom());
            assert forall|h2: u64| #[trigger] self.slots@.contains_key(h2) implies self.slots@[h2]@.len() == self.nst() by {
                if h2 != h {
                    assert(mid.slots@.contains_key(h2));
                }
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
                assert(self.state@[j].valid());
                assert(mid.sv(j).free_set().contains(sl[j]));
                mid.state@[j].lemma_free();
                if h2 == h {
                    assert(k == 0);
                    assert(self.pv(0).leases[h].c == 0);
                } else {
                    assert(mid.slots@.contains_key(h2));
                    let x = mid.slots@[h2]@[j];
                    assert(mid.sv(j).holder[x as int] == Some(h2));
                    assert(x != sl[j]);
                    assert(self.pv(0).leases[h2] == mid.pv(0).leases[h2]);
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
                if x != sl[j] as int {
                    assert(mid.sv(j).holder[x] is Some);
                    let h2 = mid.sv(j).holder[x]->Some_0;
                    assert(mid.slots@.contains_key(h2));
                    assert(h2 < h);
                }
            }
        }
    }

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

    /// `Prot` of C1 for the hit prefix `k` (the first `k` hits of each probe).
    // `toks` is read only by the contract and the proof.
    #[allow(unused_variables)]
    pub(crate) fn compute_prot(&self, toks: &[Token], probes: &Vec<Probe>, k: usize) -> (r: Vec<bool>)
        requires
            self.valid(),
            probes@.len() == self.np(),
            forall|c: int|
                0 <= c < self.np() ==> probe_ok(self.pv(c), self.paged@[c].den_log(), toks@, #[trigger] probes@[c]) && k
                    <= probes@[c].hits@.len(),
        ensures
            r@ == self@.attach_prot(toks@, k as nat),
            forall|c: int, j: int|
                #![trigger probes@[c].hits@[j]]
                0 <= c < self.np() && 0 <= j < k && !probes@[c].hits@[j].1 ==> r@[probes@[c].hits@[j].0 as int / (self.per_c(c) as int)],
    {
        proof {
            self.lemma_view();
            self.lemma_shape();
        }
        let mut prot: Vec<bool> = vec![false; self.nslab];
        let ghost target = self@.attach_prot(toks@, k as nat);
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                self.valid(),
                probes@.len() == self.np(),
                forall|c2: int|
                    0 <= c2 < self.np() ==> probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks@, #[trigger] probes@[c2]) && k
                        <= probes@[c2].hits@.len(),
                target == self@.attach_prot(toks@, k as nat),
                c <= self.npaged,
                prot@.len() == self.nslab,
                forall|s: int|
                    0 <= s < self.nslab ==> #[trigger] prot@[s] == exists|c2: int, i: nat|
                        0 <= c2 < c && i < k && #[trigger] self@.prot_hit(toks@, c2, i, s),
                forall|c2: int, j: int|
                    #![trigger probes@[c2].hits@[j]]
                    0 <= c2 < c && 0 <= j < k && !probes@[c2].hits@[j].1 ==> prot@[probes@[c2].hits@[j].0 as int / (
                    self.per_c(c2) as int)],
            decreases self.npaged - c,
        {
            let pr = &probes[c];
            let p = self.per[c];
            proof {
                assert(self.paged@[c as int].valid());
                assert(self.unit@[c as int] >= 1);
                assert(self@.paged[c as int] == self.pv(c as int));
            }
            let mut i: usize = 0;
            let ghost prot_c = prot@;
            while i < k
                invariant
                    self.valid(),
                    probes@.len() == self.np(),
                    (c as nat) < self.np(),
                    pr == &probes@[c as int],
                    p as nat == self.per_c(c as int),
                    p >= 1,
                    self@.paged[c as int] == self.pv(c as int),
                    self.paged@[c as int].valid(),
                    probe_ok(self.pv(c as int), self.paged@[c as int].den_log(), toks@, *pr),
                    k <= pr.hits@.len(),
                    i <= k,
                    prot@.len() == self.nslab,
                    forall|s: int|
                        0 <= s < self.nslab ==> #[trigger] prot@[s] == (prot_c[s] || exists|i2: nat|
                            i2 < i && #[trigger] self@.prot_hit(toks@, c as int, i2, s)),
                    forall|j: int| #![trigger pr.hits@[j]] 0 <= j < i && !pr.hits@[j].1 ==> prot@[pr.hits@[j].0 as int / (p as int)],
                    forall|s: int| 0 <= s < self.nslab && #[trigger] prot_c[s] ==> prot@[s],
                    prot_c.len() == self.nslab,
                decreases k - i,
            {
                let (_x, act) = pr.hits[i];
                let ghost x = pr.hits@[i as int].0;
                let ghost key = self.pv(c as int).key_of(toks@, i as nat);
                proof {
                    assert(in_index(self.pv(c as int).keys, key, x));
                    assert(act == self.pv(c as int).has_active_hit(key));
                }
                let ghost pb = prot@;
                if !act {
                    let ki = &pr.keys[i];
                    let cands = self.paged[c].candidates(ki);
                    let mut q: usize = 0;
                    while q < cands.len()
                        invariant
                            self.valid(),
                            (c as nat) < self.np(),
                            p as nat == self.per_c(c as int),
                            p >= 1,
                            self@.paged[c as int] == self.pv(c as int),
                            self.paged@[c as int].valid(),
                            *ki == key,
                            forall|y: usize| #[trigger] cands@.contains(y) <==> in_index(self.pv(c as int).keys, key, y),
                            q <= cands@.len(),
                            prot@.len() == self.nslab,
                            forall|s: int| 0 <= s < self.nslab && #[trigger] pb[s] ==> prot@[s],
                            forall|s: int|
                                0 <= s < self.nslab && #[trigger] prot@[s] ==> pb[s] || exists|q2: int|
                                    0 <= q2 < q && cands@[q2] as int / (p as int) == s,
                            forall|q2: int| 0 <= q2 < q ==> prot@[#[trigger] cands@[q2] as int / (p as int)],
                        decreases cands@.len() - q,
                    {
                        let y = cands[q];
                        proof {
                            assert(cands@.contains(y));
                            assert(self.pv(c as int).p == self.cunits(c as int));
                            assert((y as nat) < self.pv(c as int).p);
                            lemma_div_bounds(y as nat, p as nat);
                            if (y / p) as nat >= self.nslab {
                                lemma_mul_mono(self.nslab as nat, (y / p) as nat, p as nat);
                            }
                        }
                        prot.set(y / p, true);
                        q += 1;
                    }
                    proof {
                        assert(cands@.contains(x));
                        let qx = choose|qx: int| 0 <= qx < cands@.len() && cands@[qx] == x;
                        assert(prot@[x as int / (p as int)]);
                        assert forall|s: int| 0 <= s < self.nslab implies #[trigger] prot@[s] == (pb[s] || self@.prot_hit(
                            toks@,
                            c as int,
                            i as nat,
                            s,
                        )) by {
                            if prot@[s] && !pb[s] {
                                let q2 = choose|q2: int| 0 <= q2 < cands@.len() && cands@[q2] as int / (p as int) == s;
                                assert(cands@.contains(cands@[q2]));
                                assert(in_index(self@.paged[c as int].keys, key, cands@[q2]));
                            }
                            if self@.prot_hit(toks@, c as int, i as nat, s) {
                                let y = choose|y: usize| #[trigger] in_index(self@.paged[c as int].keys, key, y) && y as int / (
                                self@.per[c as int] as int) == s;
                                assert(cands@.contains(y));
                                let q2 = choose|q2: int| 0 <= q2 < cands@.len() && cands@[q2] == y;
                                assert(prot@[cands@[q2] as int / (p as int)]);
                            }
                        }
                    }
                } else {
                    proof {
                        assert forall|s: int| 0 <= s < self.nslab implies !self@.prot_hit(toks@, c as int, i as nat, s) by {}
                    }
                }
                proof {
                    assert forall|j: int| #![trigger pr.hits@[j]] 0 <= j < i + 1 && !pr.hits@[j].1 implies prot@[pr.hits@[j].0 as int
                        / (p as int)] by {
                        if j < i {
                            let sj = pr.hits@[j].0 as int / (p as int);
                            assert(pb[sj]);
                            assert((pr.hits@[j].0 as nat) < self.pv(c as int).p) by {
                                assert(in_index(self.pv(c as int).keys, self.pv(c as int).key_of(toks@, j as nat), pr.hits@[j].0));
                            }
                            lemma_div_bounds(pr.hits@[j].0 as nat, p as nat);
                            if sj >= self.nslab {
                                lemma_mul_mono(self.nslab as nat, sj as nat, p as nat);
                            }
                        } else {
                            assert(j == i);
                        }
                    }
                    assert forall|s: int| 0 <= s < self.nslab && #[trigger] prot_c[s] implies prot@[s] by {
                        assert(pb[s]);
                    }
                    assert forall|s: int|
                        0 <= s < self.nslab implies #[trigger] prot@[s] == (prot_c[s] || exists|i2: nat|
                        i2 < i + 1 && #[trigger] self@.prot_hit(toks@, c as int, i2, s)) by {
                        if exists|i2: nat| i2 < i + 1 && #[trigger] self@.prot_hit(toks@, c as int, i2, s) {
                            let i2 = choose|i2: nat| i2 < i + 1 && #[trigger] self@.prot_hit(toks@, c as int, i2, s);
                            if i2 < i {
                                assert(pb[s]);
                            }
                        }
                        if pb[s] && !prot_c[s] {
                            assert(exists|i2: nat| i2 < i && #[trigger] self@.prot_hit(toks@, c as int, i2, s));
                            let i2 = choose|i2: nat| i2 < i && #[trigger] self@.prot_hit(toks@, c as int, i2, s);
                            assert(i2 < i + 1);
                        }
                        if prot@[s] && !pb[s] {
                            assert(self@.prot_hit(toks@, c as int, i as nat, s));
                        }
                    }
                }
                i += 1;
            }
            proof {
                assert forall|c2: int, j: int|
                    #![trigger probes@[c2].hits@[j]]
                    0 <= c2 < c + 1 && 0 <= j < k && !probes@[c2].hits@[j].1 implies prot@[probes@[c2].hits@[j].0 as int / (
                    self.per_c(c2) as int)] by {
                    if c2 < c {
                        let x = probes@[c2].hits@[j].0;
                        let p2 = self.per_c(c2);
                        assert(prot_c[x as int / (p2 as int)]);
                        assert(self.paged@[c2].valid());
                        assert(self.unit@[c2] >= 1);
                        assert(probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks@, probes@[c2]));
                        assert(in_index(self.pv(c2).keys, self.pv(c2).key_of(toks@, j as nat), x));
                        lemma_div_bounds(x as nat, p2);
                        if x as int / (p2 as int) >= self.nslab {
                            lemma_mul_mono(self.nslab as nat, (x as int / (p2 as int)) as nat, p2);
                        }
                    }
                }
                assert forall|s: int|
                    0 <= s < self.nslab implies #[trigger] prot@[s] == exists|c2: int, i2: nat|
                    0 <= c2 < c + 1 && i2 < k && #[trigger] self@.prot_hit(toks@, c2, i2, s) by {
                    if prot@[s] {
                        if prot_c[s] {
                            let (c2, i2) = choose|c2: int, i2: nat| 0 <= c2 < c && i2 < k && #[trigger] self@.prot_hit(toks@, c2, i2, s);
                            assert(0 <= c2 < c + 1 && i2 < k && self@.prot_hit(toks@, c2, i2, s));
                        } else {
                            let i2 = choose|i2: nat| i2 < k && #[trigger] self@.prot_hit(toks@, c as int, i2, s);
                            assert(0 <= c < c + 1 && i2 < k && self@.prot_hit(toks@, c as int, i2, s));
                        }
                    }
                    if exists|c2: int, i2: nat| 0 <= c2 < c + 1 && i2 < k && #[trigger] self@.prot_hit(toks@, c2, i2, s) {
                        let (c2, i2) = choose|c2: int, i2: nat| 0 <= c2 < c + 1 && i2 < k && #[trigger] self@.prot_hit(toks@, c2, i2, s);
                        if c2 < c {
                            assert(prot_c[s]);
                        } else {
                            assert(prot@[s]);
                        }
                    }
                }
            }
            c += 1;
        }
        proof {
            assert(prot@ =~= target);
        }
        prot
    }

    /// C1 demand vector `d`: `m - u_c` for paged classes, 1 for state classes.
    // `toks` is read only by the contract and the proof.
    #[allow(unused_variables)]
    pub(crate) fn attach_demand_exec(&self, toks: &[Token], probes: &Vec<Probe>, k: usize, m: usize) -> (r: Vec<usize>)
        requires
            self.valid(),
            probes@.len() == self.np(),
            forall|c: int|
                0 <= c < self.np() ==> probe_ok(self.pv(c), self.paged@[c].den_log(), toks@, #[trigger] probes@[c]) && k
                    <= probes@[c].hits@.len(),
            m as nat <= max_slots(),
            k <= m,
        ensures
            r@ == self@.attach_demand(toks@, m as nat, k as nat),
            r@.len() == self.ncls(),
            forall|c: int| 0 <= c < r@.len() ==> #[trigger] r@[c] <= max_slots(),
    {
        proof {
            self.lemma_view();
        }
        let mut d: Vec<usize> = Vec::new();
        let k_all = self.unit.len();
        let mut c: usize = 0;
        while c < k_all
            invariant
                self.valid(),
                k_all as nat == self.ncls(),
                probes@.len() == self.np(),
                forall|c2: int|
                    0 <= c2 < self.np() ==> probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks@, #[trigger] probes@[c2]) && k
                        <= probes@[c2].hits@.len(),
                m as nat <= max_slots(),
                k <= m,
                c <= k_all,
                d@.len() == c,
                forall|c2: int| 0 <= c2 < c ==> #[trigger] d@[c2] == self@.attach_demand(toks@, m as nat, k as nat)[c2],
                forall|c2: int| 0 <= c2 < c ==> #[trigger] d@[c2] <= max_slots(),
            decreases k_all - c,
        {
            if c < self.npaged {
                let hk = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(probes[c].hits.as_slice(), 0, k));
                let u = count_hits_active(&hk);
                proof {
                    let pr = probes@[c as int];
                    assert(hk@ =~= pr.hits@.subrange(0, k as int));
                    assert(hit_ok(self.pv(c as int), toks@, hk@)) by {
                        assert forall|j: int| #![trigger hk@[j]] 0 <= j < hk@.len() implies {
                            &&& in_index(self.pv(c as int).keys, self.pv(c as int).key_of(toks@, j as nat), hk@[j].0)
                            &&& hk@[j].1 == self.pv(c as int).has_active_hit(self.pv(c as int).key_of(toks@, j as nat))
                            &&& hk@[j].1 == (self.pv(c as int).refs[hk@[j].0 as int] > 0)
                        } by {
                            assert(hk@[j] == pr.hits@[j]);
                        }
                    }
                    lemma_n_active_eq(self.pv(c as int), toks@, hk@, k as nat);
                    assert(self@.paged[c as int] == self.pv(c as int));
                    assert(u <= k);
                }
                d.push((m - u) as usize);
            } else {
                d.push(1);
            }
            c += 1;
        }
        proof {
            assert(d@ =~= self@.attach_demand(toks@, m as nat, k as nat));
        }
        d
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


impl Coordinator {
    /// Commits the new lease in every paged class and takes a live slot in every state class.
    fn attach_commit_all(&mut self, toks: &[Token], tp: Vec<Probe>, Ghost(k): Ghost<nat>, Ghost(m): Ghost<nat>) -> (r: (
        usize,
        LeaseView,
    ))
        requires
            old(self).valid(),
            1 <= toks@.len(),
            m == cdiv(toks@.len(), old(self).b as nat),
            k + 1 <= m,
            m <= usize::MAX,
            old(self).nst() > 0 ==> k == 0,
            old(self)@.fits_m(m),
            old(self).next_handle() < u64::MAX,
            tp@.len() == old(self).np(),
            forall|c: int|
                0 <= c < old(self).np() ==> {
                    &&& probe_ok(old(self).pv(c), old(self).paged@[c].den_log(), toks@, #[trigger] tp@[c])
                    &&& tp@[c].hits@.len() == k
                    &&& old(self).pv(c).free_set().len() >= m - count_active(old(self).pv(c), toks@, k)
                },
            forall|j: int| 0 <= j < old(self).nst() ==> #[trigger] old(self).sv(j).free_set().len() >= 1,
        ensures
            final(self).valid(),
            r.0 as nat == k * (old(self).b as nat),
            r.1.tables@.len() == old(self).np(),
            r.1.slots@.len() == old(self).nst(),
            final(self).id == old(self).id,
            final(self).nslab == old(self).nslab,
            final(self).sbytes == old(self).sbytes,
            final(self).b == old(self).b,
            final(self).npaged == old(self).npaged,
            final(self).unit@ == old(self).unit@,
            final(self).per@ == old(self).per@,
            final(self).owner@ == old(self).owner@,
            final(self).paged@.len() == old(self).paged@.len(),
            final(self).state@.len() == old(self).state@.len(),
            final(self).slots@.dom() == old(self).slots@.dom().insert(old(self).next_handle()),
            final(self).slots@[old(self).next_handle()]@ == r.1.slots@,
            forall|h2: u64| #[trigger] old(self).slots@.contains_key(h2) ==> final(self).slots@[h2] == old(self).slots@[h2],
            forall|c: int|
                0 <= c < old(self).np() ==> {
                    &&& (#[trigger] r.1.tables@[c])@.len() == m
                    &&& attach_choice_k(old(self).pv(c), toks@, r.1.tables@[c]@, k)
                    &&& final(self).pv(c) == attached(old(self).pv(c), toks@, r.1.tables@[c]@, k)
                },
            forall|j: int|
                0 <= j < old(self).nst() ==> {
                    &&& old(self).sv(j).free_set().contains(#[trigger] r.1.slots@[j])
                    &&& final(self).sv(j) == (StateV {
                        holder: old(self).sv(j).holder.update(r.1.slots@[j] as int, Some(old(self).next_handle())),
                        w: old(self).sv(j).w.update(r.1.slots@[j] as int, None),
                        ..old(self).sv(j)
                    })
                },
    {
        let ghost mid = *self;
        let ghost h = mid.next_handle();
        let mut tables: Vec<Vec<PageId>> = Vec::new();
        let mut cached: usize = 0;
        proof {
            assert(self.paged@[0].valid());
        }
        let hid = self.paged[0].next_handle_exec();
        let mut c: usize = 0;
        proof {
            mid.lemma_view();
        }
        while c < self.npaged
            invariant
                mid.valid(),
                h == mid.next_handle(),
                h < u64::MAX,
                1 <= toks@.len(),
                m == cdiv(toks@.len(), mid.b as nat),
                k + 1 <= m,
                mid@.fits_m(m),
                self.npaged == mid.npaged,
                self.paged@.len() == mid.paged@.len(),
                self.state@ == mid.state@,
                self.slots@ == mid.slots@,
                self.b == mid.b,
                self.id == mid.id,
                self.nslab == mid.nslab,
                self.sbytes == mid.sbytes,
                self.unit@ == mid.unit@,
                self.per@ == mid.per@,
                self.owner@ == mid.owner@,
                self.fs == mid.fs,
                c <= self.npaged,
                tp@.len() == mid.np(),
                tables@.len() == c,
                c > 0 ==> cached as nat == k * (mid.b as nat),
                forall|c2: int|
                    c <= c2 < mid.np() ==> {
                        &&& probe_ok(mid.pv(c2), mid.paged@[c2].den_log(), toks@, #[trigger] tp@[c2])
                        &&& tp@[c2].hits@.len() == k
                        &&& mid.pv(c2).free_set().len() >= m - count_active(mid.pv(c2), toks@, k)
                        &&& self.paged@[c2] == mid.paged@[c2]
                    },
                forall|c2: int|
                    0 <= c2 < c ==> {
                        &&& (#[trigger] self.paged@[c2]).valid()
                        &&& tables@[c2]@.len() == m
                        &&& attach_choice_k(mid.pv(c2), toks@, tables@[c2]@, k)
                        &&& self.pv(c2) == attached(mid.pv(c2), toks@, tables@[c2]@, k)
                    },
            decreases self.npaged - c,
        {
            let pr = copy_probe(&tp[c]);
            proof {
                assert(self.paged@[c as int] == mid.paged@[c as int]);
                assert(mid.paged@[c as int].valid());
                lemma_probe_ok_views(mid.pv(c as int), mid.paged@[c as int].den_log(), toks@, tp@[c as int], pr);
                assert(mid.unit@[c as int] >= 1);
                lemma_fits_bound(mid.per@, mid.np(), mid.nst(), mid.nslab as nat, m, c as int);
                lemma_cdiv_props(toks@.len(), mid.b as nat);
                lemma_mul_mono(m, mid.cunits(c as int), mid.b as nat);
                assert(mid.pv(c as int).next_handle == h);
            }
            let ghost p0 = self.paged@;
            let (_hh, ch, view) = self.paged[c].attach_commit(toks, pr);
            proof {
                assert forall|c2: int| 0 <= c2 < self.paged@.len() && c2 != c implies #[trigger] self.paged@[c2] == p0[c2] by {}
            }
            cached = ch;
            tables.push(view.pages);
            proof {
                assert forall|c2: int|
                    0 <= c2 < c + 1 implies {
                    &&& (#[trigger] self.paged@[c2]).valid()
                    &&& tables@[c2]@.len() == m
                    &&& attach_choice_k(mid.pv(c2), toks@, tables@[c2]@, k)
                    &&& self.pv(c2) == attached(mid.pv(c2), toks@, tables@[c2]@, k)
                } by {
                    if c2 < c {
                        assert(self.paged@[c2] == p0[c2]);
                    }
                }
            }
            c += 1;
        }
        let ghost tabs = tables@;
        proof {
            assert forall|c2: int| 0 <= c2 < mid.np() implies (#[trigger] self.paged@[c2]).valid() && tabs[c2]@.len() == m
                && attach_choice_k(mid.pv(c2), toks@, tabs[c2]@, k) && self.pv(c2) == attached(mid.pv(c2), toks@, tabs[c2]@, k) by {
                assert(self.paged@[c2].valid());
            }
        }
        // State classes.
        let mut sl: Vec<usize> = Vec::new();
        let mut j: usize = 0;
        let ghost pg = self.paged@;
        while j < self.state.len()
            invariant
                mid.valid(),
                h == mid.next_handle(),
                self.state@.len() == mid.state@.len(),
                self.paged@ == pg,
                j <= self.state@.len(),
                sl@.len() == j,
                forall|j2: int| j <= j2 < mid.nst() ==> #[trigger] self.state@[j2] == mid.state@[j2],
                forall|j2: int| 0 <= j2 < mid.nst() ==> #[trigger] mid.sv(j2).free_set().len() >= 1,
                forall|j2: int|
                    0 <= j2 < j ==> {
                        &&& (#[trigger] self.state@[j2]).valid()
                        &&& mid.sv(j2).free_set().contains(sl@[j2])
                        &&& self.sv(j2) == (StateV {
                            holder: mid.sv(j2).holder.update(sl@[j2] as int, Some(h)),
                            w: mid.sv(j2).w.update(sl@[j2] as int, None),
                            ..mid.sv(j2)
                        })
                    },
            decreases self.state@.len() - j,
        {
            proof {
                assert(self.state@[j as int] == mid.state@[j as int]);
                assert(mid.state@[j as int].valid());
                mid.paged@[0].lemma_handles_lt();
                assert forall|y: int| 0 <= y < mid.sv(j as int).p implies #[trigger] mid.sv(j as int).holder[y] != Some(h) by {
                    if mid.sv(j as int).holder[y] == Some(h) {
                        assert(mid.slots@.contains_key(h));
                    }
                }
            }
            let ghost s0 = self.state@;
            let x = self.state[j].acquire(Ghost(h));
            proof {
                assert forall|j2: int| 0 <= j2 < s0.len() && j2 != j implies #[trigger] self.state@[j2] == s0[j2] by {}
            }
            sl.push(x);
            proof {
                assert forall|j2: int|
                    0 <= j2 < j + 1 implies {
                    &&& (#[trigger] self.state@[j2]).valid()
                    &&& mid.sv(j2).free_set().contains(sl@[j2])
                    &&& self.sv(j2) == (StateV {
                        holder: mid.sv(j2).holder.update(sl@[j2] as int, Some(h)),
                        w: mid.sv(j2).w.update(sl@[j2] as int, None),
                        ..mid.sv(j2)
                    })
                } by {
                    if j2 < j {
                        assert(self.state@[j2] == s0[j2]);
                    }
                }
            }
            j += 1;
        }
        proof {
            mid.paged@[0].lemma_handles_lt();
            assert(!mid.slots@.contains_key(h)) by {
                if mid.slots@.contains_key(h) {
                    assert(mid.pv(0).leases.contains_key(h));
                }
            }
        }
        let slv = vstd::slice::slice_to_vec(sl.as_slice());
        self.slots.insert(hid, slv);
        proof {
            assert(self.slots@.dom() =~= mid.slots@.dom().insert(h));
            let tv = tables@.map_values(|t: Vec<PageId>| t@);
            assert forall|c2: int| 0 <= c2 < mid.np() implies {
                &&& (#[trigger] self.paged@[c2]).valid()
                &&& attach_choice_k(mid.pv(c2), toks@, tv[c2], k)
                &&& self.pv(c2) == attached(mid.pv(c2), toks@, tv[c2], k)
            } by {
                assert(self.paged@[c2] == pg[c2]);
                assert(tv[c2] == tabs[c2]@);
            }
            assert forall|j2: int| 0 <= j2 < mid.nst() implies {
                &&& (#[trigger] self.state@[j2]).valid()
                &&& mid.sv(j2).free_set().contains(sl@[j2])
                &&& self.sv(j2) == (StateV {
                    holder: mid.sv(j2).holder.update(sl@[j2] as int, Some(h)),
                    w: mid.sv(j2).w.update(sl@[j2] as int, None),
                    ..mid.sv(j2)
                })
            } by {
                assert(self.state@[j2].valid());
            }
            self.lemma_attach_valid(&mid, toks@, k, h, tv, sl@);
            assert forall|c2: int| 0 <= c2 < mid.np() implies {
                &&& (#[trigger] tables@[c2])@.len() == m
                &&& attach_choice_k(mid.pv(c2), toks@, tables@[c2]@, k)
                &&& self.pv(c2) == attached(mid.pv(c2), toks@, tables@[c2]@, k)
            } by {
                assert(self.paged@[c2] == pg[c2]);
            }
        }
        let lv = LeaseView { tables, slots: sl };
        proof {
            assert forall|j2: int| 0 <= j2 < mid.nst() implies {
                &&& mid.sv(j2).free_set().contains(#[trigger] lv.slots@[j2])
                &&& self.sv(j2) == (StateV {
                    holder: mid.sv(j2).holder.update(lv.slots@[j2] as int, Some(h)),
                    w: mid.sv(j2).w.update(lv.slots@[j2] as int, None),
                    ..mid.sv(j2)
                })
            } by {
                assert(self.state@[j2].valid());
            }
        }
        (cached, lv)
    }
}


impl Coordinator {
    /// The run of every probe can be truncated to `k`, keeping `probe_ok`.
    fn truncate_all(&self, probes: Vec<Probe>, k: usize, Ghost(toks): Ghost<Seq<Token>>) -> (r: Vec<Probe>)
        requires
            self.valid(),
            probes@.len() == self.np(),
            forall|c: int|
                0 <= c < self.np() ==> probe_ok(self.pv(c), self.paged@[c].den_log(), toks, #[trigger] probes@[c]) && k
                    <= probes@[c].hits@.len(),
        ensures
            r@.len() == self.np(),
            forall|c: int|
                0 <= c < self.np() ==> probe_ok(self.pv(c), self.paged@[c].den_log(), toks, #[trigger] r@[c]) && r@[c].hits@
                    == probes@[c].hits@.subrange(0, k as int),
    {
        let mut out: Vec<Probe> = Vec::new();
        let mut c: usize = 0;
        while c < self.npaged
            invariant
                self.valid(),
                probes@.len() == self.np(),
                forall|c2: int|
                    0 <= c2 < self.np() ==> probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks, #[trigger] probes@[c2]) && k
                        <= probes@[c2].hits@.len(),
                c <= self.npaged,
                out@.len() == c,
                forall|c2: int|
                    0 <= c2 < c ==> probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks, #[trigger] out@[c2]) && out@[c2].hits@
                        == probes@[c2].hits@.subrange(0, k as int),
            decreases self.npaged - c,
        {
            proof {
                assert(self.paged@[c as int].valid());
            }
            let pr = copy_probe(&probes[c]);
            proof {
                lemma_probe_ok_views(self.pv(c as int), self.paged@[c as int].den_log(), toks, probes@[c as int], pr);
            }
            let t = self.paged[c].truncate_probe(pr, k, Ghost(toks));
            let ghost o0 = out@;
            out.push(t);
            proof {
                assert forall|c2: int| 0 <= c2 < c + 1 implies probe_ok(self.pv(c2), self.paged@[c2].den_log(), toks, #[trigger] out@[c2])
                    && out@[c2].hits@ == probes@[c2].hits@.subrange(0, k as int) by {
                    if c2 < c {
                        assert(out@[c2] == o0[c2]);
                    }
                }
            }
            c += 1;
        }
        out
    }

    proof fn lemma_coord_attached(
        o: &Coordinator,
        pre: &Coordinator,
        mid: &Coordinator,
        fin: &Coordinator,
        toks: Seq<Token>,
        k: nat,
        m: nat,
        tp: &Vec<Probe>,
        d: Seq<usize>,
        prot: Seq<bool>,
        view: &LeaseView,
    )
        requires
            o.valid(),
            pre.valid(),
            mid.valid(),
            o@ == pre@,
            forall|c: int| 0 <= c < o.np() ==> #[trigger] pre.pv(c) == o.pv(c),
            m == cdiv(toks.len(), o.b as nat),
            d == o@.attach_demand(toks, m, k),
            prot == o@.attach_prot(toks, k),
            mid@.plan_rel(pre@, d, prot),
            mid.slab_frame(pre, prot),
            tp@.len() == o.np(),
            forall|c: int|
                0 <= c < o.np() ==> probe_ok(pre.pv(c), pre.paged@[c].den_log(), toks, #[trigger] tp@[c])
                    && tp@[c].hits@.len() == k,
            fin.valid(),
            fin.id == mid.id,
            fin.nslab == mid.nslab,
            fin.sbytes == mid.sbytes,
            fin.b == mid.b,
            fin.npaged == mid.npaged,
            fin.unit@ == mid.unit@,
            fin.per@ == mid.per@,
            fin.owner@ == mid.owner@,
            fin.paged@.len() == mid.paged@.len(),
            fin.state@.len() == mid.state@.len(),
            view.tables@.len() == mid.np(),
            view.slots@.len() == mid.nst(),
            fin.slots@.dom() == mid.slots@.dom().insert(mid.next_handle()),
            fin.slots@[mid.next_handle()]@ == view.slots@,
            forall|h2: u64| #[trigger] mid.slots@.contains_key(h2) ==> fin.slots@[h2] == mid.slots@[h2],
            mid.next_handle() == o.next_handle(),
            forall|c: int|
                0 <= c < mid.np() ==> {
                    &&& (#[trigger] view.tables@[c])@.len() == m
                    &&& attach_choice_k(mid.pv(c), toks, view.tables@[c]@, k)
                    &&& fin.pv(c) == attached(mid.pv(c), toks, view.tables@[c]@, k)
                },
            forall|j: int|
                0 <= j < mid.nst() ==> {
                    &&& mid.sv(j).free_set().contains(#[trigger] view.slots@[j])
                    &&& fin.sv(j) == (StateV {
                        holder: mid.sv(j).holder.update(view.slots@[j] as int, Some(mid.next_handle())),
                        w: mid.sv(j).w.update(view.slots@[j] as int, None),
                        ..mid.sv(j)
                    })
                },
        ensures
            coord_attached(o@, mid@, fin@, toks, k, tables_view(view.tables@), view.slots@),
    {
        let ov = o@;
        let tabs = tables_view(view.tables@);
        mid.lemma_view();
        fin.lemma_view();
        o.lemma_view();
        pre.lemma_view();
        let h = ov.next_handle();
        assert(fin@.slots =~= mid@.slots.insert(h, view.slots@)) by {
            assert forall|h2: u64| #[trigger] fin@.slots.contains_key(h2) implies fin@.slots[h2] == mid@.slots.insert(
                h,
                view.slots@,
            )[h2] by {
                if h2 != h {
                    assert(mid.slots@.contains_key(h2));
                }
            }
        }
        assert forall|c: int| 0 <= c < ov.np implies {
            &&& (#[trigger] tabs[c]).len() == m
            &&& attach_choice_k(mid@.paged[c], toks, tabs[c], k)
            &&& fin@.paged[c] == attached(mid@.paged[c], toks, tabs[c], k)
            &&& forall|i: int|
                #![trigger tabs[c][i]]
                0 <= i < k ==> in_index(ov.paged[c].keys, ov.paged[c].key_of(toks, i as nat), tabs[c][i]) && (
                ov.paged[c].has_active_hit(ov.paged[c].key_of(toks, i as nat)) ==> ov.paged[c].refs[tabs[c][i] as int] > 0)
        } by {
            assert(tabs[c] == view.tables@[c]@);
            let t = tabs[c];
            assert(ov.paged[c] == pre.pv(c));
            assert(mid@.paged[c] == mid.pv(c));
            assert(mid.paged@[c] == mid.paged@[c]);
            assert(mid.pv(c) == (MgrV { own: mid.pv(c).own, keys: mid.pv(c).keys, ..pre.pv(c) }));
            assert(mid.paged@[c].valid());
            assert(pre.paged@[c].valid());
            assert forall|i: int| #![trigger t[i]] 0 <= i < k implies in_index(ov.paged[c].keys, ov.paged[c].key_of(toks, i as nat), t[i])
                && (ov.paged[c].has_active_hit(ov.paged[c].key_of(toks, i as nat)) ==> ov.paged[c].refs[t[i] as int] > 0) by {
                let key = pre.pv(c).key_of(toks, i as nat);
                assert(attach_choice_k(mid.pv(c), toks, t, k));
                assert(mid.pv(c).key_of(toks, i as nat) == key);
                assert(in_index(mid.pv(c).keys, key, t[i]));
                let x = t[i];
                assert(mid.pv(c).keys[x as int] == pre.pv(c).keys[x as int] || (mid.pv(c).keys[x as int] is None
                    && pre.pv(c).refs[x as int] == 0 && !prot[x as int / (mid.per_c(c) as int)]));
                assert(in_index(pre.pv(c).keys, key, x));
                if pre.pv(c).has_active_hit(key) {
                    let y = choose|y: PageId| #[trigger] in_index(pre.pv(c).keys, key, y) && pre.pv(c).refs[y as int] > 0;
                    assert(mid.pv(c).keys[y as int] == pre.pv(c).keys[y as int] || (mid.pv(c).keys[y as int] is None
                        && pre.pv(c).refs[y as int] == 0 && !prot[y as int / (mid.per_c(c) as int)]));
                    assert(in_index(mid.pv(c).keys, key, y));
                    assert(mid.pv(c).has_active_hit(key));
                }
            }
        }
        assert forall|j: int| 0 <= j < ov.nst() implies {
            &&& mid@.state[j].free_set().contains(#[trigger] view.slots@[j])
            &&& fin@.state[j] == (StateV {
                holder: mid@.state[j].holder.update(view.slots@[j] as int, Some(h)),
                w: mid@.state[j].w.update(view.slots@[j] as int, None),
                ..mid@.state[j]
            })
        } by {
            assert(mid@.state[j] == mid.sv(j));
            assert(fin@.state[j] == fin.sv(j));
        }
        assert(tabs.len() == ov.np);
    }

    /// C1. `attach(T)` across every class (contract v0.3 §6 C1).
    pub fn attach(&mut self, toks: &[Token]) -> (r: Result<(Handle, usize, LeaseView), Error>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            coord_attach_result(old(self)@, final(self)@, toks@, r),
    {
        let ghost o = *self;
        let ghost ov = o@;
        let n = toks.len();
        if n == 0 {
            return Err(Error::InvalidArgument);
        }
        let b = self.b;
        proof {
            self.lemma_view();
            self.lemma_shape();
        }
        let m = (n - 1) / b + 1;
        proof {
            vstd::arithmetic::div_mod::lemma_div_plus_one((n - 1) as int, b as int);
            assert(((n - 1 + b) as int) / (b as int) == ((n - 1) as int) / (b as int) + 1);
            assert(m as nat == cdiv(n as nat, b as nat));
        }
        if !self.fits_exec(m) {
            return Err(Error::RequestTooLarge);
        }
        proof {
            self.paged@[0].lemma_valid();
            assert(self.paged@[0].valid());
        }
        let hid = self.paged[0].next_handle_exec();
        if hid == u64::MAX {
            return Err(Error::IdentifierExhausted);
        }
        proof {
            lemma_cdiv_props(n as nat, b as nat);
            assert(m >= 1);
            lemma_fits_bound(self.per@, self.np(), self.nst(), self.nslab as nat, m as nat, 0);
            self.lemma_nslab_bound();
            assert(self.unit@[0] >= 1);
            assert((m as nat) <= self.cunits(0));
        }
        let cap = if self.state.len() > 0 { 0 } else { m - 1 };
        let (probes, kmin) = self.joint_probe(toks, cap);
        let ghost s1 = *self;
        proof {
            self.lemma_joint_k(toks@, m as nat, cap as nat, probes@, kmin as nat);
        }
        let tp = self.truncate_all(probes, kmin, Ghost(toks@));
        let prot = self.compute_prot(toks, &tp, kmin);
        proof {
            assert forall|c: int| 0 <= c < self.np() implies probe_ok(self.pv(c), self.paged@[c].den_log(), toks@, #[trigger] tp@[c])
                && kmin <= tp@[c].hits@.len() by {}
            self.lemma_nslab_bound();
            assert((m as nat) <= max_slots());
        }
        let d = self.attach_demand_exec(toks, &tp, kmin, m);
        if !self.check_cap(&d, &prot) {
            proof {
                assert(ov.joint_k(toks@, m as nat, kmin as nat));
                assert(!ov.cap(ov.attach_demand(toks@, m as nat, kmin as nat), ov.attach_prot(toks@, kmin as nat)));
            }
            return Err(Error::NoCapacity);
        }
        let ghost pre = *self;
        self.run_plan(&d, &prot);
        let ghost mid = *self;
        proof {
            // Probes stay valid; every class has room for its share of the lease.
            assert forall|c: int| 0 <= c < pre.np() implies {
                &&& probe_ok(mid.pv(c), mid.paged@[c].den_log(), toks@, #[trigger] tp@[c])
                &&& tp@[c].hits@.len() == kmin
                &&& mid.pv(c).free_set().len() >= m - count_active(mid.pv(c), toks@, kmin as nat)
            } by {
                assert(tp@[c].hits@.len() == kmin);
                mid.lemma_commit_pre(&pre, toks@, tp@, kmin as nat, m as nat, d@, prot@, c);
            }
            mid.lemma_view();
            mid.lemma_view_cls();
            assert forall|j: int| 0 <= j < mid.nst() implies #[trigger] mid.sv(j).free_set().len() >= 1 by {
                assert(mid@.cfree(mid.np() + j) >= d@[mid.np() + j]);
                assert(mid@.state[j] == mid.sv(j));
            }
            assert(mid.paged@[0] == mid.paged@[0]);
            assert(mid.next_handle() == o.next_handle());
            assert(mid@.fits_m(m as nat));
        }
        let (cached, view) = self.attach_commit_all(toks, tp, Ghost(kmin as nat), Ghost(m as nat));
        proof {
            self.lemma_view();
            o.lemma_view();
            pre.lemma_view();
            assert forall|c: int| 0 <= c < o.np() implies #[trigger] pre.pv(c) == o.pv(c) by {
                assert(pre@.paged[c] == o@.paged[c]);
            }
            Self::lemma_coord_attached(&o, &pre, &mid, self, toks@, kmin as nat, m as nat, &tp, d@, prot@, &view);
            assert((cached as nat) / ov.b == kmin as nat) by {
                lemma_slot_decomp(kmin as nat, 0, ov.b);
            }
        }
        proof {
            assert(hid == ov.next_handle()) by {
                assert(o.paged@[0] == o.paged@[0]);
                o.lemma_view();
            }
            assert(self.id == ov.id) by {
                o.lemma_view();
            }
            assert(ov.joint_k(toks@, m as nat, kmin as nat));
            assert(ov.cap(ov.attach_demand(toks@, m as nat, kmin as nat), ov.attach_prot(toks@, kmin as nat)));
            assert(ov.fits_m(m as nat));
            assert(cached as nat == kmin * ov.b) by {
                o.lemma_view();
            }
            assert(m as nat == cdiv(toks@.len(), ov.b)) by {
                o.lemma_view();
            }
            let midv = mid@;
            assert(coord_attached(ov, midv, self@, toks@, kmin as nat, tables_view(view.tables@), view.slots@));
            assert(ov == old(self)@);
            lemma_attach_ok(ov, midv, self@, toks@, kmin as nat, Handle { mgr: self.id, id: hid }, cached, view);
        }
        Ok((Handle { mgr: self.id, id: hid }, cached, view))
    }
}

} // verus!
