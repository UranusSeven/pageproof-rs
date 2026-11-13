//! v0.3 coordinator (contract §1, §3.5, D10–D15): one slab arena shared by paged classes (each a
//! verified `Manager` over `N·n_c` units) and state classes (each a `StatePool`). The coordinator
//! owns slab ownership and makes every public operation all-or-nothing across classes. Paged
//! classes run in lockstep: they hold the same leases (ids, inputs, frontier, pending ticket) and
//! the same tickets, so one coordinator handle/ticket id names the same lease/ticket in every
//! class. No trusted content.
use vstd::prelude::*;
use std::collections::HashMap;
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::arith::*;
use crate::manager::*;
use crate::idxset::IdxSet;
use crate::state::*;
use crate::ops_slab::*;
use crate::cnt::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// `Σ_{i<k} ceil(m / n_i)` over the paged classes.
pub open spec fn psum(per: Seq<usize>, k: int, m: nat) -> nat
    decreases k,
{
    if k <= 0 {
        0
    } else {
        psum(per, k - 1, m) + cdiv(m, per[k - 1] as nat)
    }
}

/// The configuration every paged class of a coordinator shares (§3.1, D18, D20, D21):
/// `μ = (δ + 1)·λ`, plus `λ` when there are drafter classes `[ntarget, np)`.
pub open spec fn cfg_rel(c: PCfg, np: nat) -> bool {
    &&& 1 <= c.ntarget <= np
    &&& c.lam <= max_slots()
    &&& c.delta <= 1
    &&& c.mu == (if c.delta == 1 { c.lam + c.lam } else { c.lam }) + (if c.ntarget < np { c.lam } else { 0 })
}

/// The configuration checks `create` makes before it builds anything (C0).
pub open spec fn create_early_ok(pu: Seq<usize>, du: Seq<usize>, lambda: nat, delta: nat) -> bool {
    &&& pu.len() >= 1
    &&& du.len() > 0 ==> lambda > 0
    &&& delta == 0
    &&& lambda <= max_slots()
    &&& create_mu(lambda, du.len()) <= max_slots()
}

/// `μ` of a configuration with `nd` drafter classes and δ = 0 (D18).
pub open spec fn create_mu(lambda: nat, nd: nat) -> nat {
    if nd > 0 { lambda + lambda } else { lambda }
}

/// `n_c = S / u_c` for every class.
pub open spec fn per_of(sbytes: nat, units: Seq<usize>) -> Seq<usize> {
    Seq::new(units.len(), |c: int| (sbytes / (units[c] as nat)) as usize)
}

/// `Fits(m)` of §3.1: a lease of `m` blocks fits in an otherwise empty arena.
pub open spec fn fits(per: Seq<usize>, np: nat, nstate: nat, nslab: nat, m: nat) -> bool {
    psum(per, np as int, m) + nstate <= nslab
}

/// `psum` is monotone in the block count.
pub proof fn lemma_psum_mono(per: Seq<usize>, k: int, m1: nat, m2: nat)
    requires
        m1 <= m2,
        forall|i: int| 0 <= i < k ==> #[trigger] per[i] >= 1,
    ensures
        psum(per, k, m1) <= psum(per, k, m2),
    decreases k,
{
    if k > 0 {
        lemma_psum_mono(per, k - 1, m1, m2);
        lemma_cdiv_mono(m1, m2, per[k - 1] as nat);
    }
}

/// `Fits` is monotone: a smaller lease fits whenever a larger one does.
pub proof fn lemma_fits_mono(per: Seq<usize>, np: nat, nstate: nat, nslab: nat, m1: nat, m2: nat)
    requires
        m1 <= m2,
        fits(per, np, nstate, nslab, m2),
        forall|i: int| 0 <= i < np ==> #[trigger] per[i] >= 1,
    ensures
        fits(per, np, nstate, nslab, m1),
{
    lemma_psum_mono(per, np as int, m1, m2);
}

pub proof fn lemma_psum_ge(per: Seq<usize>, k: int, m: nat, i: int)
    requires
        0 <= i < k,
    ensures
        psum(per, k, m) >= cdiv(m, per[i] as nat),
    decreases k,
{
    if i < k - 1 {
        lemma_psum_ge(per, k - 1, m, i);
    }
}

/// `Fits(m)` bounds `m` by every paged class's unit count.
pub proof fn lemma_fits_bound(per: Seq<usize>, np: nat, nstate: nat, nslab: nat, m: nat, i: int)
    requires
        fits(per, np, nstate, nslab, m),
        0 <= i < np,
        per[i] >= 1,
    ensures
        m <= nslab * (per[i] as nat),
        cdiv(m, per[i] as nat) <= nslab,
{
    lemma_psum_ge(per, np as int, m, i);
    lemma_cdiv_props(m, per[i] as nat);
    lemma_mul_mono(cdiv(m, per[i] as nat), nslab, per[i] as nat);
}

/// `x` lies in slab `s` of a class with `n` units per slab iff `x / n == s`.
pub proof fn lemma_slab_of(x: int, n: nat, s: nat)
    requires
        n > 0,
        x >= 0,
    ensures
        in_range(x, s * n, n) <==> x / (n as int) == s,
{
    lemma_div_bounds(x as nat, n);
    if in_range(x, s * n, n) {
        lemma_mul_succ(s, n);
        lemma_div_unique(x as nat, n, s);
    }
    if x / (n as int) == s {
        lemma_mul_succ(s, n);
    }
}

/// The public abstract state of a coordinator (contract §3.2), for client reasoning.
pub ghost struct CoordV {
    pub id: u64,
    pub nslab: nat,
    pub sbytes: nat,
    pub b: nat,
    /// `u_c` of every class, paged classes first.
    pub unit: Seq<usize>,
    pub per: Seq<usize>,
    pub np: nat,
    /// `owner[s]`: 0 is `Free`, `c + 1` is class `c`.
    pub owner: Seq<usize>,
    /// Paged classes (lockstep leases; class 0 is the reference copy).
    pub paged: Seq<MgrV>,
    pub state: Seq<StateV>,
    /// `σ_h^c` for each lease and state class.
    pub slots: Map<u64, Seq<usize>>,
}

impl CoordV {
    pub open spec fn ncls(self) -> nat {
        self.unit.len()
    }

    pub open spec fn nst(self) -> nat {
        self.state.len()
    }

    pub open spec fn leases(self) -> Map<u64, LeaseV> {
        self.paged[0].leases
    }

    pub open spec fn pend(self) -> Map<u64, PendV> {
        self.paged[0].pend
    }

    pub open spec fn next_handle(self) -> u64 {
        self.paged[0].next_handle
    }

    pub open spec fn next_ticket(self) -> u64 {
        self.paged[0].next_ticket
    }

    pub open spec fn fits_m(self, m: nat) -> bool {
        fits(self.per, self.np, self.nst(), self.nslab, m)
    }

    /// The shared configuration (I10): `μ`, `λ`, `δ` and the number of target classes.
    pub open spec fn mu(self) -> nat {
        self.paged[0].cfg.mu
    }

    pub open spec fn lam(self) -> nat {
        self.paged[0].cfg.lam
    }

    pub open spec fn delta(self) -> nat {
        self.paged[0].cfg.delta
    }

    pub open spec fn ntarget(self) -> nat {
        self.paged[0].cfg.ntarget
    }

    /// The extra write range of paged class `c` in a plan with `propose`: `λ` proposal rows in a
    /// drafter class (D20), none otherwise.
    pub open spec fn ext_of(self, c: int, propose: bool) -> nat {
        if propose && c >= self.ntarget() { self.lam() } else { 0 }
    }

    /// Blocks covering the reach `L + μ` of an input of length `L` (D18).
    pub open spec fn reach_blocks(self, l: nat) -> nat {
        cdiv(l + self.mu(), self.b)
    }

    /// `FS`.
    pub open spec fn free_slabs(self) -> Set<usize> {
        Set::<usize>::range(0, self.nslab as usize).filter(|s: usize| self.owner[s as int] == 0)
    }

    pub open spec fn per_c(self, c: int) -> nat {
        self.per[c] as nat
    }

    /// `|F_c|`.
    pub open spec fn cfree(self, c: int) -> nat {
        if c < self.np {
            self.paged[c].free_set().len()
        } else {
            self.state[c - self.np].free_set().len()
        }
    }

    /// Unit `x` of class `c` is owned and unreferenced.
    pub open spec fn cidle(self, c: int, x: int) -> bool {
        if c < self.np {
            self.paged[c].own[x] && self.paged[c].refs[x] == 0
        } else {
            self.state[c - self.np].own[x] && self.state[c - self.np].holder[x] is None
        }
    }

    /// Every unit of slab `s` of class `c` is owned and unreferenced.
    pub open spec fn slab_idle(self, c: int, s: nat) -> bool {
        forall|x: int| #[trigger] in_range(x, s * self.per_c(c), self.per_c(c)) ==> self.cidle(c, x)
    }

    pub open spec fn fpred(self) -> spec_fn(int) -> bool {
        |s: int| self.owner[s] == 0
    }

    pub open spec fn rpred(self, c: int, prot: Seq<bool>) -> spec_fn(int) -> bool {
        |s: int| self.reclaimable(c, prot, s)
    }

    /// `|FS|`: the number of free slabs.
    pub open spec fn fcount(self) -> nat {
        cnt(self.nslab as int, self.fpred())
    }

    /// Slab `s` is reclaimable from class `c` outside `prot` (a member of `R_c`, §3.5).
    pub open spec fn reclaimable(self, c: int, prot: Seq<bool>, s: int) -> bool {
        self.owner[s] == c + 1 && !prot[s] && self.slab_idle(c, s as nat)
    }

    /// `|R_c|`.
    pub open spec fn rcount(self, c: int, prot: Seq<bool>) -> nat {
        cnt(self.nslab as int, self.rpred(c, prot))
    }

    /// `need_c`.
    pub open spec fn need(self, c: int, d: nat) -> nat {
        if d <= self.cfree(c) {
            0
        } else {
            cdiv((d - self.cfree(c)) as nat, self.per_c(c))
        }
    }

    /// `give_c`.
    pub open spec fn give(self, c: int, d: nat, prot: Seq<bool>) -> nat {
        if self.cfree(c) >= d {
            let lim = ((self.cfree(c) - d) as nat) / self.per_c(c);
            let r = self.rcount(c, prot);
            if r <= lim {
                r
            } else {
                lim
            }
        } else {
            0
        }
    }

    pub open spec fn needf(self, d: Seq<usize>) -> spec_fn(int) -> nat {
        |c: int| self.need(c, d[c] as nat)
    }

    pub open spec fn givef(self, d: Seq<usize>, prot: Seq<bool>) -> spec_fn(int) -> nat {
        |c: int| self.give(c, d[c] as nat, prot)
    }

    /// `Σ_c need_c`.
    pub open spec fn sum_need(self, d: Seq<usize>) -> nat {
        nsum(self.ncls() as int, self.needf(d))
    }

    /// `Σ_c give_c`.
    pub open spec fn sum_give(self, d: Seq<usize>, prot: Seq<bool>) -> nat {
        nsum(self.ncls() as int, self.givef(d, prot))
    }

    /// `Cap(d, Prot)` of §3.5.
    pub open spec fn cap(self, d: Seq<usize>, prot: Seq<bool>) -> bool {
        self.sum_need(d) <= self.fcount() + self.sum_give(d, prot)
    }

    /// Slabs class `c` gained since `o` / lost since `o`.
    pub open spec fn gpred(self, o: CoordV, c: int) -> spec_fn(int) -> bool {
        |s: int| self.owner[s] == c + 1 && o.owner[s] != c + 1
    }

    pub open spec fn lpred(self, o: CoordV, c: int) -> spec_fn(int) -> bool {
        |s: int| o.owner[s] == c + 1 && self.owner[s] != c + 1
    }

    /// Slabs class `c` gained since `o`.
    pub open spec fn gained(self, o: CoordV, c: int) -> nat {
        cnt(self.nslab as int, self.gpred(o, c))
    }

    /// Slabs class `c` lost since `o`.
    pub open spec fn lost(self, o: CoordV, c: int) -> nat {
        cnt(self.nslab as int, self.lpred(o, c))
    }

    pub open spec fn lostf(self, o: CoordV) -> spec_fn(int) -> nat {
        |c: int| self.lost(o, c)
    }

    pub open spec fn gainedf(self, o: CoordV) -> spec_fn(int) -> nat {
        |c: int| self.gained(o, c)
    }

    /// `self` is `o` after the slab plan of §3.5 for demand `d` and protection `prot`:
    /// - leases, references, tickets and slots are unchanged; pools differ only in ownership, in
    ///   keys revoked on slabs that changed owner, and in the provenance of free state units;
    /// - every slab that changed owner was free, or idle and unprotected, in `o`; keys were
    ///   revoked only on unreferenced pages of unprotected slabs;
    /// - class `c` gained exactly `need_c` slabs and lost at most `give_c`;
    /// - slabs were reclaimed only when free slabs did not suffice: exactly
    ///   `max(0, Σ need - |FS|)` of them;
    /// - every class now has at least `d_c` free units.
    pub open spec fn plan_rel(self, o: CoordV, d: Seq<usize>, prot: Seq<bool>) -> bool {
        let tot = o.sum_need(d);
        &&& self.id == o.id
        &&& self.b == o.b
        &&& self.sbytes == o.sbytes
        &&& self.nslab == o.nslab
        &&& self.per == o.per
        &&& self.unit == o.unit
        &&& self.np == o.np
        &&& self.paged.len() == o.paged.len()
        &&& self.state.len() == o.state.len()
        &&& self.owner.len() == o.owner.len()
        &&& self.slots == o.slots
        &&& forall|i: int|
            0 <= i < o.paged.len() ==> #[trigger] self.paged[i] == (MgrV {
                own: self.paged[i].own,
                keys: self.paged[i].keys,
                ..o.paged[i]
            })
        &&& forall|j: int|
            0 <= j < o.state.len() ==> #[trigger] self.state[j] == (StateV {
                own: self.state[j].own,
                w: self.state[j].w,
                ..o.state[j]
            })
        &&& forall|j: int, x: int|
            0 <= j < o.state.len() && 0 <= x < o.state[j].p && o.state[j].holder[x] is Some ==> #[trigger] self.state[j].w[x]
                == o.state[j].w[x]
        &&& forall|i: int, x: int|
            0 <= i < o.paged.len() && 0 <= x < o.paged[i].p ==> #[trigger] self.paged[i].keys[x] == o.paged[i].keys[x] || (
            self.paged[i].keys[x] is None && o.paged[i].refs[x] == 0 && !prot[x / (o.per[i] as int)])
        &&& forall|s: int|
            0 <= s < o.nslab && #[trigger] self.owner[s] != o.owner[s] ==> o.owner[s] == 0 || (!prot[s] && o.slab_idle(
                o.owner[s] - 1,
                s as nat,
            ))
        &&& forall|c: int| 0 <= c < o.ncls() ==> #[trigger] self.gained(o, c) == o.need(c, d[c] as nat) && self.lost(o, c)
            <= o.give(c, d[c] as nat, prot)
        &&& nsum(o.ncls() as int, self.lostf(o)) == if tot > o.fcount() { (tot - o.fcount()) as nat } else { 0nat }
        &&& forall|c: int| 0 <= c < o.ncls() ==> #[trigger] self.cfree(c) >= d[c]
    }

    /// The joint `k*` of C1.
    pub open spec fn joint_k(self, toks: Seq<Token>, m: nat, k: nat) -> bool {
        &&& k + 1 <= m
        &&& self.nst() > 0 ==> k == 0
        &&& self.nst() == 0 ==> {
            &&& forall|c: int, i: nat| 0 <= c < self.np && i < k ==> #[trigger] self.paged[c].has_hit(
                self.paged[c].key_of(toks, i),
            )
            &&& k + 1 < m ==> exists|c: int| 0 <= c < self.np && !#[trigger] self.paged[c].has_hit(
                self.paged[c].key_of(toks, k),
            )
        }
    }

    /// C1 demand `d_c`: `m - u_c` for paged classes, 1 for state classes.
    pub open spec fn attach_demand(self, toks: Seq<Token>, m: nat, k: nat) -> Seq<usize> {
        Seq::new(
            self.ncls(),
            |c: int| if c < self.np { (m - count_active(self.paged[c], toks, k)) as usize } else { 1usize },
        )
    }

    /// Hit position `i` of class `c` has no active candidate, and some candidate lies in slab `s`.
    pub open spec fn prot_hit(self, toks: Seq<Token>, c: int, i: nat, s: int) -> bool {
        let key = self.paged[c].key_of(toks, i);
        &&& !self.paged[c].has_active_hit(key)
        &&& exists|x: usize| #[trigger] crate::index::in_index(self.paged[c].keys, key, x) && x as int / (self.per[c] as int) == s
    }

    /// C1 `Prot`: slabs of the free candidates of hit positions `i < k*` (§6 C1).
    pub open spec fn attach_prot(self, toks: Seq<Token>, k: nat) -> Seq<bool> {
        Seq::new(
            self.nslab,
            |s: int| exists|c: int, i: nat| 0 <= c < self.np && i < k && #[trigger] self.prot_hit(toks, c, i, s),
        )
    }
}

pub struct Coordinator {
    pub(crate) id: u64,
    pub(crate) nslab: usize,
    pub(crate) sbytes: usize,
    pub(crate) b: usize,
    pub(crate) npaged: usize,
    /// `u_c` for every class: paged classes first, then state classes.
    pub(crate) unit: Vec<usize>,
    /// `n_c = S / u_c`.
    pub(crate) per: Vec<usize>,
    /// `owner[s]`: 0 is `Free`, `c + 1` is class `c`.
    pub(crate) owner: Vec<usize>,
    /// `FS`.
    pub(crate) fs: IdxSet,
    pub(crate) paged: Vec<Manager>,
    pub(crate) state: Vec<StatePool>,
    /// Live state slots `σ_h^c` of every lease, one per state class.
    pub(crate) slots: HashMap<u64, Vec<usize>>,
}

impl Coordinator {
    /// Public view.
    pub open(crate) spec fn view(&self) -> CoordV {
        CoordV {
            id: self.id,
            nslab: self.nslab as nat,
            sbytes: self.sbytes as nat,
            b: self.b as nat,
            unit: self.unit@,
            per: self.per@,
            np: self.npaged as nat,
            owner: self.owner@,
            paged: Seq::new(self.paged@.len(), |i: int| self.paged@[i]@),
            state: Seq::new(self.state@.len(), |j: int| self.state@[j]@),
            slots: self.slots@.map_values(|v: Vec<usize>| v@),
        }
    }

    /// Public validity.
    pub open(crate) spec fn inv(&self) -> bool {
        self.valid()
    }

    /// The public view agrees with the internal accessors.
    pub(crate) proof fn lemma_view(&self)
        ensures
            self@.paged.len() == self.paged@.len(),
            self@.state.len() == self.state@.len(),
            forall|i: int| 0 <= i < self.paged@.len() ==> #[trigger] self@.paged[i] == self.pv(i),
            forall|j: int| 0 <= j < self.state@.len() ==> #[trigger] self@.state[j] == self.sv(j),
            self@.owner == self.owner@,
            self@.per == self.per@,
            self@.unit == self.unit@,
            self@.np == self.np(),
            self@.nslab == self.nslab as nat,
            self@.b == self.b as nat,
            self@.id == self.id,
            self@.slots.dom() == self.slots@.dom(),
            forall|h: u64| #[trigger] self.slots@.contains_key(h) ==> self@.slots[h] == self.slots@[h]@,
    {
    }

    pub(crate) proof fn lemma_view_cls(&self)
        requires
            self.cfg_ok(),
        ensures
            forall|c: int| 0 <= c < self.ncls() ==> #[trigger] self@.cfree(c) == self.cfree(c),
            forall|c: int, x: int| 0 <= c < self.ncls() ==> #[trigger] self@.cidle(c, x) == self.cidle(c, x),
            forall|c: int, s: nat| 0 <= c < self.ncls() ==> #[trigger] self@.slab_idle(c, s) == self.slab_idle(c, s),
    {
        self.lemma_view();
        assert forall|c: int| 0 <= c < self.ncls() implies #[trigger] self@.cfree(c) == self.cfree(c) by {
            if c >= self.np() {
                assert(self@.state[c - self.np()] == self.sv(c - self.np()));
            } else {
                assert(self@.paged[c] == self.pv(c));
            }
        }
        assert forall|c: int, x: int| 0 <= c < self.ncls() implies #[trigger] self@.cidle(c, x) == self.cidle(c, x) by {
            if c >= self.np() {
                assert(self@.state[c - self.np()] == self.sv(c - self.np()));
            } else {
                assert(self@.paged[c] == self.pv(c));
            }
        }
        assert forall|c: int, s: nat| 0 <= c < self.ncls() implies #[trigger] self@.slab_idle(c, s) == self.slab_idle(c, s) by {
            assert(self@.per_c(c) == self.per_c(c));
            assert forall|x: int| #[trigger] in_range(x, s * self.per_c(c), self.per_c(c)) implies self@.cidle(c, x)
                == self.cidle(c, x) by {
                assert(self@.cidle(c, x) == self.cidle(c, x));
            }
            if self@.slab_idle(c, s) {
                assert forall|x: int| #[trigger] in_range(x, s * self.per_c(c), self.per_c(c)) implies self.cidle(c, x) by {
                    assert(in_range(x, s * self@.per_c(c), self@.per_c(c)));
                    assert(self@.cidle(c, x) == self.cidle(c, x));
                }
            }
            if self.slab_idle(c, s) {
                assert forall|x: int| #[trigger] in_range(x, s * self@.per_c(c), self@.per_c(c)) implies self@.cidle(c, x) by {
                    assert(in_range(x, s * self.per_c(c), self.per_c(c)));
                    assert(self@.cidle(c, x) == self.cidle(c, x));
                }
            }
        }
    }

    // ------------------------------------------------------------------ abstract accessors
    pub open(crate) spec fn np(&self) -> nat {
        self.npaged as nat
    }

    pub open(crate) spec fn nst(&self) -> nat {
        self.state@.len()
    }

    pub open(crate) spec fn ncls(&self) -> nat {
        self.unit@.len()
    }

    /// Abstract state of paged class `i`.
    pub open(crate) spec fn pv(&self, i: int) -> MgrV {
        self.paged@[i]@
    }

    /// Abstract state of state class `j`.
    pub open(crate) spec fn sv(&self, j: int) -> StateV {
        self.state@[j]@
    }

    pub open(crate) spec fn per_c(&self, c: int) -> nat {
        self.per@[c] as nat
    }

    /// Unit ids of class `c` are `[0, N·n_c)`.
    pub open(crate) spec fn cunits(&self, c: int) -> nat {
        (self.nslab as nat) * self.per_c(c)
    }

    pub open(crate) spec fn cown(&self, c: int, x: int) -> bool {
        if c < self.np() {
            self.pv(c).own[x]
        } else {
            self.sv(c - self.np()).own[x]
        }
    }

    /// Unit `x` of class `c` is owned and unreferenced.
    pub open(crate) spec fn cidle(&self, c: int, x: int) -> bool {
        if c < self.np() {
            self.pv(c).own[x] && self.pv(c).refs[x] == 0
        } else {
            self.sv(c - self.np()).own[x] && self.sv(c - self.np()).holder[x] is None
        }
    }

    /// `|F_c|`.
    pub open(crate) spec fn cfree(&self, c: int) -> nat {
        if c < self.np() {
            self.pv(c).free_set().len()
        } else {
            self.sv(c - self.np()).free_set().len()
        }
    }

    /// Every unit of slab `s` is owned by class `c` and unreferenced.
    pub open(crate) spec fn slab_idle(&self, c: int, s: nat) -> bool {
        forall|x: int| #[trigger] in_range(x, s * self.per_c(c), self.per_c(c)) ==> self.cidle(c, x)
    }

    /// The live leases (paged class 0 is the reference copy).
    pub open(crate) spec fn leases(&self) -> Map<u64, LeaseV> {
        self.pv(0).leases
    }

    pub open(crate) spec fn next_handle(&self) -> u64 {
        self.pv(0).next_handle
    }

    pub open(crate) spec fn next_ticket(&self) -> u64 {
        self.pv(0).next_ticket
    }

    pub open(crate) spec fn fits_m(&self, m: nat) -> bool {
        fits(self.per@, self.np(), self.nst(), self.nslab as nat, m)
    }

    // ------------------------------------------------------------------ invariant
    /// Fixed configuration (I10, A1, representability).
    pub open(crate) spec fn cfg_ok(&self) -> bool {
        &&& self.nslab >= 1
        &&& self.sbytes >= 1
        &&& self.b >= 1
        &&& self.npaged >= 1
        &&& self.paged@.len() == self.np()
        &&& self.unit@.len() == self.per@.len()
        &&& self.unit@.len() == self.np() + self.nst()
        &&& self.ncls() < 0x1_0000
        &&& (self.nslab as nat) * (self.sbytes as nat) <= u64::MAX
        &&& forall|c: int|
            0 <= c < self.ncls() ==> {
                &&& #[trigger] self.unit@[c] >= 1
                &&& self.sbytes % self.unit@[c] == 0
                &&& self.per@[c] == self.sbytes / self.unit@[c]
                &&& self.per@[c] >= 1
                &&& self.cunits(c) * (self.b as nat) <= max_slots()
            }
    }

    /// Every pool is valid and sized `N·n_c`; paged classes share B and the namespace.
    pub open(crate) spec fn pools_ok(&self) -> bool {
        &&& forall|i: int|
            0 <= i < self.np() ==> {
                &&& #[trigger] self.paged@[i].valid()
                &&& self.pv(i).p == self.cunits(i)
                &&& self.pv(i).b == self.b as nat
                &&& self.pv(i).ns == self.pv(0).ns
                &&& self.pv(i).cfg == self.pv(0).cfg
                &&& cfg_rel(self.pv(i).cfg, self.np())
            }
        &&& forall|j: int|
            0 <= j < self.nst() ==> {
                &&& #[trigger] self.state@[j].valid()
                &&& self.sv(j).p == self.cunits(self.np() + j)
            }
    }

    /// I12/I13: slab ownership, `FS`, and per-unit ownership derived from the slab owner.
    pub open(crate) spec fn own_ok(&self) -> bool {
        &&& self.owner@.len() == self.nslab
        &&& forall|s: int| 0 <= s < self.nslab ==> #[trigger] self.owner@[s] <= self.ncls()
        &&& self.fs.wf()
        &&& self.fs.universe() == self.nslab
        &&& forall|s: usize| #[trigger] self.fs@.contains(s) <==> ((s as nat) < self.nslab && self.owner@[s as int] == 0)
        &&& forall|c: int, x: int|
            0 <= c < self.ncls() && 0 <= x < self.cunits(c) ==> #[trigger] self.cown(c, x) == (self.owner@[x
                / (self.per_c(c) as int)] == c + 1)
    }

    /// D14: paged classes hold the same leases and tickets; every lease fits (I1).
    pub open(crate) spec fn lock_ok(&self) -> bool {
        &&& forall|i: int|
            #![trigger self.paged@[i]]
            0 <= i < self.np() ==> {
                &&& self.pv(i).leases.dom() == self.pv(0).leases.dom()
                &&& self.pv(i).pend == self.pv(0).pend
                &&& self.pv(i).next_handle == self.pv(0).next_handle
                &&& self.pv(i).next_ticket == self.pv(0).next_ticket
            }
        &&& forall|i: int, h: u64|
            0 <= i < self.np() && #[trigger] self.pv(i).leases.contains_key(h) ==> {
                &&& self.pv(i).leases[h].toks == self.pv(0).leases[h].toks
                &&& self.pv(i).leases[h].c == self.pv(0).leases[h].c
                &&& self.pv(i).leases[h].pending == self.pv(0).leases[h].pending
                &&& self.pv(i).leases[h].rho == self.pv(0).leases[h].rho
            }
        &&& forall|h: u64|
            #[trigger] self.pv(0).leases.contains_key(h) ==> self.fits_m(cdiv(self.pv(0).leases[h].rho, self.b as nat))
    }

    /// I14/I15: one exclusive live slot per lease and state class, holding the state after
    /// `T_h[0:c_h]` once `c_h > 0`.
    pub open(crate) spec fn slots_ok(&self) -> bool {
        &&& self.slots@.dom() == self.pv(0).leases.dom()
        &&& forall|h: u64|
            #[trigger] self.slots@.contains_key(h) ==> self.slots@[h]@.len() == self.nst()
        &&& forall|h: u64, j: int|
            #![trigger self.slots@[h]@[j]]
            self.slots@.contains_key(h) && 0 <= j < self.nst() ==> {
                let x = self.slots@[h]@[j];
                let l = self.pv(0).leases[h];
                &&& (x as nat) < self.sv(j).p
                &&& self.sv(j).holder[x as int] == Some(h)
                &&& l.c > 0 ==> self.sv(j).w[x as int] == Some(l.toks.subrange(0, l.c as int))
            }
        &&& forall|j: int, x: int|
            #![trigger self.sv(j).holder[x]]
            0 <= j < self.nst() && 0 <= x < self.sv(j).p && self.sv(j).holder[x] is Some ==> {
                let h = self.sv(j).holder[x]->Some_0;
                &&& self.slots@.contains_key(h)
                &&& self.slots@[h]@[j] as int == x
            }
    }

    /// `Valid(S)` of the coordinator.
    pub open(crate) spec fn valid(&self) -> bool {
        &&& self.cfg_ok()
        &&& self.pools_ok()
        &&& self.own_ok()
        &&& self.lock_ok()
        &&& self.slots_ok()
    }

    /// `self` is `o` after one slab move at slab `s`: owners differ at most at `s`, and units of
    /// other slabs keep their ownership and idleness.
    pub(crate) open spec fn moved(&self, o: &Coordinator, s: int) -> bool {
        &&& o.valid()
        &&& self.valid()
        &&& self.nslab == o.nslab
        &&& self.per@ == o.per@
        &&& self.unit@ == o.unit@
        &&& self.npaged == o.npaged
        &&& self.paged@.len() == o.paged@.len()
        &&& self.state@.len() == o.state@.len()
        &&& 0 <= s < self.nslab
        &&& forall|s2: int| 0 <= s2 < self.nslab && s2 != s ==> #[trigger] self.owner@[s2] == o.owner@[s2]
        &&& forall|c2: int, x: int|
            #![trigger self.cidle(c2, x)]
            0 <= c2 < o.ncls() && 0 <= x < o.cunits(c2) && x / (o.per_c(c2) as int) != s ==> self.cidle(c2, x) == o.cidle(c2, x)
    }

    /// Same configuration and same lease/slot structure; pools differ at most by ownership,
    /// revoked keys of unreferenced pages outside `prot`, and `⊥` provenance of free state units
    /// (the effect of slab moves, §3.5 rules 1–3).
    pub open(crate) spec fn slab_frame(&self, o: &Coordinator, prot: Seq<bool>) -> bool {
        &&& self.id == o.id
        &&& self.nslab == o.nslab
        &&& self.sbytes == o.sbytes
        &&& self.b == o.b
        &&& self.npaged == o.npaged
        &&& self.unit@ == o.unit@
        &&& self.per@ == o.per@
        &&& self.paged@.len() == o.paged@.len()
        &&& self.state@.len() == o.state@.len()
        &&& self.slots@ == o.slots@
        &&& prot.len() == self.nslab
        &&& forall|i: int|
            #![trigger self.paged@[i]]
            0 <= i < self.np() ==> {
                &&& self.pv(i) == (MgrV { own: self.pv(i).own, keys: self.pv(i).keys, ..o.pv(i) })
                &&& self.paged@[i].den_log() == o.paged@[i].den_log()
                &&& forall|x: int|
                    #![trigger self.pv(i).keys[x]]
                    0 <= x < self.pv(i).p ==> self.pv(i).keys[x] == o.pv(i).keys[x] || (self.pv(i).keys[x] is None
                        && o.pv(i).refs[x] == 0 && !prot[x / (self.per_c(i) as int)])
            }
        &&& forall|j: int|
            #![trigger self.state@[j]]
            0 <= j < self.nst() ==> {
                &&& self.sv(j) == (StateV { own: self.sv(j).own, w: self.sv(j).w, ..o.sv(j) })
                &&& forall|x: int|
                    #![trigger self.sv(j).w[x]]
                    0 <= x < self.sv(j).p && o.sv(j).holder[x] is Some ==> self.sv(j).w[x] == o.sv(j).w[x]
            }
    }
}

/// `slab_frame` is reflexive and transitive.
pub(crate) proof fn lemma_slab_frame_refl(c: &Coordinator, prot: Seq<bool>)
    requires
        c.valid(),
        prot.len() == c.nslab,
    ensures
        c.slab_frame(c, prot),
{
    assert forall|i: int| #![trigger c.paged@[i]] 0 <= i < c.np() implies c.pv(i) == (MgrV {
        own: c.pv(i).own,
        keys: c.pv(i).keys,
        ..c.pv(i)
    }) by {}
    assert forall|j: int| #![trigger c.state@[j]] 0 <= j < c.nst() implies c.sv(j) == (StateV {
        own: c.sv(j).own,
        w: c.sv(j).w,
        ..c.sv(j)
    }) by {}
}

pub(crate) proof fn lemma_slab_frame_trans(a: &Coordinator, b: &Coordinator, c: &Coordinator, prot: Seq<bool>)
    requires
        b.slab_frame(a, prot),
        c.slab_frame(b, prot),
    ensures
        c.slab_frame(a, prot),
{
    assert forall|i: int| #![trigger c.paged@[i]] 0 <= i < c.np() implies {
        &&& c.pv(i) == (MgrV { own: c.pv(i).own, keys: c.pv(i).keys, ..a.pv(i) })
        &&& c.paged@[i].den_log() == a.paged@[i].den_log()
        &&& forall|x: int|
            #![trigger c.pv(i).keys[x]]
            0 <= x < c.pv(i).p ==> c.pv(i).keys[x] == a.pv(i).keys[x] || (c.pv(i).keys[x] is None && a.pv(i).refs[x] == 0
                && !prot[x / (c.per_c(i) as int)])
    } by {
        assert(b.paged@[i] == b.paged@[i]);
        assert(c.pv(i) == (MgrV { own: c.pv(i).own, keys: c.pv(i).keys, ..b.pv(i) }));
        assert(b.pv(i) == (MgrV { own: b.pv(i).own, keys: b.pv(i).keys, ..a.pv(i) }));
        assert forall|x: int| #![trigger c.pv(i).keys[x]] 0 <= x < c.pv(i).p implies c.pv(i).keys[x] == a.pv(i).keys[x] || (
        c.pv(i).keys[x] is None && a.pv(i).refs[x] == 0 && !prot[x / (c.per_c(i) as int)]) by {
            assert(b.pv(i).keys[x] == a.pv(i).keys[x] || (b.pv(i).keys[x] is None && a.pv(i).refs[x] == 0 && !prot[x / (
            b.per_c(i) as int)]));
            assert(c.pv(i).keys[x] == b.pv(i).keys[x] || (c.pv(i).keys[x] is None && b.pv(i).refs[x] == 0 && !prot[x / (
            c.per_c(i) as int)]));
        }
    }
    assert forall|j: int| #![trigger c.state@[j]] 0 <= j < c.nst() implies {
        &&& c.sv(j) == (StateV { own: c.sv(j).own, w: c.sv(j).w, ..a.sv(j) })
        &&& forall|x: int|
            #![trigger c.sv(j).w[x]]
            0 <= x < c.sv(j).p && a.sv(j).holder[x] is Some ==> c.sv(j).w[x] == a.sv(j).w[x]
    } by {
        assert(b.state@[j] == b.state@[j]);
        assert forall|x: int| #![trigger c.sv(j).w[x]] 0 <= x < c.sv(j).p && a.sv(j).holder[x] is Some implies c.sv(j).w[x]
            == a.sv(j).w[x] by {
            assert(b.sv(j).w[x] == a.sv(j).w[x]);
        }
    }
}

impl Coordinator {
    /// Gives free slab `s` to class `c` (§3.5 rule 3, receiving side).
    pub(crate) fn grant_slab(&mut self, s: usize, c: usize, Ghost(prot): Ghost<Seq<bool>>)
        requires
            old(self).valid(),
            prot.len() == old(self).nslab,
            (s as nat) < old(self).nslab,
            (c as nat) < old(self).ncls(),
            old(self).owner@[s as int] == 0,
        ensures
            final(self).valid(),
            final(self).slab_frame(old(self), prot),
            final(self).owner@ == old(self).owner@.update(s as int, (c + 1) as usize),
            final(self).fs@ == old(self).fs@.remove(s),
            final(self).cfree(c as int) == old(self).cfree(c as int) + old(self).per_c(c as int),
            forall|c2: int| 0 <= c2 < old(self).ncls() && c2 != c ==> #[trigger] final(self).cfree(c2) == old(self).cfree(c2),
            forall|c2: int, x: int|
                #![trigger final(self).cidle(c2, x)]
                #![trigger final(self).cown(c2, x)]
                0 <= c2 < old(self).ncls() && 0 <= x < old(self).cunits(c2) && x / (old(self).per_c(c2) as int) != s as int
                    ==> final(self).cidle(c2, x) == old(self).cidle(c2, x) && final(self).cown(c2, x) == old(self).cown(c2, x),
            forall|i: int| 0 <= i < old(self).np() ==> (#[trigger] final(self).pv(i)).keys == old(self).pv(i).keys,
            final(self).moved(old(self), s as int),
    {
        let ghost o = *self;
        let per = self.per[c];
        proof {
            assert(self.unit@[c as int] >= 1);
            lemma_mul_mono((s + 1) as nat, self.nslab as nat, per as nat);
            lemma_mul_succ(s as nat, per as nat);
            lemma_mul_mono(1, self.b as nat, self.cunits(c as int));
            assert(self.cunits(c as int) <= max_slots()) by (nonlinear_arith)
                requires self.cunits(c as int) * (self.b as nat) <= max_slots(), self.b >= 1;
        }
        let lo = s * per;
        if c < self.npaged {
            proof {
                assert(self.paged@[c as int].valid());
                assert forall|x: int| #[trigger] in_range(x, lo as nat, per as nat) implies !self.pv(c as int).own[x] by {
                    lemma_slab_of(x, per as nat, s as nat);
                    assert(self.cown(c as int, x) == (self.owner@[x / (per as int)] == c + 1));
                }
            }
            self.paged[c].grant_range(lo, per);
        } else {
            let j = c - self.npaged;
            proof {
                assert(self.state@[j as int].valid());
                assert forall|x: int| #[trigger] in_range(x, lo as nat, per as nat) implies !self.sv(j as int).own[x] by {
                    lemma_slab_of(x, per as nat, s as nat);
                    assert(self.cown(c as int, x) == (self.owner@[x / (per as int)] == c + 1));
                }
            }
            self.state[j].grant_range(lo, per);
        }
        self.fs.remove(s);
        self.owner.set(s, c + 1);
        proof {
            self.lemma_move_own(&o, s, c, lo, true);
            self.lemma_unit_frame(&o, s, c, lo, true);
            assert forall|i: int| 0 <= i < o.np() implies (#[trigger] self.pv(i)).keys == o.pv(i).keys by {
                if i != c as int {
                    assert(self.paged@[i] == o.paged@[i]);
                }
            }
        }
    }

    /// Takes idle slab `s` from class `c` (§3.5 rule 3, giving side): keys revoked, slab free.
    pub(crate) fn reclaim_slab(&mut self, s: usize, c: usize, Ghost(prot): Ghost<Seq<bool>>)
        requires
            old(self).valid(),
            (s as nat) < old(self).nslab,
            (c as nat) < old(self).ncls(),
            prot.len() == old(self).nslab,
            old(self).owner@[s as int] == c + 1,
            old(self).slab_idle(c as int, s as nat),
            !prot[s as int],
        ensures
            final(self).valid(),
            final(self).slab_frame(old(self), prot),
            final(self).owner@ == old(self).owner@.update(s as int, 0usize),
            final(self).fs@ == old(self).fs@.insert(s),
            final(self).cfree(c as int) + old(self).per_c(c as int) == old(self).cfree(c as int),
            forall|c2: int| 0 <= c2 < old(self).ncls() && c2 != c ==> #[trigger] final(self).cfree(c2) == old(self).cfree(c2),
            forall|c2: int, x: int|
                #![trigger final(self).cidle(c2, x)]
                #![trigger final(self).cown(c2, x)]
                0 <= c2 < old(self).ncls() && 0 <= x < old(self).cunits(c2) && x / (old(self).per_c(c2) as int) != s as int
                    ==> final(self).cidle(c2, x) == old(self).cidle(c2, x) && final(self).cown(c2, x) == old(self).cown(c2, x),
            final(self).moved(old(self), s as int),
    {
        let ghost o = *self;
        let per = self.per[c];
        proof {
            assert(self.unit@[c as int] >= 1);
            lemma_mul_mono((s + 1) as nat, self.nslab as nat, per as nat);
            lemma_mul_succ(s as nat, per as nat);
            lemma_mul_mono(1, self.b as nat, self.cunits(c as int));
            assert(self.cunits(c as int) <= max_slots()) by (nonlinear_arith)
                requires self.cunits(c as int) * (self.b as nat) <= max_slots(), self.b >= 1;
        }
        let lo = s * per;
        if c < self.npaged {
            proof {
                assert(self.paged@[c as int].valid());
                assert forall|x: int| #[trigger] in_range(x, lo as nat, per as nat) implies self.pv(c as int).own[x]
                    && self.pv(c as int).refs[x] == 0 by {
                    assert(self.cidle(c as int, x));
                }
            }
            self.paged[c].reclaim_range(lo, per);
        } else {
            let j = c - self.npaged;
            proof {
                assert(self.state@[j as int].valid());
                assert forall|x: int| #[trigger] in_range(x, lo as nat, per as nat) implies self.sv(j as int).own[x]
                    && self.sv(j as int).holder[x] is None by {
                    assert(self.cidle(c as int, x));
                }
            }
            self.state[j].reclaim_range(lo, per);
        }
        proof {
            assert(!self.fs@.contains(s));
        }
        self.fs.insert(s);
        self.owner.set(s, 0);
        proof {
            self.lemma_move_own(&o, s, c, lo, false);
            self.lemma_unit_frame(&o, s, c, lo, false);
            assert forall|i: int| #![trigger self.paged@[i]] 0 <= i < self.np() implies forall|x: int|
                #![trigger self.pv(i).keys[x]]
                0 <= x < self.pv(i).p ==> self.pv(i).keys[x] == o.pv(i).keys[x] || (self.pv(i).keys[x] is None
                    && o.pv(i).refs[x] == 0 && !prot[x / (self.per_c(i) as int)]) by {
                assert forall|x: int| #![trigger self.pv(i).keys[x]] 0 <= x < self.pv(i).p implies self.pv(i).keys[x]
                    == o.pv(i).keys[x] || (self.pv(i).keys[x] is None && o.pv(i).refs[x] == 0 && !prot[x / (self.per_c(
                    i,
                ) as int)]) by {
                    if i == c as int && in_range(x, lo as nat, per as nat) {
                        lemma_slab_of(x, per as nat, s as nat);
                        assert(o.cidle(c as int, x));
                    }
                }
            }
        }
    }

    /// Units outside slab `s` keep their idleness and ownership across a slab move.
    proof fn lemma_unit_frame(&self, o: &Coordinator, s: usize, c: usize, lo: usize, grant: bool)
        requires
            o.valid(),
            (c as nat) < o.ncls(),
            lo as nat == (s as nat) * o.per_c(c as int),
            o.per_c(c as int) >= 1,
            self.npaged == o.npaged,
            self.per@ == o.per@,
            self.paged@.len() == o.paged@.len(),
            self.state@.len() == o.state@.len(),
            forall|i: int| 0 <= i < o.np() && i != c ==> #[trigger] self.paged@[i] == o.paged@[i],
            forall|j: int| 0 <= j < o.nst() && j + o.np() != c ==> #[trigger] self.state@[j] == o.state@[j],
            (c as nat) < o.np() ==> {
                &&& grant ==> self.pv(c as int) == granted(o.pv(c as int), lo as nat, o.per_c(c as int))
                &&& !grant ==> self.pv(c as int) == reclaimed(o.pv(c as int), lo as nat, o.per_c(c as int))
            },
            (c as nat) >= o.np() ==> {
                let j = c - o.np();
                &&& grant ==> self.sv(j) == (StateV {
                    own: Seq::new(o.sv(j).p, |x: int| if in_range(x, lo as nat, o.per_c(c as int)) { true } else { o.sv(j).own[x] }),
                    ..o.sv(j)
                })
                &&& !grant ==> self.sv(j) == (StateV {
                    own: Seq::new(o.sv(j).p, |x: int| if in_range(x, lo as nat, o.per_c(c as int)) { false } else { o.sv(j).own[x] }),
                    w: Seq::new(o.sv(j).p, |x: int| if in_range(x, lo as nat, o.per_c(c as int)) { None } else { o.sv(j).w[x] }),
                    ..o.sv(j)
                })
            },
        ensures
            forall|c2: int, x: int|
                #![trigger self.cidle(c2, x)]
                #![trigger self.cown(c2, x)]
                0 <= c2 < o.ncls() && 0 <= x < o.cunits(c2) && x / (o.per_c(c2) as int) != s as int ==> self.cidle(c2, x)
                    == o.cidle(c2, x) && self.cown(c2, x) == o.cown(c2, x),
    {
        assert forall|c2: int, x: int|
            #![trigger self.cidle(c2, x)]
            #![trigger self.cown(c2, x)]
            0 <= c2 < o.ncls() && 0 <= x < o.cunits(c2) && x / (o.per_c(c2) as int) != s as int implies self.cidle(c2, x)
            == o.cidle(c2, x) && self.cown(c2, x) == o.cown(c2, x) by {
            if c2 == c as int {
                assert(!in_range(x, lo as nat, o.per_c(c as int))) by {
                    if in_range(x, lo as nat, o.per_c(c as int)) {
                        lemma_slab_of(x, o.per_c(c as int), s as nat);
                    }
                }
                if c2 < o.np() {
                    assert(o.paged@[c2].valid());
                    assert(o.pv(c2).p == o.cunits(c2));
                    assert(self.pv(c2).own[x] == o.pv(c2).own[x]);
                } else {
                    let j = c2 - o.np();
                    assert(o.state@[j].valid());
                    assert(o.sv(j).p == o.cunits(c2));
                    assert(self.sv(j).own[x] == o.sv(j).own[x]);
                    assert(self.sv(j).holder == o.sv(j).holder);
                }
            } else if c2 < o.np() {
                assert(self.paged@[c2] == o.paged@[c2]);
            } else {
                assert(self.state@[c2 - o.np()] == o.state@[c2 - o.np()]);
            }
        }
    }

    /// Ownership bookkeeping shared by `grant_slab` / `reclaim_slab`.
    proof fn lemma_move_own(&self, o: &Coordinator, s: usize, c: usize, lo: usize, grant: bool)
        requires
            o.valid(),
            (s as nat) < o.nslab,
            (c as nat) < o.ncls(),
            lo as nat == (s as nat) * o.per_c(c as int),
            self.id == o.id,
            self.nslab == o.nslab,
            self.sbytes == o.sbytes,
            self.b == o.b,
            self.npaged == o.npaged,
            self.unit@ == o.unit@,
            self.per@ == o.per@,
            self.slots@ == o.slots@,
            self.paged@.len() == o.paged@.len(),
            self.state@.len() == o.state@.len(),
            grant ==> o.owner@[s as int] == 0,
            !grant ==> o.owner@[s as int] == c + 1 && o.slab_idle(c as int, s as nat),
            self.owner@ == o.owner@.update(s as int, if grant { (c + 1) as usize } else { 0usize }),
            self.fs.wf(),
            self.fs.universe() == o.nslab,
            grant ==> self.fs@ == o.fs@.remove(s),
            !grant ==> self.fs@ == o.fs@.insert(s),
            forall|i: int| 0 <= i < o.np() && i != c ==> #[trigger] self.paged@[i] == o.paged@[i],
            forall|j: int| 0 <= j < o.nst() && j + o.np() != c ==> #[trigger] self.state@[j] == o.state@[j],
            (c as nat) < o.np() ==> {
                &&& self.paged@[c as int].valid()
                &&& self.paged@[c as int].den_log() == o.paged@[c as int].den_log()
                &&& grant ==> self.pv(c as int) == granted(o.pv(c as int), lo as nat, o.per_c(c as int))
                    && self.cfree(c as int) == o.cfree(c as int) + o.per_c(c as int)
                &&& !grant ==> self.pv(c as int) == reclaimed(o.pv(c as int), lo as nat, o.per_c(c as int))
                    && self.cfree(c as int) + o.per_c(c as int) == o.cfree(c as int)
            },
            (c as nat) >= o.np() ==> {
                let j = c - o.np();
                &&& self.state@[j].valid()
                &&& grant ==> self.sv(j) == (StateV {
                    own: Seq::new(o.sv(j).p, |x: int| if in_range(x, lo as nat, o.per_c(c as int)) { true } else { o.sv(j).own[x] }),
                    ..o.sv(j)
                }) && self.cfree(c as int) == o.cfree(c as int) + o.per_c(c as int)
                &&& !grant ==> self.sv(j) == (StateV {
                    own: Seq::new(o.sv(j).p, |x: int| if in_range(x, lo as nat, o.per_c(c as int)) { false } else { o.sv(j).own[x] }),
                    w: Seq::new(o.sv(j).p, |x: int| if in_range(x, lo as nat, o.per_c(c as int)) { None } else { o.sv(j).w[x] }),
                    ..o.sv(j)
                }) && self.cfree(c as int) + o.per_c(c as int) == o.cfree(c as int)
            },
        ensures
            self.valid(),
            forall|c2: int| 0 <= c2 < o.ncls() && c2 != c ==> #[trigger] self.cfree(c2) == o.cfree(c2),
            forall|i: int|
                #![trigger self.paged@[i]]
                0 <= i < self.np() ==> {
                    &&& self.pv(i) == (MgrV { own: self.pv(i).own, keys: self.pv(i).keys, ..o.pv(i) })
                    &&& self.paged@[i].den_log() == o.paged@[i].den_log()
                },
            forall|j: int|
                #![trigger self.state@[j]]
                0 <= j < self.nst() ==> {
                    &&& self.sv(j) == (StateV { own: self.sv(j).own, w: self.sv(j).w, ..o.sv(j) })
                    &&& forall|x: int|
                        #![trigger self.sv(j).w[x]]
                        0 <= x < self.sv(j).p && o.sv(j).holder[x] is Some ==> self.sv(j).w[x] == o.sv(j).w[x]
                },
    {
        let per = o.per_c(c as int);
        let newo: usize = if grant { (c + 1) as usize } else { 0usize };
        // cfg_ok, pools_ok
        assert(self.cfg_ok());
        // Every paged class differs from before at most in `own` and `keys`.
        assert forall|i: int| 0 <= i < self.np() implies (#[trigger] self.pv(i)) == (MgrV {
            own: self.pv(i).own,
            keys: self.pv(i).keys,
            ..o.pv(i)
        }) && self.paged@[i].valid() && self.paged@[i].den_log() == o.paged@[i].den_log() by {
            if i != c as int {
                assert(self.paged@[i] == o.paged@[i]);
            } else if grant {
                assert(self.pv(i) == granted(o.pv(i), lo as nat, per));
            } else {
                assert(self.pv(i) == reclaimed(o.pv(i), lo as nat, per));
            }
        }
        assert forall|j: int| 0 <= j < self.nst() implies (#[trigger] self.sv(j)) == (StateV {
            own: self.sv(j).own,
            w: self.sv(j).w,
            ..o.sv(j)
        }) && self.state@[j].valid() by {
            if j + o.np() != c as int {
                assert(self.state@[j] == o.state@[j]);
            }
        }
        assert forall|i: int| 0 <= i < self.np() implies {
            &&& #[trigger] self.paged@[i].valid()
            &&& self.pv(i).p == self.cunits(i)
            &&& self.pv(i).b == self.b as nat
            &&& self.pv(i).ns == self.pv(0).ns
            &&& self.pv(i).cfg == self.pv(0).cfg
            &&& cfg_rel(self.pv(i).cfg, self.np())
        } by {
            assert(o.paged@[i].valid());
            assert(self.pv(i) == (MgrV { own: self.pv(i).own, keys: self.pv(i).keys, ..o.pv(i) }));
            assert(self.pv(0) == (MgrV { own: self.pv(0).own, keys: self.pv(0).keys, ..o.pv(0) }));
        }
        assert forall|j: int| 0 <= j < self.nst() implies {
            &&& #[trigger] self.state@[j].valid()
            &&& self.sv(j).p == self.cunits(self.np() + j)
        } by {
            assert(o.state@[j].valid());
            assert(self.sv(j) == (StateV { own: self.sv(j).own, w: self.sv(j).w, ..o.sv(j) }));
        }
        assert(self.pools_ok());
        // own_ok
        assert forall|s2: int| 0 <= s2 < self.nslab implies #[trigger] self.owner@[s2] <= self.ncls() by {
            assert(o.owner@[s2] <= o.ncls());
        }
        assert forall|s2: usize| #[trigger] self.fs@.contains(s2) <==> ((s2 as nat) < self.nslab && self.owner@[s2 as int]
            == 0) by {
            assert(o.fs@.contains(s2) <==> ((s2 as nat) < o.nslab && o.owner@[s2 as int] == 0));
        }
        assert forall|c2: int, x: int| 0 <= c2 < self.ncls() && 0 <= x < self.cunits(c2) implies #[trigger] self.cown(
            c2,
            x,
        ) == (self.owner@[x / (self.per_c(c2) as int)] == c2 + 1) by {
            assert(o.cown(c2, x) == (o.owner@[x / (o.per_c(c2) as int)] == c2 + 1));
            assert(self.unit@[c2] >= 1);
            let n2 = self.per_c(c2);
            lemma_div_bounds(x as nat, n2);
            if x / (n2 as int) >= self.nslab {
                lemma_mul_mono(self.nslab as nat, (x / (n2 as int)) as nat, n2);
            }
            let s2 = x / (n2 as int);
            assert(0 <= s2 < self.nslab);
            assert(self.owner@[s2] == if s2 == s as int { newo } else { o.owner@[s2] });
            if c2 == c as int {
                lemma_slab_of(x, per, s as nat);
                if c2 < self.np() {
                    if grant {
                        assert(self.pv(c2) == granted(o.pv(c2), lo as nat, per));
                    } else {
                        assert(self.pv(c2) == reclaimed(o.pv(c2), lo as nat, per));
                    }
                }
            } else {
                if c2 < self.np() {
                    assert(self.paged@[c2] == o.paged@[c2]);
                } else {
                    assert(self.state@[c2 - o.np()] == o.state@[c2 - o.np()]);
                }
            }
        }
        assert(self.own_ok());
        // lock_ok: leases unchanged in every paged class.
        assert forall|i: int| 0 <= i < self.np() implies (#[trigger] self.pv(i)) == (MgrV {
            own: self.pv(i).own,
            keys: self.pv(i).keys,
            ..o.pv(i)
        }) by {}
        assert forall|i: int| #![trigger self.paged@[i]] 0 <= i < self.np() implies {
            &&& self.pv(i).leases.dom() == self.pv(0).leases.dom()
            &&& self.pv(i).pend == self.pv(0).pend
            &&& self.pv(i).next_handle == self.pv(0).next_handle
            &&& self.pv(i).next_ticket == self.pv(0).next_ticket
        } by {
            assert(self.pv(i) == (MgrV { own: self.pv(i).own, keys: self.pv(i).keys, ..o.pv(i) }));
            assert(self.pv(0) == (MgrV { own: self.pv(0).own, keys: self.pv(0).keys, ..o.pv(0) }));
            assert(o.paged@[i] == o.paged@[i]);
        }
        assert forall|i: int, h: u64| 0 <= i < self.np() && #[trigger] self.pv(i).leases.contains_key(h) implies {
            &&& self.pv(i).leases[h].toks == self.pv(0).leases[h].toks
            &&& self.pv(i).leases[h].c == self.pv(0).leases[h].c
            &&& self.pv(i).leases[h].pending == self.pv(0).leases[h].pending
            &&& self.pv(i).leases[h].rho == self.pv(0).leases[h].rho
        } by {
            assert(self.pv(i) == (MgrV { own: self.pv(i).own, keys: self.pv(i).keys, ..o.pv(i) }));
            assert(self.pv(0) == (MgrV { own: self.pv(0).own, keys: self.pv(0).keys, ..o.pv(0) }));
            assert(o.pv(i).leases.contains_key(h));
        }
        assert(self.pv(0) == (MgrV { own: self.pv(0).own, keys: self.pv(0).keys, ..o.pv(0) }));
        assert(self.lock_ok());
        // slots_ok: holders unchanged; held units keep their provenance.
        assert forall|j: int| 0 <= j < self.nst() implies (#[trigger] self.sv(j)) == (StateV {
            own: self.sv(j).own,
            w: self.sv(j).w,
            ..o.sv(j)
        }) by {}
        assert forall|j: int, x: int|
            #![trigger self.sv(j).w[x]]
            0 <= j < self.nst() && 0 <= x < self.sv(j).p && o.sv(j).holder[x] is Some implies self.sv(j).w[x] == o.sv(
            j,
        ).w[x] by {
            if !grant && j + o.np() == c as int && in_range(x, lo as nat, per) {
                lemma_slab_of(x, per, s as nat);
                assert(o.cidle(c as int, x));
            }
        }
        assert forall|h: u64, j: int| #![trigger self.slots@[h]@[j]] self.slots@.contains_key(h) && 0 <= j < self.nst() implies {
            let x = self.slots@[h]@[j];
            let l = self.pv(0).leases[h];
            &&& (x as nat) < self.sv(j).p
            &&& self.sv(j).holder[x as int] == Some(h)
            &&& l.c > 0 ==> self.sv(j).w[x as int] == Some(l.toks.subrange(0, l.c as int))
        } by {
            let x = o.slots@[h]@[j];
            assert(o.sv(j).holder[x as int] == Some(h));
            assert(self.sv(j).w[x as int] == o.sv(j).w[x as int]);
        }
        assert forall|j: int, x: int|
            #![trigger self.sv(j).holder[x]]
            0 <= j < self.nst() && 0 <= x < self.sv(j).p && self.sv(j).holder[x] is Some implies {
            let h = self.sv(j).holder[x]->Some_0;
            &&& self.slots@.contains_key(h)
            &&& self.slots@[h]@[j] as int == x
        } by {
            assert(o.sv(j).holder[x] is Some);
        }
        assert(self.slots_ok());
        assert forall|c2: int| 0 <= c2 < o.ncls() && c2 != c implies #[trigger] self.cfree(c2) == o.cfree(c2) by {
            if c2 < o.np() {
                assert(self.paged@[c2] == o.paged@[c2]);
            } else {
                assert(self.state@[c2 - o.np()] == o.state@[c2 - o.np()]);
            }
        }
    }
}

} // verus!

verus! {

/// Configuration accepted by C0 (A1 and representability).
pub open spec fn cfg_accepts(nslab: nat, sbytes: nat, b: nat, pu: Seq<usize>, su: Seq<usize>, ns: Seq<u8>) -> bool {
    &&& nslab >= 1
    &&& sbytes >= 1
    &&& b >= 1
    &&& pu.len() >= 1
    &&& pu.len() + su.len() < 0x1_0000
    &&& ns.len() <= u32::MAX
    &&& nslab * sbytes <= u64::MAX
    &&& forall|c: int| 0 <= c < pu.len() ==> #[trigger] pu[c] >= 1 && sbytes % (pu[c] as nat) == 0 && nslab * (sbytes
        / (pu[c] as nat)) * b <= max_slots()
    &&& forall|c: int| 0 <= c < su.len() ==> #[trigger] su[c] >= 1 && sbytes % (su[c] as nat) == 0 && nslab * (sbytes
        / (su[c] as nat)) * b <= max_slots()
}

impl Coordinator {
    /// C0. `create(N, S, classes, B, λ, δ, Namespace)`. Target paged classes are `pu` (in order),
    /// drafter paged classes `du`, then state classes `su`. The reservation margin is
    /// `μ = (δ + 1)·λ`, plus `λ` with drafter classes (D18). Every slab starts free.
    ///
    /// This stage supports `δ = 0` only; `δ > 0` returns ConfigError.
    pub fn create(
        nslab: usize,
        sbytes: usize,
        pu: &[usize],
        du: &[usize],
        su: &[usize],
        b: usize,
        lambda: usize,
        delta: usize,
        ns: &[u8],
    ) -> (r: Result<Coordinator, Error>)
        ensures
            r matches Ok(co) ==> {
                &&& co.inv()
                &&& co@.lam() == lambda
                &&& co@.mu() == create_mu(lambda as nat, du@.len())
                &&& co@.ntarget() == pu@.len()
                &&& co@.delta() == delta
                &&& co@.fits_m(cdiv(1 + co@.mu(), b as nat))
                &&& co@.nslab == nslab
                &&& co@.sbytes == sbytes
                &&& co@.b == b
                &&& co@.unit == pu@ + du@ + su@
                &&& co@.np == pu@.len() + du@.len()
                &&& co@.nst() == su@.len()
                &&& co@.owner.len() == nslab
                &&& forall|s: int| 0 <= s < nslab ==> #[trigger] co@.owner[s] == 0
                &&& co@.leases() == Map::<u64, LeaseV>::empty()
                &&& co@.pend() == Map::<u64, PendV>::empty()
                &&& co@.paged[0].ns == ns@
            },
            r matches Err(e) ==> e == Error::ConfigError || e == Error::IdentifierExhausted,
            !cfg_accepts(nslab as nat, sbytes as nat, b as nat, pu@ + du@, su@, ns@) ==> r == Err::<Coordinator, Error>(
                Error::ConfigError,
            ),
            // C0: no target class, drafter classes without drafts, δ > 0 (stage F), or an unrepresentable μ.
            (pu@.len() == 0 || (du@.len() > 0 && lambda == 0) || delta > 0 || lambda as nat > max_slots()
                || create_mu(lambda as nat, du@.len()) > max_slots()) ==> r == Err::<Coordinator, Error>(Error::ConfigError),
            // C0: not even a one-token lease (with its reservation) could attach.
            r is Ok ==> fits(per_of(sbytes as nat, pu@ + du@ + su@), pu@.len() + du@.len(), su@.len(), nslab as nat,
                cdiv(1 + create_mu(lambda as nat, du@.len()), b as nat)),
    {
        // C0: drafter classes need λ >= 1; δ > 0 is stage F.
        if pu.len() == 0 || pu.len() >= 0x1_0000 || du.len() >= 0x1_0000 || (du.len() > 0 && lambda == 0) || delta > 0
            || lambda > MAX_SLOTS as usize {
            return Err(Error::ConfigError);
        }
        let mu_d = if du.len() > 0 { lambda } else { 0 };
        if mu_d > MAX_SLOTS as usize - lambda {
            return Err(Error::ConfigError);
        }
        // μ = λ, plus λ with drafter classes (D18).
        let mu = lambda + mu_d;
        // Target classes, then drafter classes: one list of paged classes (D20).
        let ntarget = pu.len();
        let mut pall: Vec<usize> = vstd::slice::slice_to_vec(pu);
        pall.extend_from_slice(du);
        proof {
            assert(pall@ =~= pu@ + du@);
            assert(mu as nat == create_mu(lambda as nat, du@.len()));
            assert(create_early_ok(pu@, du@, lambda as nat, delta as nat));
        }
        if nslab == 0 || sbytes == 0 || b == 0 || pall.len() == 0 || pall.len() >= 0x1_0000 || su.len() >= 0x1_0000
            - pall.len() || ns.len() > u32::MAX as usize {
            return Err(Error::ConfigError);
        }
        proof {
            assert((nslab as nat) * (sbytes as nat) <= u128::MAX) by (nonlinear_arith)
                requires nslab as nat <= u64::MAX, sbytes as nat <= u64::MAX;
        }
        if (nslab as u128) * (sbytes as u128) > u64::MAX as u128 {
            return Err(Error::ConfigError);
        }
        let mut unit: Vec<usize> = Vec::new();
        let mut per: Vec<usize> = Vec::new();
        let ghost all = pall@ + su@;
        let ncls = pall.len() + su.len();
        let mut c: usize = 0;
        while c < ncls
            invariant
                pall@ == pu@ + du@,
                create_early_ok(pu@, du@, lambda as nat, delta as nat),
                0 <= c <= ncls,
                ncls == all.len(),
                all == pall@ + su@,
                nslab >= 1,
                b >= 1,
                sbytes >= 1,
                (nslab as nat) * (sbytes as nat) <= u64::MAX,
                unit@ == all.subrange(0, c as int),
                per@.len() == c,
                forall|k: int| 0 <= k < c ==> #[trigger] all[k] >= 1 && sbytes % all[k] == 0 && per@[k] == sbytes
                    / all[k] && per@[k] >= 1 && (nslab as nat) * (per@[k] as nat) * (b as nat) <= max_slots()
                    && (nslab as nat) * (per@[k] as nat) <= usize::MAX,
            decreases ncls - c,
        {
            let u = if c < pall.len() { pall[c] } else { su[c - pall.len()] };
            proof {
                assert(u == all[c as int]);
            }
            if u == 0 || !sbytes.is_multiple_of(u) {
                proof {
                    if c < pall.len() {
                        assert(pall@[c as int] == u);
                    } else {
                        assert(su@[c - pall.len()] == u);
                    }
                }
                return Err(Error::ConfigError);
            }
            let n = sbytes / u;
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(sbytes as int, u as int);
                assert(sbytes as int == u * (sbytes / u) as int + 0);
                if n == 0 {
                    assert(sbytes as int == u * 0);
                }
                assert(n >= 1);
                assert(n <= sbytes) by (nonlinear_arith) requires sbytes as int == u * (n as int), u >= 1, n >= 1;
                assert((nslab as nat) * (n as nat) <= (nslab as nat) * (sbytes as nat)) by (nonlinear_arith)
                    requires n <= sbytes;
                assert((nslab as nat) * (n as nat) * (b as nat) <= u128::MAX) by (nonlinear_arith)
                    requires (nslab as nat) * (n as nat) <= u64::MAX, b as nat <= u64::MAX;
            }
            if (nslab as u128) * (n as u128) * (b as u128) > MAX_SLOTS as u128 {
                proof {
                    if c < pall.len() {
                        assert(pall@[c as int] == u);
                    } else {
                        assert(su@[c - pall.len()] == u);
                    }
                }
                return Err(Error::ConfigError);
            }
            proof {
                assert((nslab as nat) * (n as nat) <= usize::MAX);
            }
            unit.push(u);
            per.push(n);
            proof {
                assert(unit@ =~= all.subrange(0, c + 1));
            }
            c += 1;
        }
        proof {
            assert(unit@ =~= all);
            assert(cfg_accepts(nslab as nat, sbytes as nat, b as nat, pall@, su@, ns@)) by {
                assert forall|k: int| 0 <= k < pall@.len() implies #[trigger] pall@[k] >= 1 && (sbytes as nat) % (
                pall@[k] as nat) == 0 && (nslab as nat) * ((sbytes as nat) / (pall@[k] as nat)) * (b as nat) <= max_slots() by {
                    assert(all[k] == pall@[k]);
                }
                assert forall|k: int| 0 <= k < su@.len() implies #[trigger] su@[k] >= 1 && (sbytes as nat) % (
                su@[k] as nat) == 0 && (nslab as nat) * ((sbytes as nat) / (su@[k] as nat)) * (b as nat) <= max_slots() by {
                    assert(all[pall@.len() + k] == su@[k]);
                }
            }
        }
        let id = match fresh_mgr_id() {
            Some(id) => id,
            None => return Err(Error::IdentifierExhausted),
        };
        // Every paged class shares one configuration (I10): μ = λ with no drafters and δ = 0.
        let cfg0 = PCfgC { mu, lam: lambda, delta: 0, ntarget };
        // Paged classes.
        let mut paged: Vec<Manager> = Vec::new();
        let mut i: usize = 0;
        proof {
            assert forall|k: int| 0 <= k < ncls implies #[trigger] per@[k] >= 1 && (nslab as nat) * (per@[k] as nat) * (
            b as nat) <= max_slots() && (nslab as nat) * (per@[k] as nat) <= usize::MAX by {
                assert(all[k] >= 1);
            }
        }
        while i < pall.len()
            invariant
                pall@ == pu@ + du@,
                create_early_ok(pu@, du@, lambda as nat, delta as nat),
                cfg_accepts(nslab as nat, sbytes as nat, b as nat, pall@, su@, ns@),
                cfg0@ == (PCfg { mu: mu as nat, lam: lambda as nat, delta: 0, ntarget: ntarget as nat }),
                lambda as nat <= max_slots(),
                mu as nat <= max_slots(),
                mu as nat == lambda as nat + (if ntarget < pall@.len() { lambda as nat } else { 0 }),
                1 <= ntarget <= pall@.len(),
                delta == 0,
                0 <= i <= pall@.len(),
                per@.len() == ncls,
                ncls == pall@.len() + su@.len(),
                b >= 1,
                nslab >= 1,
                ns@.len() <= u32::MAX,
                forall|k: int| 0 <= k < ncls ==> #[trigger] per@[k] >= 1 && (nslab as nat) * (per@[k] as nat) * (b as nat)
                    <= max_slots(),
                paged@.len() == i,
                forall|k: int|
                    0 <= k < ncls ==> (nslab as nat) * (#[trigger] per@[k] as nat) <= usize::MAX,
                forall|k: int|
                    0 <= k < i ==> {
                        &&& #[trigger] paged@[k].valid()
                        &&& paged@[k]@ == initial_own(paged@[k]@.id, (nslab as nat) * (per@[k] as nat), b as nat, ns@, false, cfg0@)
                        &&& paged@[k]@.ns == ns@
                    },
            decreases pall@.len() - i,
        {
            proof {
                assert((nslab as nat) * (per@[i as int] as nat) <= usize::MAX);
            }
            let units = nslab * per[i];
            proof {
                assert((nslab as nat) * (per@[i as int] as nat) * (b as nat) <= max_slots());
                lemma_mul_mono(1, b as nat, (nslab as nat) * (per@[i as int] as nat));
                assert((nslab as nat) * (per@[i as int] as nat) >= 1) by (nonlinear_arith)
                    requires nslab >= 1, per@[i as int] >= 1;
            }
            match Manager::create_empty(units, b, ns, cfg0) {
                Ok(m) => {
                    let ghost p0 = paged@;
                    paged.push(m);
                    proof {
                        assert forall|k: int| 0 <= k < i + 1 implies {
                            &&& #[trigger] paged@[k].valid()
                            &&& paged@[k]@ == initial_own(paged@[k]@.id, (nslab as nat) * (per@[k] as nat), b as nat, ns@, false, cfg0@)
                            &&& paged@[k]@.ns == ns@
                        } by {
                            if k < i {
                                assert(paged@[k] == p0[k]);
                            }
                        }
                    }
                },
                Err(_e) => {
                    proof {
                        // ConfigError is impossible: the configuration was checked above.
                        assert((units as nat) * (b as nat) <= max_slots());
                        assert(cfg0.mu as nat <= max_slots());
                    }
                    return Err(Error::IdentifierExhausted);
                },
            }
            i += 1;
        }
        let mut state: Vec<StatePool> = Vec::new();
        let mut j: usize = 0;
        let ghost pg0 = paged@;
        proof {
            assert(pg0.len() == pall@.len());
            assert(paged@[0].valid());
            assert(pg0[0]@.ns == ns@);
        }
        while j < su.len()
            invariant
                pall@ == pu@ + du@,
                create_early_ok(pu@, du@, lambda as nat, delta as nat),
                cfg0@ == (PCfg { mu: mu as nat, lam: lambda as nat, delta: 0, ntarget: ntarget as nat }),
                mu as nat <= max_slots(),
                mu as nat == lambda as nat + (if ntarget < pall@.len() { lambda as nat } else { 0 }),
                1 <= ntarget <= pall@.len(),
                delta == 0,
                lambda as nat <= max_slots(),
                paged@ == pg0,
                0 <= j <= su@.len(),
                per@.len() == ncls,
                ncls == pall@.len() + su@.len(),
                nslab >= 1,
                b >= 1,
                forall|k: int| 0 <= k < ncls ==> #[trigger] per@[k] >= 1 && (nslab as nat) * (per@[k] as nat) * (b as nat)
                    <= max_slots(),
                state@.len() == j,
                forall|k: int|
                    0 <= k < ncls ==> (nslab as nat) * (#[trigger] per@[k] as nat) <= usize::MAX,
                forall|k: int|
                    0 <= k < j ==> {
                        &&& #[trigger] state@[k].valid()
                        &&& state@[k]@.p == (nslab as nat) * (per@[pall@.len() + k] as nat)
                        &&& state@[k]@.own == Seq::new(state@[k]@.p, |x: int| false)
                        &&& state@[k]@.holder == Seq::new(state@[k]@.p, |x: int| None::<u64>)
                    },
            decreases su@.len() - j,
        {
            proof {
                let k = pall@.len() + j;
                assert(per@[k] >= 1);
                lemma_mul_mono(1, b as nat, (nslab as nat) * (per@[k] as nat));
            }
            let units = nslab * per[pall.len() + j];
            state.push(StatePool::new(units));
            j += 1;
        }
        let owner: Vec<usize> = vec![0usize; nslab];
        let fs = IdxSet::new_full(nslab);
        let ghost st = state@;
        let ghost pg = paged@;
        let co = Coordinator {
            id,
            nslab,
            sbytes,
            b,
            npaged: pall.len(),
            unit,
            per,
            owner,
            fs,
            paged,
            state,
            slots: HashMap::new(),
        };
        proof {
            assert(co.cfg_ok()) by {
                assert forall|k: int| 0 <= k < co.ncls() implies {
                    &&& #[trigger] co.unit@[k] >= 1
                    &&& co.sbytes % co.unit@[k] == 0
                    &&& co.per@[k] == co.sbytes / co.unit@[k]
                    &&& co.per@[k] >= 1
                    &&& co.cunits(k) * (co.b as nat) <= max_slots()
                } by {
                    assert(all[k] == co.unit@[k]);
                }
            }
            assert(co.pools_ok()) by {
                assert forall|k: int| 0 <= k < co.np() implies {
                    &&& #[trigger] co.paged@[k].valid()
                    &&& co.pv(k).p == co.cunits(k)
                    &&& co.pv(k).b == co.b as nat
                    &&& co.pv(k).ns == co.pv(0).ns
                    &&& co.pv(k).cfg == co.pv(0).cfg
                    &&& cfg_rel(co.pv(k).cfg, co.np())
                } by {
                    assert(co.paged@ == pg0);
                    assert(pg0[k].valid());
                    assert(pg0[0].valid());
                    assert(pg0[k]@.ns == ns@);
                    assert(pg0[0]@.ns == ns@);
                }
                assert forall|k: int| 0 <= k < co.nst() implies {
                    &&& #[trigger] co.state@[k].valid()
                    &&& co.sv(k).p == co.cunits(co.np() + k)
                } by {
                    assert(co.state@[k].valid());
                }
            }
            assert(co.own_ok()) by {
                assert forall|s2: usize| #[trigger] co.fs@.contains(s2) <==> ((s2 as nat) < co.nslab && co.owner@[s2 as int]
                    == 0) by {}
                assert forall|c2: int, x: int| 0 <= c2 < co.ncls() && 0 <= x < co.cunits(c2) implies #[trigger] co.cown(
                    c2,
                    x,
                ) == (co.owner@[x / (co.per_c(c2) as int)] == c2 + 1) by {
                    let n2 = co.per_c(c2);
                    lemma_div_bounds(x as nat, n2);
                    if x / (n2 as int) >= co.nslab {
                        lemma_mul_mono(co.nslab as nat, (x / (n2 as int)) as nat, n2);
                    }
                    if c2 < co.np() {
                        assert(co.paged@[c2].valid());
                    } else {
                        assert(co.state@[c2 - co.np()].valid());
                    }
                }
            }
            assert(co.lock_ok()) by {
                assert forall|k: int, h: u64| 0 <= k < co.np() && #[trigger] co.pv(k).leases.contains_key(h) implies false by {
                    assert(co.paged@[k].valid());
                }
                assert forall|h: u64| #[trigger] co.pv(0).leases.contains_key(h) implies false by {
                    assert(co.paged@[0].valid());
                }
                assert forall|k: int| #![trigger co.paged@[k]] 0 <= k < co.np() implies {
                    &&& co.pv(k).leases.dom() == co.pv(0).leases.dom()
                    &&& co.pv(k).pend == co.pv(0).pend
                    &&& co.pv(k).next_handle == co.pv(0).next_handle
                    &&& co.pv(k).next_ticket == co.pv(0).next_ticket
                } by {
                    assert(co.paged@[0].valid());
                    assert(co.paged@[k].valid());
                    assert(co.pv(k).leases =~= Map::<u64, LeaseV>::empty());
                    assert(co.pv(0).leases =~= Map::<u64, LeaseV>::empty());
                }
            }
            assert(co.pv(0).leases =~= Map::<u64, LeaseV>::empty()) by {
                assert(co.paged@[0].valid());
            }
            assert(co.slots_ok()) by {
                assert(co.slots@.dom() =~= Set::<u64>::empty());
                assert(co.slots@.dom() =~= co.pv(0).leases.dom());
                assert forall|k: int, x: int|
                    #![trigger co.sv(k).holder[x]]
                    0 <= k < co.nst() && 0 <= x < co.sv(k).p && co.sv(k).holder[x] is Some implies {
                    let h = co.sv(k).holder[x]->Some_0;
                    &&& co.slots@.contains_key(h)
                    &&& co.slots@[h]@[k] as int == x
                } by {
                    assert(co.state@[k].valid());
                }
            }
            assert(co@.paged[0] == co.pv(0));
            assert(co@.leases() =~= Map::<u64, LeaseV>::empty());
            assert(co@.pend() =~= Map::<u64, PendV>::empty()) by {
                assert(co.paged@[0].valid());
            }
            assert(co@.unit == pall@ + su@);
            assert(co@.nst() == su@.len());
            assert(co.inv());
            assert(co@.nslab == nslab);
            assert(co@.sbytes == sbytes);
            assert(co@.b == b);
            assert(co@.np == pall@.len());
            assert(co@.owner.len() == nslab);
            assert(forall|s: int| 0 <= s < nslab ==> #[trigger] co@.owner[s] == 0);
            assert(co.paged@ == pg);
            assert(co.paged@[0]@.ns == ns@);
            co.lemma_view();
            assert(co@.paged[0] == co.pv(0));
            assert(co@.paged[0].ns == ns@);
            assert(per@ =~= per_of(sbytes as nat, pall@ + su@)) by {
                assert forall|k: int| 0 <= k < per@.len() implies #[trigger] per@[k] == per_of(sbytes as nat, pall@ + su@)[k] by {
                    assert(per@[k] == sbytes / all[k]);
                }
            }
            assert(co@.per == per@);
            assert(co@.mu() == mu as nat && co@.lam() == lambda as nat && co@.delta() == delta as nat && co@.ntarget() == ntarget as nat) by {
                assert(co.paged@[0].valid());
                assert(co@.paged[0] == co.pv(0));
            }
        }
        // C0: a one-token lease must fit with its reservation, `Fits(ceil((1 + μ)/B))`.
        let n1 = 1 + mu;
        let m1 = (n1 - 1) / b + 1;
        proof {
            vstd::arithmetic::div_mod::lemma_div_plus_one((n1 - 1) as int, b as int);
            assert(((n1 - 1 + b) as int) / (b as int) == ((n1 - 1) as int) / (b as int) + 1);
            assert(m1 as nat == cdiv(n1 as nat, b as nat));
        }
        if !co.fits_exec(m1) {
            return Err(Error::ConfigError);
        }
        Ok(co)
    }
}

} // verus!
