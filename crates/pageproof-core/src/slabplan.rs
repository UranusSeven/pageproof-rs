//! v0.3 slab plan (contract §3.5): exact computation of `Cap(d, Prot)`, and the greedy plan that
//! acquires exactly `need_c` slabs per class, free slabs first, reclaiming idle unprotected slabs
//! from surplus classes only when free slabs run out. No trusted content.
use vstd::prelude::*;
use crate::arith::*;
use crate::cnt::*;
use crate::coord::*;
use crate::ops_slab::in_range;

verus! {

/// `n` and `o` have the same configuration.
pub open spec fn same_shape(n: CoordV, o: CoordV) -> bool {
    &&& n.nslab == o.nslab
    &&& n.per == o.per
    &&& n.unit == o.unit
    &&& n.np == o.np
    &&& n.paged.len() == o.paged.len()
    &&& n.state.len() == o.state.len()
}

/// Shape facts every valid coordinator view has.
pub open spec fn shape_ok(o: CoordV) -> bool {
    &&& o.per.len() == o.ncls()
    &&& o.owner.len() == o.nslab
    &&& o.nslab <= usize::MAX
    &&& forall|c: int| 0 <= c < o.ncls() ==> #[trigger] o.per[c] >= 1
}

/// `n` differs from `o` by a move at slab `s`: other slabs keep owner and idleness.
pub open spec fn slab_moved(n: CoordV, o: CoordV, s: int) -> bool {
    &&& same_shape(n, o)
    &&& 0 <= s < o.nslab
    &&& n.owner.len() == o.owner.len()
    &&& forall|s2: int| 0 <= s2 < o.nslab && s2 != s ==> #[trigger] n.owner[s2] == o.owner[s2]
    &&& forall|c2: int, s2: int|
        0 <= c2 < o.ncls() && 0 <= s2 < o.nslab && s2 != s ==> #[trigger] n.slab_idle(c2, s2 as nat) == o.slab_idle(
            c2,
            s2 as nat,
        )
}

/// `cdiv(x, p) = cdiv(x - p, p) + 1` for `x > p`, and `cdiv(x, p) = 1` for `0 < x <= p`.
pub proof fn lemma_cdiv_step(x: nat, p: nat)
    requires
        p >= 1,
        x > 0,
    ensures
        x <= p ==> cdiv(x, p) == 1,
        x > p ==> cdiv(x, p) == cdiv((x - p) as nat, p) + 1,
{
    lemma_cdiv_props(x, p);
    if x <= p {
        let q = cdiv(x, p);
        if q >= 2 {
            lemma_mul_mono(2, q, p);
            assert((q - 1) * p >= p) by (nonlinear_arith) requires q >= 2, p >= 1;
        }
    } else {
        let y = (x - p) as nat;
        lemma_cdiv_props(y, p);
        let q = cdiv(x, p);
        let r = cdiv(y, p);
        // (q-1)p < x <= qp and (r-1)p < y <= rp, with y = x - p.
        lemma_mul_succ(r, p);
        if q > r + 1 {
            lemma_mul_mono(r + 1, (q - 1) as nat, p);
        }
        if q < r + 1 {
            lemma_mul_mono(q, r, p);
            assert((r - 1) * p + p == r * p) by (nonlinear_arith) requires r >= 1;
        }
    }
}

/// If `f + (k-1)p < d <= f + kp` with `k >= 1`, then `k == cdiv(d - f, p)`.
pub proof fn lemma_cdiv_exact(f: nat, d: nat, p: nat, k: nat)
    requires
        p >= 1,
        k >= 1,
        f + (k - 1) * p < d,
        d <= f + k * p,
    ensures
        k == cdiv((d - f) as nat, p),
{
    let x = (d - f) as nat;
    lemma_cdiv_props(x, p);
    let q = cdiv(x, p);
    if q < k {
        lemma_mul_mono(q, (k - 1) as nat, p);
    }
    if q > k {
        lemma_mul_mono(k, (q - 1) as nat, p);
    }
}

proof fn lemma_cnt_free_point(o: CoordV, n: CoordV, s: int)
    requires
        slab_moved(n, o, s),
    ensures
        cnt(o.nslab as int, n.fpred()) + (if o.owner[s] == 0 {
            1nat
        } else {
            0nat
        }) == cnt(o.nslab as int, o.fpred()) + (if n.owner[s] == 0 {
            1nat
        } else {
            0nat
        }),
{
    assert forall|i: int| 0 <= i < o.nslab && i != s implies #[trigger] (o.fpred())(i) == (n.fpred())(i) by {}
    lemma_cnt_point(o.nslab as int, o.fpred(), n.fpred(), s);
}

proof fn lemma_cnt_recl_point(o: CoordV, n: CoordV, s: int, c: int, prot: Seq<bool>)
    requires
        slab_moved(n, o, s),
        0 <= c < o.ncls(),
    ensures
        n.rcount(c, prot) + (if o.reclaimable(c, prot, s) {
            1nat
        } else {
            0nat
        }) == o.rcount(c, prot) + (if n.reclaimable(c, prot, s) {
            1nat
        } else {
            0nat
        }),
{
    assert forall|i: int| 0 <= i < o.nslab && i != s implies #[trigger] (o.rpred(c, prot))(i) == (n.rpred(c, prot))(i) by {
        assert(n.slab_idle(c, i as nat) == o.slab_idle(c, i as nat));
    }
    lemma_cnt_point(o.nslab as int, o.rpred(c, prot), n.rpred(c, prot), s);
}

/// Effect of granting free slab `s` to deficit class `c` (§3.5 rule 3).
pub proof fn lemma_grant_step(o: CoordV, n: CoordV, s: int, c: int, d: Seq<usize>, prot: Seq<bool>)
    requires
        shape_ok(o),
        slab_moved(n, o, s),
        0 <= c < o.ncls(),
        d.len() == o.ncls(),
        o.owner[s] == 0,
        n.owner[s] == c + 1,
        n.cfree(c) == o.cfree(c) + o.per_c(c),
        forall|c2: int| 0 <= c2 < o.ncls() && c2 != c ==> #[trigger] n.cfree(c2) == o.cfree(c2),
        o.cfree(c) < d[c],
    ensures
        n.sum_need(d) + 1 == o.sum_need(d),
        n.fcount() + 1 == o.fcount(),
        n.sum_give(d, prot) == o.sum_give(d, prot),
        forall|c2: int| 0 <= c2 < o.ncls() ==> #[trigger] n.give(c2, d[c2] as nat, prot) == o.give(c2, d[c2] as nat, prot),
        forall|c2: int| 0 <= c2 < o.ncls() && c2 != c ==> #[trigger] n.need(c2, d[c2] as nat) == o.need(c2, d[c2] as nat),
        n.need(c, d[c] as nat) + 1 == o.need(c, d[c] as nat),
{
    let k = o.ncls() as int;
    let p = o.per_c(c);
    lemma_cnt_free_point(o, n, s);
    // need: only class c changes, by exactly one.
    let x = (d[c] - o.cfree(c)) as nat;
    lemma_cdiv_step(x, p);
    assert(n.need(c, d[c] as nat) + 1 == o.need(c, d[c] as nat)) by {
        if n.cfree(c) < d[c] {
            assert(((d[c] - n.cfree(c)) as nat) == (x - p) as nat);
        }
    }
    assert forall|c2: int| 0 <= c2 < k && c2 != c implies #[trigger] (o.needf(d))(c2) == (n.needf(d))(c2) by {}
    lemma_nsum_point(k, o.needf(d), n.needf(d), c);
    // give: class c gives 0 before and after; others unchanged.
    assert forall|c2: int| 0 <= c2 < k implies #[trigger] n.give(c2, d[c2] as nat, prot) == o.give(c2, d[c2] as nat, prot) by {
        lemma_cnt_recl_point(o, n, s, c2, prot);
        if c2 == c {
            if n.cfree(c) >= d[c] {
                assert(((n.cfree(c) - d[c]) as nat) < p);
                vstd::arithmetic::div_mod::lemma_basic_div((n.cfree(c) - d[c]) as int, p as int);
            }
        } else {
            assert(!o.reclaimable(c2, prot, s));
            assert(!n.reclaimable(c2, prot, s));
        }
    }
    assert forall|c2: int| 0 <= c2 < k implies #[trigger] (o.givef(d, prot))(c2) == (n.givef(d, prot))(c2) by {}
    lemma_nsum_ext(k, o.givef(d, prot), n.givef(d, prot));
}

/// Effect of reclaiming slab `s` from surplus class `c` (§3.5 rule 3).
pub proof fn lemma_reclaim_step(o: CoordV, n: CoordV, s: int, c: int, d: Seq<usize>, prot: Seq<bool>)
    requires
        shape_ok(o),
        slab_moved(n, o, s),
        0 <= c < o.ncls(),
        d.len() == o.ncls(),
        o.reclaimable(c, prot, s),
        n.owner[s] == 0,
        n.cfree(c) + o.per_c(c) == o.cfree(c),
        forall|c2: int| 0 <= c2 < o.ncls() && c2 != c ==> #[trigger] n.cfree(c2) == o.cfree(c2),
        o.cfree(c) >= d[c] + o.per_c(c),
    ensures
        n.sum_need(d) == o.sum_need(d),
        n.fcount() == o.fcount() + 1,
        n.sum_give(d, prot) + 1 == o.sum_give(d, prot),
        n.give(c, d[c] as nat, prot) + 1 == o.give(c, d[c] as nat, prot),
        forall|c2: int| 0 <= c2 < o.ncls() && c2 != c ==> #[trigger] n.give(c2, d[c2] as nat, prot) == o.give(c2, d[c2] as nat, prot),
        forall|c2: int| 0 <= c2 < o.ncls() ==> #[trigger] n.need(c2, d[c2] as nat) == o.need(c2, d[c2] as nat),
{
    let k = o.ncls() as int;
    let p = o.per_c(c);
    lemma_cnt_free_point(o, n, s);
    assert forall|c2: int| 0 <= c2 < k implies #[trigger] (o.needf(d))(c2) == (n.needf(d))(c2) by {}
    lemma_nsum_ext(k, o.needf(d), n.needf(d));
    lemma_cnt_recl_point(o, n, s, c, prot);
    assert(!n.reclaimable(c, prot, s));
    // lim decreases by exactly one.
    let lo = ((o.cfree(c) - d[c]) as nat);
    let ln = ((n.cfree(c) - d[c]) as nat);
    assert(ln + p == lo);
    vstd::arithmetic::div_mod::lemma_div_plus_one(ln as int, p as int);
    assert(lo / p == ln / p + 1) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ln as int, p as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(lo as int, p as int);
        vstd::arithmetic::div_mod::lemma_div_plus_one(ln as int, p as int);
    }
    assert(lo / p >= 1);
    assert(o.rcount(c, prot) >= 1);
    assert forall|c2: int| 0 <= c2 < k && c2 != c implies #[trigger] n.give(c2, d[c2] as nat, prot) == o.give(c2, d[c2] as nat, prot) by {
        lemma_cnt_recl_point(o, n, s, c2, prot);
        assert(!o.reclaimable(c2, prot, s));
        assert(!n.reclaimable(c2, prot, s));
    }
    assert forall|c2: int| 0 <= c2 < k && c2 != c implies #[trigger] (o.givef(d, prot))(c2) == (n.givef(d, prot))(c2) by {}
    lemma_nsum_point(k, o.givef(d, prot), n.givef(d, prot), c);
}

/// With no free slab and no possible donor, no class has a deficit (Cap is tight).
pub proof fn lemma_no_donor(o: CoordV, c: int, d: Seq<usize>, prot: Seq<bool>)
    requires
        shape_ok(o),
        0 <= c < o.ncls(),
        d.len() == o.ncls(),
        o.sum_need(d) <= o.fcount() + o.sum_give(d, prot),
        o.fcount() == 0,
        o.cfree(c) < d[c],
        forall|c2: int| 0 <= c2 < o.ncls() ==> o.cfree(c2) < d[c2] + o.per_c(c2) || #[trigger] o.rcount(c2, prot) == 0,
    ensures
        false,
{
    let k = o.ncls() as int;
    assert forall|c2: int| 0 <= c2 < k implies #[trigger] (o.givef(d, prot))(c2) == 0 by {
        if o.cfree(c2) >= d[c2] && o.cfree(c2) < d[c2] + o.per_c(c2) {
            vstd::arithmetic::div_mod::lemma_basic_div((o.cfree(c2) - d[c2]) as int, o.per_c(c2) as int);
        }
    }
    lemma_nsum_zero(k, o.givef(d, prot));
    lemma_nsum_le(k, o.needf(d), c);
    lemma_cdiv_props((d[c] - o.cfree(c)) as nat, o.per_c(c));
}

impl Coordinator {
    pub(crate) proof fn lemma_shape(&self)
        requires
            self.valid(),
        ensures
            shape_ok(self@),
            self@.ncls() == self.ncls(),
            forall|c: int| 0 <= c < self.ncls() ==> #[trigger] self@.per_c(c) == self.per_c(c),
    {
        self.lemma_view();
        assert forall|c: int| 0 <= c < self@.ncls() implies #[trigger] self@.per[c] >= 1 by {
            assert(self.unit@[c] >= 1);
        }
    }

    /// `|F_c|`, executable.
    pub(crate) fn class_free(&self, c: usize) -> (r: usize)
        requires
            self.valid(),
            (c as nat) < self.ncls(),
        ensures
            r as nat == self@.cfree(c as int),
    {
        proof {
            self.lemma_view_cls();
        }
        if c < self.npaged {
            proof {
                assert(self.paged@[c as int].valid());
            }
            self.paged[c].free_len()
        } else {
            proof {
                assert(self.state@[c - self.npaged].valid());
            }
            self.state[c - self.npaged].free_len()
        }
    }

    /// Whether slab `s` of class `c` is idle, executable.
    pub(crate) fn slab_is_idle(&self, c: usize, s: usize) -> (r: bool)
        requires
            self.valid(),
            (c as nat) < self.ncls(),
            (s as nat) < self.nslab,
        ensures
            r == self@.slab_idle(c as int, s as nat),
    {
        proof {
            self.lemma_view_cls();
            assert(self.unit@[c as int] >= 1);
            lemma_mul_mono((s + 1) as nat, self.nslab as nat, self.per_c(c as int));
            lemma_mul_succ(s as nat, self.per_c(c as int));
            lemma_mul_mono(1, self.b as nat, self.cunits(c as int));
            assert(self.cunits(c as int) <= max_slots()) by (nonlinear_arith)
                requires self.cunits(c as int) * (self.b as nat) <= max_slots(), self.b >= 1;
        }
        let per = self.per[c];
        let lo = s * per;
        if c < self.npaged {
            proof {
                assert(self.paged@[c as int].valid());
            }
            let r = self.paged[c].range_idle(lo, per);
            proof {
                assert(r == self.slab_idle(c as int, s as nat)) by {
                    if r {
                        assert forall|x: int| #[trigger] in_range(x, (s as nat) * self.per_c(c as int), self.per_c(c as int))
                            implies self.cidle(c as int, x) by {
                            assert(in_range(x, lo as nat, per as nat));
                        }
                    } else {
                        let x = choose|x: int| #[trigger] in_range(x, lo as nat, per as nat) && !(self.pv(c as int).own[x]
                            && self.pv(c as int).refs[x] == 0);
                        assert(in_range(x, (s as nat) * self.per_c(c as int), self.per_c(c as int)));
                    }
                }
            }
            r
        } else {
            let j = c - self.npaged;
            proof {
                assert(self.state@[j as int].valid());
            }
            let r = self.state[j].range_idle(lo, per);
            proof {
                assert(r == self.slab_idle(c as int, s as nat)) by {
                    if r {
                        assert forall|x: int| #[trigger] in_range(x, (s as nat) * self.per_c(c as int), self.per_c(c as int))
                            implies self.cidle(c as int, x) by {
                            assert(in_range(x, lo as nat, per as nat));
                        }
                    } else {
                        let x = choose|x: int| #[trigger] in_range(x, lo as nat, per as nat) && !(self.sv(j as int).own[x]
                            && self.sv(j as int).holder[x] is None);
                        assert(in_range(x, (s as nat) * self.per_c(c as int), self.per_c(c as int)));
                    }
                }
            }
            r
        }
    }

    /// Whether slab `s` is in `R_c` (reclaimable from class `c` outside `prot`).
    pub(crate) fn is_reclaimable(&self, c: usize, prot: &Vec<bool>, s: usize) -> (r: bool)
        requires
            self.valid(),
            (c as nat) < self.ncls(),
            (s as nat) < self.nslab,
            prot@.len() == self.nslab,
        ensures
            r == self@.reclaimable(c as int, prot@, s as int),
    {
        proof {
            self.lemma_view();
        }
        self.owner[s] == c + 1 && !prot[s] && self.slab_is_idle(c, s)
    }

    /// `|R_c|`, executable.
    pub(crate) fn count_reclaimable(&self, c: usize, prot: &Vec<bool>) -> (r: usize)
        requires
            self.valid(),
            (c as nat) < self.ncls(),
            prot@.len() == self.nslab,
        ensures
            r as nat == self@.rcount(c as int, prot@),
            r <= self.nslab,
    {
        let mut n: usize = 0;
        let mut s: usize = 0;
        while s < self.nslab
            invariant
                self.valid(),
                (c as nat) < self.ncls(),
                prot@.len() == self.nslab,
                s <= self.nslab,
                n as nat == cnt(s as int, self@.rpred(c as int, prot@)),
                n <= s,
            decreases self.nslab - s,
        {
            if self.is_reclaimable(c, prot, s) {
                n += 1;
            }
            s += 1;
        }
        n
    }

    /// Some slab of `R_c`, or `None` iff `R_c` is empty.
    pub(crate) fn find_reclaimable(&self, c: usize, prot: &Vec<bool>) -> (r: Option<usize>)
        requires
            self.valid(),
            (c as nat) < self.ncls(),
            prot@.len() == self.nslab,
        ensures
            r is None ==> self@.rcount(c as int, prot@) == 0,
            r matches Some(s) ==> (s as nat) < self.nslab && self@.reclaimable(c as int, prot@, s as int),
    {
        let mut s: usize = 0;
        while s < self.nslab
            invariant
                self.valid(),
                (c as nat) < self.ncls(),
                prot@.len() == self.nslab,
                s <= self.nslab,
                cnt(s as int, self@.rpred(c as int, prot@)) == 0,
            decreases self.nslab - s,
        {
            if self.is_reclaimable(c, prot, s) {
                return Some(s);
            }
            s += 1;
        }
        None
    }

    /// `need_c` and `give_c` for one class, executable.
    pub(crate) fn need_give(&self, c: usize, d: usize, prot: &Vec<bool>) -> (r: (usize, usize))
        requires
            self.valid(),
            (c as nat) < self.ncls(),
            prot@.len() == self.nslab,
        ensures
            r.0 as nat == self@.need(c as int, d as nat),
            r.1 as nat == self@.give(c as int, d as nat, prot@),
            r.0 <= d,
            r.1 <= self.nslab,
    {
        proof {
            self.lemma_shape();
        }
        let f = self.class_free(c);
        let p = self.per[c];
        if d <= f {
            let lim = (f - d) / p;
            let rc = self.count_reclaimable(c, prot);
            (0, if rc <= lim { rc } else { lim })
        } else {
            let x = d - f;
            let q = (x - 1) / p;
            proof {
                vstd::arithmetic::div_mod::lemma_div_plus_one((x - 1) as int, p as int);
                assert(((x - 1 + p) as int) / (p as int) == q + 1);
                assert(cdiv(x as nat, p as nat) == q + 1);
                vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator((x - 1) as int, 1, p as int);
                assert(q <= x - 1);
            }
            (q + 1, 0)
        }
    }

    /// `Cap(d, Prot)`, executable (exact).
    pub(crate) fn check_cap(&self, d: &Vec<usize>, prot: &Vec<bool>) -> (r: bool)
        requires
            self.valid(),
            d@.len() == self.ncls(),
            prot@.len() == self.nslab,
            forall|c: int| 0 <= c < d@.len() ==> #[trigger] d@[c] <= max_slots(),
        ensures
            r == self@.cap(d@, prot@),
    {
        proof {
            self.lemma_shape();
        }
        let k = self.unit.len();
        let mut tn: u64 = 0;
        let mut tg: u64 = 0;
        let mut c: usize = 0;
        while c < k
            invariant
                self.valid(),
                k as nat == self.ncls(),
                d@.len() == self.ncls(),
                prot@.len() == self.nslab,
                forall|c2: int| 0 <= c2 < d@.len() ==> #[trigger] d@[c2] <= max_slots(),
                c <= k,
                k < 0x1_0000,
                tn as nat == nsum(c as int, self@.needf(d@)),
                tg as nat == nsum(c as int, self@.givef(d@, prot@)),
                tn as nat <= c * max_slots(),
                tg as nat <= c * max_slots(),
            decreases k - c,
        {
            let (nd, gv) = self.need_give(c, d[c], prot);
            proof {
                self.lemma_nslab_bound();
                assert((c + 1) * max_slots() <= 0x1_0000 * max_slots()) by (nonlinear_arith) requires c + 1 <= 0x1_0000;
                lemma_mul_succ(c as nat, max_slots());
            }
            tn = tn + nd as u64;
            tg = tg + gv as u64;
            c += 1;
        }
        let f = self.free_slab_count();
        proof {
            self.lemma_nslab_bound();
            assert(k * max_slots() <= 0x1_0000 * max_slots()) by (nonlinear_arith) requires k <= 0x1_0000;
        }
        tn <= f as u64 + tg
    }

    pub(crate) proof fn lemma_nslab_bound(&self)
        requires
            self.valid(),
        ensures
            self.nslab as nat <= max_slots(),
            forall|c: int| 0 <= c < self.ncls() ==> #[trigger] self.cunits(c) <= max_slots(),
    {
        assert forall|c: int| 0 <= c < self.ncls() implies #[trigger] self.cunits(c) <= max_slots() by {
            assert(self.unit@[c] >= 1);
            assert(self.cunits(c) <= max_slots()) by (nonlinear_arith)
                requires self.cunits(c) * (self.b as nat) <= max_slots(), self.b >= 1;
        }
        assert(self.unit@[0] >= 1);
        assert(self.cunits(0) <= max_slots());
        assert(self.nslab as nat <= self.cunits(0)) by (nonlinear_arith)
            requires self.cunits(0) == (self.nslab as nat) * self.per_c(0), self.per_c(0) >= 1;
    }

    /// First class with a deficit (`|F_c| < d_c`), if any.
    pub(crate) fn find_deficit(&self, d: &Vec<usize>) -> (r: Option<usize>)
        requires
            self.valid(),
            d@.len() == self.ncls(),
        ensures
            r is None ==> forall|c: int| 0 <= c < self.ncls() ==> #[trigger] self@.cfree(c) >= d@[c],
            r matches Some(c) ==> (c as nat) < self.ncls() && self@.cfree(c as int) < d@[c as int],
    {
        let k = self.unit.len();
        let mut c: usize = 0;
        while c < k
            invariant
                self.valid(),
                k as nat == self.ncls(),
                d@.len() == self.ncls(),
                c <= k,
                forall|c2: int| 0 <= c2 < c ==> #[trigger] self@.cfree(c2) >= d@[c2],
            decreases k - c,
        {
            if self.class_free(c) < d[c] {
                return Some(c);
            }
            c += 1;
        }
        None
    }

    /// A class `c` with `|F_c| >= d_c + n_c` and a reclaimable slab, with that slab.
    pub(crate) fn find_donor(&self, d: &Vec<usize>, prot: &Vec<bool>) -> (r: Option<(usize, usize)>)
        requires
            self.valid(),
            d@.len() == self.ncls(),
            prot@.len() == self.nslab,
            forall|c: int| 0 <= c < d@.len() ==> #[trigger] d@[c] <= max_slots(),
        ensures
            r is None ==> forall|c: int| 0 <= c < self.ncls() ==> self@.cfree(c) < d@[c] + self@.per_c(c) || #[trigger] self@.rcount(
                c,
                prot@,
            ) == 0,
            r matches Some((c, s)) ==> (c as nat) < self.ncls() && (s as nat) < self.nslab && self@.cfree(c as int) >= d@[c as int]
                + self@.per_c(c as int) && self@.reclaimable(c as int, prot@, s as int),
    {
        proof {
            self.lemma_shape();
        }
        let k = self.unit.len();
        let mut c: usize = 0;
        while c < k
            invariant
                self.valid(),
                k as nat == self.ncls(),
                d@.len() == self.ncls(),
                prot@.len() == self.nslab,
                forall|c2: int| 0 <= c2 < d@.len() ==> #[trigger] d@[c2] <= max_slots(),
                forall|c2: int| 0 <= c2 < self.ncls() ==> #[trigger] self@.per_c(c2) == self.per_c(c2),
                c <= k,
                forall|c2: int| 0 <= c2 < c ==> self@.cfree(c2) < d@[c2] + self@.per_c(c2) || #[trigger] self@.rcount(c2, prot@)
                    == 0,
            decreases k - c,
        {
            let f = self.class_free(c);
            let p = self.per[c];
            if f >= p && f - p >= d[c] {
                match self.find_reclaimable(c, prot) {
                    Some(s) => {
                        return Some((c, s));
                    },
                    None => {},
                }
            }
            c += 1;
        }
        None
    }

    /// The slab plan of §3.5: while some class has a deficit, give it a free slab, or else
    /// reclaim an idle unprotected slab from a class that keeps `d_c` free units without it.
    /// Requires `Cap(d, prot)`; afterwards every class has `|F_c| >= d_c`.
    pub(crate) fn run_plan(&mut self, d: &Vec<usize>, prot: &Vec<bool>)
        requires
            old(self).valid(),
            d@.len() == old(self).ncls(),
            prot@.len() == old(self).nslab,
            forall|c: int| 0 <= c < d@.len() ==> #[trigger] d@[c] <= max_slots(),
            old(self)@.cap(d@, prot@),
        ensures
            final(self).valid(),
            final(self).slab_frame(old(self), prot@),
            forall|c: int| 0 <= c < final(self).ncls() ==> #[trigger] final(self)@.cfree(c) >= d@[c],
            final(self).ncls() == old(self).ncls(),
            final(self).nslab == old(self).nslab,
    {
        let ghost o = *self;
        proof {
            lemma_slab_frame_refl(self, prot@);
        }
        loop
            invariant_except_break
                self.valid(),
                self.slab_frame(&o, prot@),
                self.ncls() == o.ncls(),
                self.nslab == o.nslab,
                d@.len() == self.ncls(),
                prot@.len() == self.nslab,
                forall|c: int| 0 <= c < d@.len() ==> #[trigger] d@[c] <= max_slots(),
                self@.cap(d@, prot@),
            invariant
                self.valid(),
                self.slab_frame(&o, prot@),
                self.ncls() == o.ncls(),
                self.nslab == o.nslab,
            ensures
                forall|c: int| 0 <= c < self.ncls() ==> #[trigger] self@.cfree(c) >= d@[c],
            decreases self@.sum_need(d@) + self@.sum_give(d@, prot@),
        {
            proof {
                self.lemma_shape();
            }
            let def = self.find_deficit(d);
            match def {
                None => {
                    break;
                },
                Some(c) => {
                    let ghost before = *self;
                    let ghost bv = self@;
                    if self.fs.len() > 0 {
                        let s = self.fs.peek();
                        proof {
                            assert(self.owner@[s as int] == 0);
                        }
                        self.grant_slab(s, c, Ghost(prot@));
                        proof {
                            self.lemma_view();
                            before.lemma_view();
                            self.lemma_view_cls();
                            before.lemma_view_cls();
                            self.lemma_moved_view(&before, s as int);
                            lemma_grant_step(bv, self@, s as int, c as int, d@, prot@);
                            lemma_slab_frame_trans(&o, &before, self, prot@);
                        }
                    } else {
                        let don = self.find_donor(d, prot);
                        match don {
                            None => {
                                proof {
                                    self.lemma_view();
                                    lemma_cnt_set(self.nslab as int, self@.fpred(), self.fs@);
                                    lemma_no_donor(self@, c as int, d@, prot@);
                                }
                                assert(false);
                                break;
                            },
                            Some((c2, s)) => {
                                proof {
                                    self.lemma_view_cls();
                                    self.lemma_view();
                                }
                                self.reclaim_slab(s, c2, Ghost(prot@));
                                proof {
                                    self.lemma_view();
                                    before.lemma_view();
                                    self.lemma_view_cls();
                                    before.lemma_view_cls();
                                    self.lemma_moved_view(&before, s as int);
                                    lemma_reclaim_step(bv, self@, s as int, c2 as int, d@, prot@);
                                    lemma_slab_frame_trans(&o, &before, self, prot@);
                                }
                            },
                        }
                    }
                },
            }
        }
    }

    /// `moved` lifts to the public view.
    pub(crate) proof fn lemma_moved_view(&self, o: &Coordinator, s: int)
        requires
            self.moved(o, s),
        ensures
            slab_moved(self@, o@, s),
    {
        self.lemma_view();
        o.lemma_view();
        self.lemma_view_cls();
        o.lemma_view_cls();
        assert forall|c2: int, s2: int|
            0 <= c2 < o@.ncls() && 0 <= s2 < o@.nslab && s2 != s implies #[trigger] self@.slab_idle(c2, s2 as nat) == o@.slab_idle(
            c2,
            s2 as nat,
        ) by {
            let p = o.per_c(c2);
            assert(o.unit@[c2] >= 1);
            assert forall|x: int| #[trigger] in_range(x, (s2 as nat) * p, p) implies self.cidle(c2, x) == o.cidle(c2, x) by {
                lemma_mul_mono((s2 + 1) as nat, o.nslab as nat, p);
                lemma_mul_succ(s2 as nat, p);
                crate::coord::lemma_slab_of(x, p, s2 as nat);
            }
            if self.slab_idle(c2, s2 as nat) {
                assert forall|x: int| #[trigger] in_range(x, (s2 as nat) * p, p) implies o.cidle(c2, x) by {
                    assert(self.cidle(c2, x) == o.cidle(c2, x));
                }
            }
            if o.slab_idle(c2, s2 as nat) {
                assert forall|x: int| #[trigger] in_range(x, (s2 as nat) * p, p) implies self.cidle(c2, x) by {
                    assert(self.cidle(c2, x) == o.cidle(c2, x));
                }
            }
        }
    }

    /// `|FS|`, executable.
    pub(crate) fn free_slab_count(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self@.fcount(),
            r <= self.nslab,
    {
        proof {
            self.lemma_view();
            lemma_cnt_set(self.nslab as int, self@.fpred(), self.fs@);
            self.fs.lemma_bounds();
        }
        self.fs.len()
    }
}

} // verus!
