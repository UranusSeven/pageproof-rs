//! v0.3 slab operations on one paged class (contract §3.5): give a unit range to the class
//! (`grant_range`), take an idle range back revoking its keys (`reclaim_range`), and the idleness
//! test (`range_idle`). No trusted content.
use vstd::prelude::*;
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::manager::*;
use crate::idxset::IdxSet;
use crate::index::KeyIndex;
#[cfg(verus_keep_ghost)]
use crate::index::in_index;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub open spec fn in_range(x: int, lo: nat, n: nat) -> bool {
    lo <= x < lo + n
}

/// Abstract state after granting `[lo, lo+n)`: those units become owned (ref 0, no key).
pub open spec fn granted(v: MgrV, lo: nat, n: nat) -> MgrV {
    MgrV { own: Seq::new(v.p, |x: int| if in_range(x, lo, n) { true } else { v.own[x] }), ..v }
}

/// Abstract state after reclaiming `[lo, lo+n)`: unowned, keys revoked (I13).
pub open spec fn reclaimed(v: MgrV, lo: nat, n: nat) -> MgrV {
    MgrV {
        own: Seq::new(v.p, |x: int| if in_range(x, lo, n) { false } else { v.own[x] }),
        keys: Seq::new(v.p, |x: int| if in_range(x, lo, n) { None } else { v.keys[x] }),
        ..v
    }
}

/// Every unit of the range is owned and unreferenced (a reclaimable slab of §3.5).
pub open spec fn idle_range(v: MgrV, lo: nat, n: nat) -> bool {
    forall|x: int| #[trigger] in_range(x, lo, n) ==> v.own[x] && v.refs[x] == 0
}

/// Every unit of the range is unowned (a free slab).
pub open spec fn unowned_range(v: MgrV, lo: nat, n: nat) -> bool {
    forall|x: int| #[trigger] in_range(x, lo, n) ==> !v.own[x]
}

/// Grant keeps `Valid`: new units have ref 0 and no key (I13 of the previous state).
pub proof fn lemma_grant_inv(v: MgrV, log: Log, lo: nat, n: nat)
    requires
        inv(v, log),
        lo + n <= v.p,
    ensures
        inv(granted(v, lo, n), log),
{
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    let v2 = granted(v, lo, n);
    assert forall|h: u64| #[trigger] v2.leases.contains_key(h) implies lease_ok(v2, log, h) by {
        assert(lease_ok(v, log, h));
        let l = v.leases[h];
        assert forall|i: nat| i < l.table.len() implies #[trigger] blk_ok(v2, log, l, i) by {
            assert(blk_ok(v, log, l, i));
        }
    }
    assert forall|x: PageId| (x as nat) < v2.p implies #[trigger] page_ok(v2, log, x) by {
        assert(page_ok(v, log, x));
        assert(hold_ok(v, x));
        if v.keys[x as int] is Some {
            lemma_pub_frame(v, v2, log, log, x);
        }
    }
    assert forall|t: u64| #[trigger] v2.pend.contains_key(t) implies pend_ok(v2, t) by {
        assert(pend_ok(v, t));
    }
    lemma_last_frame(v, v2);
}

/// Reclaim keeps `Valid`: the range is idle, so no lease references it, and its keys go.
pub proof fn lemma_reclaim_inv(v: MgrV, log: Log, lo: nat, n: nat)
    requires
        inv(v, log),
        lo + n <= v.p,
        idle_range(v, lo, n),
    ensures
        inv(reclaimed(v, lo, n), log),
{
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    let v2 = reclaimed(v, lo, n);
    // No lease's table touches the range.
    assert forall|h: u64, i: int|
        v.leases.contains_key(h) && 0 <= i < v.leases[h].table.len() implies !in_range(
        #[trigger] v.leases[h].table[i] as int,
        lo,
        n,
    ) by {
        let x = v.leases[h].table[i];
        assert(lease_ok(v, log, h));
        assert(page_ok(v, log, x));
        assert(v.holders[x as int].contains(h));
        vstd::set::lemma_set_contains_len(v.holders[x as int], h);
        if in_range(x as int, lo, n) {
            assert(v.refs[x as int] == 0);
        }
    }
    assert forall|h: u64| #[trigger] v2.leases.contains_key(h) implies lease_ok(v2, log, h) by {
        assert(lease_ok(v, log, h));
        let l = v.leases[h];
        assert forall|i: int| 0 <= i < l.table.len() implies v2.keys[#[trigger] l.table[i] as int]
            == v.keys[l.table[i] as int] by {
            assert(!in_range(l.table[i] as int, lo, n));
        }
        lemma_lease_frame(v, v2, log, log, h);
    }
    assert forall|x: PageId| (x as nat) < v2.p implies #[trigger] page_ok(v2, log, x) by {
        assert(page_ok(v, log, x));
        assert(hold_ok(v, x));
        if in_range(x as int, lo, n) {
            assert(v.refs[x as int] == 0);
        } else if v.keys[x as int] is Some {
            lemma_pub_frame(v, v2, log, log, x);
        }
    }
    assert forall|t: u64| #[trigger] v2.pend.contains_key(t) implies pend_ok(v2, t) by {
        assert(pend_ok(v, t));
    }
    lemma_last_frame(v, v2);
}

impl Manager {
    pub fn units(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self@.p,
    {
        self.p
    }

    /// Whether every unit of `[lo, lo+n)` is owned and unreferenced.
    pub fn range_idle(&self, lo: usize, n: usize) -> (r: bool)
        requires
            self.valid(),
            lo + n <= self@.p,
        ensures
            r == idle_range(self@, lo as nat, n as nat),
    {
        let mut x = lo;
        while x < lo + n
            invariant
                self.valid(),
                lo <= x <= lo + n,
                lo + n <= self@.p,
                forall|y: int| lo <= y < x ==> self@.own[y] && self@.refs[y] == 0,
            decreases lo + n - x,
        {
            if !self.own[x] || self.refs[x] != 0 {
                proof {
                    assert(in_range(x as int, lo as nat, n as nat));
                }
                return false;
            }
            x += 1;
        }
        true
    }

    /// Whether every unit of `[lo, lo+n)` is unowned.
    pub fn range_unowned(&self, lo: usize, n: usize) -> (r: bool)
        requires
            self.valid(),
            lo + n <= self@.p,
        ensures
            r == unowned_range(self@, lo as nat, n as nat),
    {
        let mut x = lo;
        while x < lo + n
            invariant
                self.valid(),
                lo <= x <= lo + n,
                lo + n <= self@.p,
                forall|y: int| lo <= y < x ==> !self@.own[y],
            decreases lo + n - x,
        {
            if self.own[x] {
                proof {
                    assert(in_range(x as int, lo as nat, n as nat));
                }
                return false;
            }
            x += 1;
        }
        true
    }

    /// Every candidate page of key `k` in this class (`Index_c[k]`).
    pub fn candidates(&self, k: &Digest) -> (r: Vec<PageId>)
        requires
            self.valid(),
        ensures
            r@.no_duplicates(),
            forall|x: PageId| #[trigger] r@.contains(x) <==> in_index(self@.keys, *k, x),
    {
        proof {
            self.lemma_valid();
        }
        self.index.candidates(&self.keys, k)
    }

    /// Number of free units `|F_c|`.
    pub fn free_len(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self@.free_set().len(),
    {
        self.free.len()
    }

    /// Gives the unowned range `[lo, lo+n)` to this class: its units enter `F` (ref 0, no key).
    pub fn grant_range(&mut self, lo: usize, n: usize)
        requires
            old(self).valid(),
            lo + n <= old(self)@.p,
            unowned_range(old(self)@, lo as nat, n as nat),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            final(self)@ == granted(old(self)@, lo as nat, n as nat),
            final(self)@.free_set().len() == old(self)@.free_set().len() + n,
    {
        proof {
            self.lemma_valid();
        }
        let ghost v = self@;
        let ghost log = self.den_log();
        let mut x = lo;
        proof {
            lemma_free_of(v.p, v.refs, v.own);
            assert(self.free@ == v.free_set());
            reveal(page_ok);
            assert forall|y: int| #![trigger v.refs[y]] lo <= y < lo + n implies v.refs[y] == 0 by {
                assert(in_range(y, lo as nat, n as nat));
                assert(page_ok(v, log, y as PageId));
            }
        }
        while x < lo + n
            invariant
                lo <= x <= lo + n,
                lo + n <= v.p,
                v.p == self.p as nat,
                self.own@.len() == v.p,
                self.free.wf(),
                self.free.universe() == v.p,
                unowned_range(v, lo as nat, n as nat),
                forall|y: int| 0 <= y < v.p ==> #[trigger] self.own@[y] == if lo <= y < x { true } else { v.own[y] },
                forall|y: PageId| #[trigger] self.free@.contains(y) <==> ((y as nat) < v.p && v.refs[y as int] == 0
                    && self.own@[y as int]),
                forall|y: int| #![trigger v.refs[y]] lo <= y < lo + n ==> v.refs[y] == 0,
                self.free@.len() == v.free_set().len() + (x - lo),
            decreases lo + n - x,
        {
            proof {
                assert(in_range(x as int, lo as nat, n as nat));
                assert(!self.own@[x as int]);
                assert(!self.free@.contains(x));
                vstd::set::lemma_set_insert_len(self.free@, x);
            }
            self.free.insert(x);
            self.own.set(x, true);
            x += 1;
        }
        let ghost v2 = granted(v, lo as nat, n as nat);
        proof {
            lemma_grant_inv(v, log, lo as nat, n as nat);
        }
        self.g = Ghost(v2);
        proof {
            assert(self.own@ =~= v2.own);
            lemma_free_of(v.p, v2.refs, v2.own);
            assert(self.free@ =~= v2.free_set());
        }
    }

    /// Takes the idle range `[lo, lo+n)` from this class, revoking every key in it (§3.5 rule 3).
    pub fn reclaim_range(&mut self, lo: usize, n: usize)
        requires
            old(self).valid(),
            lo + n <= old(self)@.p,
            idle_range(old(self)@, lo as nat, n as nat),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            final(self)@ == reclaimed(old(self)@, lo as nat, n as nat),
            final(self)@.free_set().len() + n == old(self)@.free_set().len(),
    {
        proof {
            self.lemma_valid();
        }
        let ghost v = self@;
        let ghost log = self.den_log();
        proof {
            lemma_free_of(v.p, v.refs, v.own);
        }
        let mut x = lo;
        while x < lo + n
            invariant
                lo <= x <= lo + n,
                lo + n <= v.p,
                v.p == self.p as nat,
                self.own@.len() == v.p,
                self.keys@.len() == v.p,
                self.index.wf(self.keys@),
                self.free.wf(),
                self.free.universe() == v.p,
                idle_range(v, lo as nat, n as nat),
                forall|y: int| 0 <= y < v.p ==> #[trigger] self.own@[y] == if lo <= y < x { false } else { v.own[y] },
                forall|y: int| 0 <= y < v.p ==> #[trigger] self.keys@[y] == if lo <= y < x { None } else { v.keys[y] },
                forall|y: PageId| #[trigger] self.free@.contains(y) <==> ((y as nat) < v.p && v.refs[y as int] == 0
                    && self.own@[y as int]),
                self.free@.len() + (x - lo) == v.free_set().len(),
            decreases lo + n - x,
        {
            proof {
                assert(in_range(x as int, lo as nat, n as nat));
                assert(self.own@[x as int] && v.refs[x as int] == 0);
                assert(self.free@.contains(x));
                vstd::set::lemma_set_remove_len(self.free@, x);
            }
            self.free.remove(x);
            self.own.set(x, false);
            let kx = self.keys[x];
            match kx {
                Some(kd) => {
                    self.index.remove(Ghost(self.keys@), x, &kd);
                    self.keys.set(x, None);
                },
                None => {},
            }
            x += 1;
        }
        let ghost v2 = reclaimed(v, lo as nat, n as nat);
        proof {
            lemma_reclaim_inv(v, log, lo as nat, n as nat);
        }
        self.g = Ghost(v2);
        proof {
            assert(self.own@ =~= v2.own);
            assert(self.keys@ =~= v2.keys);
            lemma_free_of(v.p, v2.refs, v2.own);
            assert(self.free@ =~= v2.free_set());
        }
    }
}

} // verus!
