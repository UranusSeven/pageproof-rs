//! v0.3 state class (contract D13, I14, I15): one exclusive live slot per lease, updated in place,
//! never keyed, published or shared. Units live in slabs owned by the class. No trusted content.
use vstd::prelude::*;
use crate::spec::*;
use crate::idxset::IdxSet;
#[cfg(verus_keep_ghost)]
use crate::ops_slab::in_range;

verus! {

/// Ghost provenance of a state unit: `Some(tau)` when it holds the state after prefix `tau`
/// (namespace fixed per coordinator), `None` for `⊥`.
pub type StateW = Option<Seq<Token>>;

/// Abstract state of one state class.
pub ghost struct StateV {
    pub p: nat,
    pub own: Seq<bool>,
    /// The lease holding each unit, or `None` (I2 with ref ∈ {0,1}).
    pub holder: Seq<Option<u64>>,
    pub w: Seq<StateW>,
}

impl StateV {
    pub open spec fn free_set(self) -> Set<usize> {
        Set::<usize>::range(0, self.p as usize).filter(|x: usize| self.own[x as int] && self.holder[x as int] is None)
    }

    pub open spec fn wf(self) -> bool {
        &&& self.own.len() == self.p
        &&& self.holder.len() == self.p
        &&& self.w.len() == self.p
        &&& forall|x: int| 0 <= x < self.p && #[trigger] self.holder[x] is Some ==> self.own[x]
        &&& forall|x: int| 0 <= x < self.p && !#[trigger] self.own[x] ==> self.w[x] is None
        &&& forall|x: int, y: int|
            0 <= x < self.p && 0 <= y < self.p && x != y && #[trigger] self.holder[x] is Some ==> #[trigger] self.holder[y]
                != self.holder[x]
    }
}

pub struct StatePool {
    pub(crate) p: usize,
    pub(crate) own: Vec<bool>,
    pub(crate) used: Vec<bool>,
    pub(crate) free: IdxSet,
    pub(crate) g: Ghost<StateV>,
}

impl StatePool {
    pub open(crate) spec fn view(&self) -> StateV {
        self.g@
    }

    pub open(crate) spec fn valid(&self) -> bool {
        let v = self.g@;
        &&& v.wf()
        &&& v.p == self.p as nat
        &&& v.p <= usize::MAX
        &&& self.own@ == v.own
        &&& self.used@.len() == v.p
        &&& forall|x: int| 0 <= x < v.p ==> #[trigger] self.used@[x] == (v.holder[x] is Some)
        &&& self.free.wf()
        &&& self.free.universe() == v.p
        &&& self.free@ == v.free_set()
    }

    pub proof fn lemma_free(&self)
        requires
            self.valid(),
        ensures
            forall|x: usize| #[trigger] self@.free_set().contains(x) <==> ((x as nat) < self@.p && self@.own[x as int]
                && self@.holder[x as int] is None),
    {
        vstd::set_lib::range_set_properties::<usize>(0usize, self.p);
    }

    /// A state class over `p` units, owning none.
    pub fn new(p: usize) -> (r: StatePool)
        ensures
            r.valid(),
            r@.p == p as nat,
            r@.own == Seq::new(p as nat, |x: int| false),
            r@.holder == Seq::new(p as nat, |x: int| None::<u64>),
            r@.w == Seq::new(p as nat, |x: int| None::<Seq<Token>>),
    {
        let own: Vec<bool> = vec![false; p];
        let used: Vec<bool> = vec![false; p];
        let ghost v = StateV {
            p: p as nat,
            own: Seq::new(p as nat, |x: int| false),
            holder: Seq::new(p as nat, |x: int| None),
            w: Seq::new(p as nat, |x: int| None),
        };
        let r = StatePool { p, own, used, free: IdxSet::new_empty(p), g: Ghost(v) };
        proof {
            assert(r.own@ =~= v.own);
            vstd::set_lib::range_set_properties::<usize>(0usize, p);
            assert(r.free@ =~= v.free_set());
        }
        r
    }

    pub fn units(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self@.p,
    {
        self.p
    }

    pub fn free_len(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self@.free_set().len(),
    {
        self.free.len()
    }

    /// Every unit of `[lo, lo+n)` is owned and held by no lease.
    pub fn range_idle(&self, lo: usize, n: usize) -> (r: bool)
        requires
            self.valid(),
            lo + n <= self@.p,
        ensures
            r == (forall|x: int| #[trigger] in_range(x, lo as nat, n as nat) ==> self@.own[x] && self@.holder[x] is None),
    {
        let mut x = lo;
        while x < lo + n
            invariant
                self.valid(),
                lo <= x <= lo + n,
                lo + n <= self@.p,
                forall|y: int| lo <= y < x ==> self@.own[y] && self@.holder[y] is None,
            decreases lo + n - x,
        {
            if !self.own[x] || self.used[x] {
                proof {
                    assert(in_range(x as int, lo as nat, n as nat));
                }
                return false;
            }
            x += 1;
        }
        true
    }

    /// Gives the unowned range `[lo, lo+n)` to this class.
    pub fn grant_range(&mut self, lo: usize, n: usize)
        requires
            old(self).valid(),
            lo + n <= old(self)@.p,
            forall|x: int| #[trigger] in_range(x, lo as nat, n as nat) ==> !old(self)@.own[x],
        ensures
            final(self).valid(),
            final(self)@ == (StateV {
                own: Seq::new(old(self)@.p, |x: int| if in_range(x, lo as nat, n as nat) { true } else { old(self)@.own[x] }),
                ..old(self)@
            }),
            final(self)@.free_set().len() == old(self)@.free_set().len() + n,
    {
        let ghost v = self@;
        proof {
            self.lemma_free();
        }
        let mut x = lo;
        while x < lo + n
            invariant
                lo <= x <= lo + n,
                lo + n <= v.p,
                v.wf(),
                v.p == self.p as nat,
                self.own@.len() == v.p,
                self.used@ == old(self).used@,
                self.g@ == v,
                self.free.wf(),
                self.free.universe() == v.p,
                forall|y: int| #[trigger] in_range(y, lo as nat, n as nat) ==> !v.own[y],
                forall|y: int| 0 <= y < v.p ==> #[trigger] self.own@[y] == if lo <= y < x { true } else { v.own[y] },
                forall|y: usize| #[trigger] self.free@.contains(y) <==> ((y as nat) < v.p && self.own@[y as int]
                    && v.holder[y as int] is None),
                forall|y: int| 0 <= y < v.p ==> #[trigger] self.used@[y] == (v.holder[y] is Some),
                self.free@.len() == v.free_set().len() + (x - lo),
            decreases lo + n - x,
        {
            proof {
                assert(in_range(x as int, lo as nat, n as nat));
                assert(v.holder[x as int] is None);
                assert(!self.free@.contains(x));
                vstd::set::lemma_set_insert_len(self.free@, x);
            }
            self.free.insert(x);
            self.own.set(x, true);
            x += 1;
        }
        let ghost v2 = StateV {
            own: Seq::new(v.p, |y: int| if in_range(y, lo as nat, n as nat) { true } else { v.own[y] }),
            ..v
        };
        self.g = Ghost(v2);
        proof {
            assert(self.own@ =~= v2.own);
            vstd::set_lib::range_set_properties::<usize>(0usize, self.p);
            assert(self.free@ =~= v2.free_set());
        }
    }

    /// Takes the idle range `[lo, lo+n)` from this class; its provenance becomes `⊥`.
    pub fn reclaim_range(&mut self, lo: usize, n: usize)
        requires
            old(self).valid(),
            lo + n <= old(self)@.p,
            forall|x: int| #[trigger] in_range(x, lo as nat, n as nat) ==> old(self)@.own[x] && old(self)@.holder[x] is None,
        ensures
            final(self).valid(),
            final(self)@ == (StateV {
                own: Seq::new(old(self)@.p, |x: int| if in_range(x, lo as nat, n as nat) { false } else { old(self)@.own[x] }),
                w: Seq::new(old(self)@.p, |x: int| if in_range(x, lo as nat, n as nat) { None } else { old(self)@.w[x] }),
                ..old(self)@
            }),
            final(self)@.free_set().len() + n == old(self)@.free_set().len(),
    {
        let ghost v = self@;
        proof {
            self.lemma_free();
        }
        let mut x = lo;
        while x < lo + n
            invariant
                lo <= x <= lo + n,
                lo + n <= v.p,
                v.wf(),
                v.p == self.p as nat,
                self.own@.len() == v.p,
                self.used@ == old(self).used@,
                self.g@ == v,
                self.free.wf(),
                self.free.universe() == v.p,
                forall|y: int| #[trigger] in_range(y, lo as nat, n as nat) ==> v.own[y] && v.holder[y] is None,
                forall|y: int| 0 <= y < v.p ==> #[trigger] self.own@[y] == if lo <= y < x { false } else { v.own[y] },
                forall|y: usize| #[trigger] self.free@.contains(y) <==> ((y as nat) < v.p && self.own@[y as int]
                    && v.holder[y as int] is None),
                forall|y: int| 0 <= y < v.p ==> #[trigger] self.used@[y] == (v.holder[y] is Some),
                self.free@.len() + (x - lo) == v.free_set().len(),
            decreases lo + n - x,
        {
            proof {
                assert(in_range(x as int, lo as nat, n as nat));
                assert(self.free@.contains(x));
                vstd::set::lemma_set_remove_len(self.free@, x);
            }
            self.free.remove(x);
            self.own.set(x, false);
            x += 1;
        }
        let ghost v2 = StateV {
            own: Seq::new(v.p, |y: int| if in_range(y, lo as nat, n as nat) { false } else { v.own[y] }),
            w: Seq::new(v.p, |y: int| if in_range(y, lo as nat, n as nat) { None } else { v.w[y] }),
            ..v
        };
        self.g = Ghost(v2);
        proof {
            assert(self.own@ =~= v2.own);
            vstd::set_lib::range_set_properties::<usize>(0usize, self.p);
            assert(self.free@ =~= v2.free_set());
            assert forall|y: int, z: int|
                0 <= y < v2.p && 0 <= z < v2.p && y != z && #[trigger] v2.holder[y] is Some implies #[trigger] v2.holder[z]
                != v2.holder[y] by {}
        }
    }

    /// Takes a free unit for lease `h` (C1). Its contents are unconstrained (`W = ⊥`).
    pub fn acquire(&mut self, Ghost(h): Ghost<u64>) -> (x: usize)
        requires
            old(self).valid(),
            old(self)@.free_set().len() > 0,
            forall|y: int| 0 <= y < old(self)@.p ==> #[trigger] old(self)@.holder[y] != Some(h),
        ensures
            final(self).valid(),
            old(self)@.free_set().contains(x),
            final(self)@.free_set().len() + 1 == old(self)@.free_set().len(),
            final(self)@ == (StateV {
                holder: old(self)@.holder.update(x as int, Some(h)),
                w: old(self)@.w.update(x as int, None),
                ..old(self)@
            }),
    {
        let ghost v = self@;
        proof {
            self.lemma_free();
        }
        let ghost f0 = self.free@;
        let x = self.free.pop_any();
        proof {
            vstd::set::lemma_set_remove_len(f0, x);
        }
        self.used.set(x, true);
        let ghost v2 = StateV { holder: v.holder.update(x as int, Some(h)), w: v.w.update(x as int, None), ..v };
        self.g = Ghost(v2);
        proof {
            vstd::set_lib::range_set_properties::<usize>(0usize, self.p);
            assert(self.free@ =~= v2.free_set());
            assert forall|y: int, z: int|
                0 <= y < v2.p && 0 <= z < v2.p && y != z && #[trigger] v2.holder[y] is Some implies #[trigger] v2.holder[z]
                != v2.holder[y] by {
                if y != x as int && z != x as int {
                    assert(v.holder[y] is Some);
                }
            }
        }
        x
    }

    /// Returns slot `x` of a released lease to `F` (C5). Its provenance becomes `⊥`.
    pub fn release_slot(&mut self, x: usize)
        requires
            old(self).valid(),
            (x as nat) < old(self)@.p,
            old(self)@.holder[x as int] is Some,
        ensures
            final(self).valid(),
            final(self)@ == (StateV {
                holder: old(self)@.holder.update(x as int, None),
                w: old(self)@.w.update(x as int, None),
                ..old(self)@
            }),
    {
        let ghost v = self@;
        proof {
            self.lemma_free();
            assert(!self.free@.contains(x));
        }
        self.used.set(x, false);
        self.free.insert(x);
        let ghost v2 = StateV { holder: v.holder.update(x as int, None), w: v.w.update(x as int, None), ..v };
        self.g = Ghost(v2);
        proof {
            vstd::set_lib::range_set_properties::<usize>(0usize, self.p);
            assert(self.free@ =~= v2.free_set());
        }
    }

    /// Ghost update of a held slot's provenance (C4: the slot now holds the state after `tau`).
    // `x` names the slot in the contract only; the update is ghost.
    #[allow(unused_variables)]
    pub fn set_w(&mut self, x: usize, Ghost(tau): Ghost<Seq<Token>>)
        requires
            old(self).valid(),
            (x as nat) < old(self)@.p,
            old(self)@.holder[x as int] is Some,
        ensures
            final(self).valid(),
            final(self)@ == (StateV { w: old(self)@.w.update(x as int, Some(tau)), ..old(self)@ }),
    {
        let ghost v = self@;
        let ghost v2 = StateV { w: v.w.update(x as int, Some(tau)), ..v };
        self.g = Ghost(v2);
        proof {
            assert(self.free@ =~= v2.free_set());
        }
    }
}

} // verus!
