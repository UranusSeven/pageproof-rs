//! `IdxSet`: a verified O(1) set of page ids in `[0, n)` (stack + position array).
//! Used for the free sets. No trusted content.
use vstd::prelude::*;

verus! {

pub struct IdxSet {
    items: Vec<usize>,
    pos: Vec<usize>,
}

impl IdxSet {
    pub closed spec fn view(&self) -> Set<usize> {
        self.items@.to_set()
    }

    pub closed spec fn universe(&self) -> nat {
        self.pos@.len()
    }

    /// Public facts implied by well-formedness.
    pub proof fn lemma_bounds(&self)
        requires
            self.wf(),
        ensures
            self@.len() <= self.universe(),
            forall|b: usize| #[trigger] self@.contains(b) ==> (b as nat) < self.universe(),
    {
        self.lemma_wf();
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.items@.no_duplicates()
        &&& self.items@.len() <= self.pos@.len()
        &&& forall|i: int|
            0 <= i < self.items@.len() ==> (#[trigger] self.items@[i] as int) < self.pos@.len()
                && self.pos@[self.items@[i] as int] == i
    }

    proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self@.len() == self.items@.len(),
            self@.len() <= self.universe(),
            forall|b: usize| #[trigger] self@.contains(b) ==> (b as nat) < self.universe(),
    {
        self.items@.unique_seq_to_set();
    }

    pub fn new_empty(n: usize) -> (s: Self)
        ensures
            s.wf(),
            s.universe() == n,
            s@ == Set::<usize>::empty(),
    {
        let pos = vec![0usize; n];
        let s = IdxSet { items: Vec::new(), pos };
        assert(s@ =~= Set::<usize>::empty());
        s
    }

    pub fn new_full(n: usize) -> (s: Self)
        ensures
            s.wf(),
            s.universe() == n,
            forall|b: usize| #[trigger] s@.contains(b) <==> (b as nat) < n,
    {
        let mut items: Vec<usize> = Vec::new();
        let mut pos: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                items@.len() == i,
                pos@.len() == i,
                forall|j: int| 0 <= j < i ==> items@[j] == j && pos@[j] == j,
            decreases n - i,
        {
            items.push(i);
            pos.push(i);
            i += 1;
        }
        let s = IdxSet { items, pos };
        assert forall|b: usize| #[trigger] s@.contains(b) <==> (b as nat) < n by {
            if (b as nat) < n {
                assert(s.items@[b as int] == b);
            }
            if s@.contains(b) {
                let j = choose|j: int| 0 <= j < s.items@.len() && s.items@[j] == b;
            }
        }
        s
    }

    pub fn len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r as nat == self@.len(),
    {
        proof {
            self.lemma_wf();
        }
        self.items.len()
    }

    pub fn contains(&self, b: usize) -> (r: bool)
        requires
            self.wf(),
            (b as nat) < self.universe(),
        ensures
            r == self@.contains(b),
    {
        let p = self.pos[b];
        if p < self.items.len() && self.items[p] == b {
            true
        } else {
            proof {
                if self@.contains(b) {
                    let j = choose|j: int| 0 <= j < self.items@.len() && self.items@[j] == b;
                    assert(self.pos@[b as int] == j);
                }
            }
            false
        }
    }

    pub fn insert(&mut self, b: usize)
        requires
            old(self).wf(),
            (b as nat) < old(self).universe(),
            !old(self)@.contains(b),
        ensures
            final(self).wf(),
            final(self).universe() == old(self).universe(),
            final(self)@ == old(self)@.insert(b),
    {
        proof {
            self.lemma_wf();
            assert(self.items@.len() < self.pos@.len()) by {
                // b is a member of the universe not in the set, so the set is not full.
                let hi: usize = self.pos.len();
                vstd::set_lib::range_set_properties::<usize>(0usize, hi);
                let r = Set::<usize>::range(0usize, hi);
                assert forall|x: usize| #[trigger] self@.contains(x) implies r.contains(x) by {
                    let k = choose|k: int| 0 <= k < self.items@.len() && self.items@[k] == x;
                }
                assert(self@.insert(b).subset_of(r));
                assert(r.contains(b));
                vstd::set_lib::lemma_len_subset(self@.insert(b), r);
            }
        }
        let n = self.items.len();
        self.items.push(b);
        self.pos[b] = n;
        assert(self.items@ == old(self).items@.push(b));
        assert forall|x: usize| #[trigger] self@.contains(x) <==> old(self)@.insert(b).contains(x) by {
            vstd::seq_lib::lemma_seq_contains_after_push(old(self).items@, b, x);
        }
        assert(self@ =~= old(self)@.insert(b));
        assert(self.items@.no_duplicates()) by {
            assert forall|i: int, j: int|
                0 <= i < self.items@.len() && 0 <= j < self.items@.len() && i != j implies self.items@[i]
                != self.items@[j] by {
                if i == n as int || j == n as int {
                    if i < n as int {
                        assert(old(self).items@.contains(old(self).items@[i]));
                    }
                    if j < n as int {
                        assert(old(self).items@.contains(old(self).items@[j]));
                    }
                }
            }
        }
        assert forall|i: int|
            0 <= i < self.items@.len() implies (#[trigger] self.items@[i] as int) < self.pos@.len()
            && self.pos@[self.items@[i] as int] == i by {
            if i < n as int {
                assert(old(self).items@.contains(old(self).items@[i]));
                assert(self.items@[i] != b);
            }
        }
    }

    pub fn remove(&mut self, b: usize)
        requires
            old(self).wf(),
            old(self)@.contains(b),
        ensures
            final(self).wf(),
            final(self).universe() == old(self).universe(),
            final(self)@ == old(self)@.remove(b),
    {
        let ghost j0 = choose|j: int| 0 <= j < self.items@.len() && self.items@[j] == b;
        let i = self.pos[b];
        assert(i == j0);
        let last = self.items.pop().unwrap();
        let n = self.items.len();
        if i < n {
            self.items.set(i, last);
            self.pos[last] = i;
        }
        let ghost s0 = old(self).items@;
        assert(self@ =~= old(self)@.remove(b)) by {
            assert forall|x: usize| #[trigger] self@.contains(x) <==> old(self)@.remove(b).contains(x) by {
                if self@.contains(x) {
                    let k = choose|k: int| 0 <= k < self.items@.len() && self.items@[k] == x;
                    if k == i as int {
                        assert(x == s0[n as int]);
                        assert(s0.contains(x));
                    } else {
                        assert(s0[k] == x);
                        assert(s0.contains(x));
                    }
                }
                if old(self)@.remove(b).contains(x) {
                    let k = choose|k: int| 0 <= k < s0.len() && s0[k] == x;
                    if k == n as int {
                        assert(self.items@[i as int] == x);
                    } else {
                        assert(self.items@[k] == x);
                    }
                }
            }
        }
        assert(self.items@.no_duplicates()) by {
            assert forall|p: int, q: int|
                0 <= p < self.items@.len() && 0 <= q < self.items@.len() && p != q implies self.items@[p]
                != self.items@[q] by {
                let sp = if p == i as int { n as int } else { p };
                let sq = if q == i as int { n as int } else { q };
                assert(self.items@[p] == s0[sp]);
                assert(self.items@[q] == s0[sq]);
            }
        }
        assert forall|k: int|
            0 <= k < self.items@.len() implies (#[trigger] self.items@[k] as int) < self.pos@.len()
            && self.pos@[self.items@[k] as int] == k by {
            if k == i as int {
                assert(self.items@[k] == last);
            } else {
                assert(self.items@[k] == s0[k]);
                assert(s0[k] != last) by {
                    assert(s0[n as int] == last);
                }
            }
        }
    }

    /// Returns some element without removing it.
    pub fn peek(&self) -> (b: usize)
        requires
            self.wf(),
            self@.len() > 0,
        ensures
            self@.contains(b),
    {
        proof {
            self.lemma_wf();
        }
        let n = self.items.len();
        let b = self.items[n - 1];
        assert(self.items@.contains(b));
        b
    }

    /// Removes and returns some element.
    pub fn pop_any(&mut self) -> (b: usize)
        requires
            old(self).wf(),
            old(self)@.len() > 0,
        ensures
            final(self).wf(),
            final(self).universe() == old(self).universe(),
            old(self)@.contains(b),
            final(self)@ == old(self)@.remove(b),
    {
        proof {
            self.lemma_wf();
        }
        let n = self.items.len();
        let b = self.items[n - 1];
        assert(self.items@.contains(b));
        self.remove(b);
        b
    }
}

} // verus!
