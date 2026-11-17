//! `IdxList`: a verified ordered set of ids in `[0, n)`: a doubly linked list threaded through
//! two arrays, with O(1) push at either end, pop from the front, and removal of any member. The
//! paged free sets use it; the list order is the order in which fresh pages are taken
//! (`manager::keyed_last`). No trusted content.
use vstd::prelude::*;

verus! {

/// The null link.
pub const NIL: usize = usize::MAX;

/// The member after position `i` of `s`, or `NIL` at the end.
pub open spec fn succ(s: Seq<usize>, i: int) -> usize {
    if i + 1 < s.len() { s[i + 1] } else { NIL }
}

/// The member before position `i` of `s`, or `NIL` at the start.
pub open spec fn pred(s: Seq<usize>, i: int) -> usize {
    if i > 0 { s[i - 1] } else { NIL }
}

pub struct IdxList {
    /// `nxt[x]`: the member after `x`, or `NIL`.
    nxt: Vec<usize>,
    /// `prv[x]`: the member before `x`, or `NIL`.
    prv: Vec<usize>,
    head: usize,
    tail: usize,
    len: usize,
    /// The members in list order.
    s: Ghost<Seq<usize>>,
}

impl IdxList {
    /// The members in list order.
    pub closed spec fn order(&self) -> Seq<usize> {
        self.s@
    }

    pub open spec fn view(&self) -> Set<usize> {
        self.order().to_set()
    }

    pub closed spec fn universe(&self) -> nat {
        self.nxt@.len()
    }

    pub closed spec fn wf(&self) -> bool {
        let s = self.s@;
        let n = self.nxt@.len();
        &&& n < NIL
        &&& self.prv@.len() == n
        &&& s.no_duplicates()
        &&& self.len == s.len()
        &&& forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] as nat) < n
        &&& self.head == (if s.len() == 0 { NIL } else { s[0] })
        &&& self.tail == (if s.len() == 0 { NIL } else { s[s.len() - 1] })
        &&& forall|i: int| 0 <= i < s.len() ==> self.nxt@[#[trigger] s[i] as int] == succ(s, i)
        &&& forall|i: int| 0 <= i < s.len() ==> self.prv@[#[trigger] s[i] as int] == pred(s, i)
    }

    /// Public facts implied by well-formedness.
    pub proof fn lemma_bounds(&self)
        requires
            self.wf(),
        ensures
            self@.len() <= self.universe(),
            self@.len() == self.order().len(),
            self.order().no_duplicates(),
            forall|b: usize| #[trigger] self@.contains(b) ==> (b as nat) < self.universe(),
    {
        self.lemma_wf();
    }

    proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self@.len() == self.order().len(),
            self@.len() <= self.universe(),
            forall|b: usize| #[trigger] self@.contains(b) ==> (b as nat) < self.universe(),
    {
        let s = self.s@;
        s.unique_seq_to_set();
        let hi: usize = self.nxt.len();
        vstd::set_lib::range_set_properties::<usize>(0usize, hi);
        let r = Set::<usize>::range(0usize, hi);
        assert forall|x: usize| #[trigger] self@.contains(x) implies r.contains(x) by {
            let k = choose|k: int| 0 <= k < s.len() && s[k] == x;
        }
        vstd::set_lib::lemma_len_subset(self@, r);
    }

    pub fn new_empty(n: usize) -> (s: Self)
        requires
            n < NIL,
        ensures
            s.wf(),
            s.universe() == n,
            s.order() == Seq::<usize>::empty(),
            s@ == Set::<usize>::empty(),
    {
        let s = IdxList {
            nxt: vec![NIL; n],
            prv: vec![NIL; n],
            head: NIL,
            tail: NIL,
            len: 0,
            s: Ghost(Seq::empty()),
        };
        assert(s@ =~= Set::<usize>::empty());
        s
    }

    /// Every id of `[0, n)`, in increasing order.
    pub fn new_full(n: usize) -> (s: Self)
        requires
            n < NIL,
        ensures
            s.wf(),
            s.universe() == n,
            s.order() == Seq::new(n as nat, |j: int| j as usize),
            forall|b: usize| #[trigger] s@.contains(b) <==> (b as nat) < n,
    {
        let mut nxt: Vec<usize> = Vec::new();
        let mut prv: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n < NIL,
                nxt@.len() == i,
                prv@.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] nxt@[j] == (if j + 1 < n { (j + 1) as usize } else { NIL }),
                forall|j: int| 0 <= j < i ==> #[trigger] prv@[j] == (if j > 0 { (j - 1) as usize } else { NIL }),
            decreases n - i,
        {
            let ghost (n0, p0) = (nxt@, prv@);
            nxt.push(if i + 1 < n { i + 1 } else { NIL });
            prv.push(if i > 0 { i - 1 } else { NIL });
            proof {
                assert forall|j: int| 0 <= j < i implies nxt@[j] == n0[j] && prv@[j] == p0[j] by {}
            }
            i += 1;
        }
        let ghost sq = Seq::new(n as nat, |j: int| j as usize);
        let s = IdxList {
            nxt,
            prv,
            head: if n > 0 { 0 } else { NIL },
            tail: if n > 0 { n - 1 } else { NIL },
            len: n,
            s: Ghost(sq),
        };
        proof {
            assert forall|j: int| 0 <= j < sq.len() implies s.nxt@[#[trigger] sq[j] as int] == succ(sq, j) by {
                assert(sq[j] as int == j);
            }
            assert forall|j: int| 0 <= j < sq.len() implies s.prv@[#[trigger] sq[j] as int] == pred(sq, j) by {
                assert(sq[j] as int == j);
            }
        }
        assert forall|b: usize| #[trigger] s@.contains(b) <==> (b as nat) < n by {
            if (b as nat) < n {
                assert(sq[b as int] == b);
            }
        }
        s
    }

    pub fn len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r as nat == self@.len(),
            r as nat == self.order().len(),
    {
        proof {
            self.lemma_wf();
        }
        self.len
    }

    /// Inserts `b` as the first member.
    pub fn push_front(&mut self, b: usize)
        requires
            old(self).wf(),
            (b as nat) < old(self).universe(),
            !old(self)@.contains(b),
        ensures
            final(self).wf(),
            final(self).universe() == old(self).universe(),
            final(self).order() == seq![b] + old(self).order(),
            final(self)@ == old(self)@.insert(b),
    {
        proof {
            self.lemma_wf();
        }
        let ghost s0 = self.s@;
        let h = self.head;
        self.nxt.set(b, h);
        self.prv.set(b, NIL);
        if h == NIL {
            self.tail = b;
        } else {
            self.prv.set(h, b);
        }
        self.head = b;
        self.len = self.len + 1;
        let ghost s1 = seq![b] + s0;
        self.s = Ghost(s1);
        proof {
            let n = self.nxt@.len();
            assert(!s0.contains(b));
            assert forall|j: int| 0 <= j < s0.len() implies #[trigger] s1[j + 1] == s0[j] by {}
            assert(s1[0] == b);
            assert forall|x: usize| #[trigger] s1.contains(x) <==> (x == b || s0.contains(x)) by {
                if s0.contains(x) {
                    let k = choose|k: int| 0 <= k < s0.len() && s0[k] == x;
                    assert(s1[k + 1] == x);
                }
                if s1.contains(x) && x != b {
                    let k = choose|k: int| 0 <= k < s1.len() && s1[k] == x;
                    assert(s0[k - 1] == x);
                }
            }
            assert(s1.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < s1.len() && 0 <= j < s1.len() && i != j implies s1[i] != s1[j] by {
                    if i == 0 {
                        assert(s0.contains(s1[j]));
                    } else if j == 0 {
                        assert(s0.contains(s1[i]));
                    } else {
                        assert(s1[i] == s0[i - 1] && s1[j] == s0[j - 1]);
                    }
                }
            }
            assert forall|i: int| 0 <= i < s1.len() implies (#[trigger] s1[i] as nat) < n by {
                if i > 0 {
                    assert(s1[i] == s0[i - 1]);
                }
            }
            assert forall|i: int| 0 <= i < s1.len() implies self.nxt@[#[trigger] s1[i] as int] == succ(s1, i) by {
                if i > 0 {
                    assert(s1[i] == s0[i - 1]);
                    assert(s0[i - 1] != b);
                    if i < s0.len() {
                        assert(s1[i + 1] == s0[i]);
                    }
                }
            }
            assert forall|i: int| 0 <= i < s1.len() implies self.prv@[#[trigger] s1[i] as int] == pred(s1, i) by {
                if i == 1 {
                    assert(s1[1] == s0[0]);
                } else if i > 1 {
                    assert(s1[i] == s0[i - 1]);
                    assert(s0[i - 1] != b);
                    assert(s0[i - 1] != s0[0]);
                    assert(s1[i - 1] == s0[i - 2]);
                }
            }
            assert(self@ =~= old(self)@.insert(b));
        }
    }

    /// Inserts `b` as the last member.
    pub fn push_back(&mut self, b: usize)
        requires
            old(self).wf(),
            (b as nat) < old(self).universe(),
            !old(self)@.contains(b),
        ensures
            final(self).wf(),
            final(self).universe() == old(self).universe(),
            final(self).order() == old(self).order().push(b),
            final(self)@ == old(self)@.insert(b),
    {
        proof {
            self.lemma_wf();
        }
        let ghost s0 = self.s@;
        let t = self.tail;
        self.prv.set(b, t);
        self.nxt.set(b, NIL);
        if t == NIL {
            self.head = b;
        } else {
            self.nxt.set(t, b);
        }
        self.tail = b;
        self.len = self.len + 1;
        let ghost s1 = s0.push(b);
        self.s = Ghost(s1);
        proof {
            let n = self.nxt@.len();
            let m = s0.len() as int;
            assert(!s0.contains(b));
            assert forall|x: usize| #[trigger] s1.contains(x) <==> (x == b || s0.contains(x)) by {
                vstd::seq_lib::lemma_seq_contains_after_push(s0, b, x);
            }
            assert(s1.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < s1.len() && 0 <= j < s1.len() && i != j implies s1[i] != s1[j] by {
                    if i == m {
                        assert(s0.contains(s1[j]));
                    } else if j == m {
                        assert(s0.contains(s1[i]));
                    }
                }
            }
            assert forall|i: int| 0 <= i < s1.len() implies self.nxt@[#[trigger] s1[i] as int] == succ(s1, i) by {
                if i < m {
                    assert(s1[i] == s0[i]);
                    assert(s0[i] != b);
                    if i < m - 1 {
                        assert(s0[i] != s0[m - 1]);
                    }
                }
            }
            assert forall|i: int| 0 <= i < s1.len() implies self.prv@[#[trigger] s1[i] as int] == pred(s1, i) by {
                if i < m {
                    assert(s1[i] == s0[i]);
                    assert(s0[i] != b);
                }
            }
            assert(self@ =~= old(self)@.insert(b));
        }
    }

    /// Removes the member `b`, wherever it is.
    pub fn remove(&mut self, b: usize)
        requires
            old(self).wf(),
            old(self)@.contains(b),
        ensures
            final(self).wf(),
            final(self).universe() == old(self).universe(),
            0 <= old(self).order().index_of(b) < old(self).order().len(),
            old(self).order()[old(self).order().index_of(b)] == b,
            final(self).order() == old(self).order().remove(old(self).order().index_of(b)),
            final(self)@ == old(self)@.remove(b),
    {
        let ghost s0 = self.s@;
        let ghost i = s0.index_of(b);
        proof {
            assert(s0.contains(b));
            assert(0 <= i < s0.len() && s0[i] == b);
        }
        let p = self.prv[b];
        let q = self.nxt[b];
        proof {
            assert(p == pred(s0, i));
            assert(q == succ(s0, i));
            if i > 0 {
                assert((s0[i - 1] as nat) < self.nxt@.len());
            }
            if i + 1 < s0.len() {
                assert((s0[i + 1] as nat) < self.nxt@.len());
            }
        }
        if p == NIL {
            self.head = q;
        } else {
            self.nxt.set(p, q);
        }
        if q == NIL {
            self.tail = p;
        } else {
            self.prv.set(q, p);
        }
        self.len = self.len - 1;
        let ghost s1 = s0.remove(i);
        self.s = Ghost(s1);
        proof {
            let n = self.nxt@.len();
            let m = s0.len() as int;
            s0.remove_ensures(i);
            assert forall|j: int| 0 <= j < s1.len() implies #[trigger] s1[j] == (if j < i { s0[j] } else { s0[j + 1] }) by {}
            assert forall|x: usize| #[trigger] s1.contains(x) <==> (x != b && s0.contains(x)) by {
                if s1.contains(x) {
                    let k = choose|k: int| 0 <= k < s1.len() && s1[k] == x;
                    if k < i {
                        assert(s0[k] == x && k != i);
                    } else {
                        assert(s0[k + 1] == x && k + 1 != i);
                    }
                }
                if x != b && s0.contains(x) {
                    let k = choose|k: int| 0 <= k < s0.len() && s0[k] == x;
                    if k < i {
                        assert(s1[k] == x);
                    } else {
                        assert(k != i);
                        assert(s1[k - 1] == x);
                    }
                }
            }
            assert(s1.no_duplicates()) by {
                assert forall|j1: int, j2: int| 0 <= j1 < s1.len() && 0 <= j2 < s1.len() && j1 != j2 implies s1[j1] != s1[j2] by {
                    let k1 = if j1 < i { j1 } else { j1 + 1 };
                    let k2 = if j2 < i { j2 } else { j2 + 1 };
                    assert(s1[j1] == s0[k1] && s1[j2] == s0[k2]);
                }
            }
            assert forall|j: int| 0 <= j < s1.len() implies (#[trigger] s1[j] as nat) < n by {
                if j < i {
                    assert(s1[j] == s0[j]);
                } else {
                    assert(s1[j] == s0[j + 1]);
                }
            }
            if i > 0 {
                assert(s1[0] == s0[0]);
            } else if m > 1 {
                assert(s1[0] == s0[1]);
            }
            if i < m - 1 {
                assert(s1[s1.len() - 1] == s0[m - 1]);
            } else if m > 1 {
                assert(s1[s1.len() - 1] == s0[m - 2]);
            }
            assert forall|j: int| 0 <= j < s1.len() implies self.nxt@[#[trigger] s1[j] as int] == succ(s1, j) by {
                if j < i - 1 {
                    assert(s1[j] == s0[j]);
                    assert(s0[j] != s0[i - 1]);
                    assert(s1[j + 1] == s0[j + 1]);
                } else if j == i - 1 {
                    assert(s1[j] == s0[i - 1]);
                    if i + 1 < m {
                        assert(s1[i] == s0[i + 1]);
                    }
                } else {
                    assert(s1[j] == s0[j + 1]);
                    assert(i > 0 ==> s0[j + 1] != s0[i - 1]);
                    if j + 2 < m {
                        assert(s1[j + 1] == s0[j + 2]);
                    }
                }
            }
            assert forall|j: int| 0 <= j < s1.len() implies self.prv@[#[trigger] s1[j] as int] == pred(s1, j) by {
                if j < i {
                    assert(s1[j] == s0[j]);
                    assert(i + 1 < m ==> s0[j] != s0[i + 1]);
                    if j > 0 {
                        assert(s1[j - 1] == s0[j - 1]);
                    }
                } else if j == i {
                    assert(s1[j] == s0[i + 1]);
                    if i > 0 {
                        assert(s1[i - 1] == s0[i - 1]);
                    }
                } else {
                    assert(s1[j] == s0[j + 1]);
                    assert(s0[j + 1] != s0[i + 1]);
                    assert(s1[j - 1] == s0[j]);
                }
            }
            assert(self@ =~= old(self)@.remove(b));
        }
    }

    /// Removes and returns the first member.
    pub fn pop_front(&mut self) -> (b: usize)
        requires
            old(self).wf(),
            old(self)@.len() > 0,
        ensures
            final(self).wf(),
            final(self).universe() == old(self).universe(),
            old(self).order().len() > 0,
            b == old(self).order()[0],
            old(self)@.contains(b),
            final(self).order() == old(self).order().remove(0),
            final(self)@ == old(self)@.remove(b),
    {
        proof {
            self.lemma_wf();
        }
        let ghost s0 = self.s@;
        let b = self.head;
        proof {
            assert(s0.len() > 0);
            assert(s0.contains(b)) by {
                assert(s0[0] == b);
            }
        }
        self.remove(b);
        proof {
            let i = s0.index_of(b);
            assert(s0[i] == b && s0[0] == b);
            assert(i == 0);
        }
        b
    }
}

} // verus!
