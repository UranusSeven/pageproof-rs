//! `KeyIndex`: the concrete representation of `Index : Map<Key, Set<PageId>>` (contract §3.4).
//!
//! Buckets are keyed by a 32-bit prefix of the digest; each bucket lists the pages whose full key
//! has that prefix. Lookups compare the full 256-bit digest (`digest_eq`), never tokens. The
//! abstract index is *derived* from the per-page keys: `Index[K] = {b | keys[b] == Some(K)}` (I8),
//! and `wf` states that the hash map represents exactly that relation. No trusted content.
use vstd::prelude::*;
use std::collections::HashMap;
use crate::spec::*;
use crate::e8::digest_eq;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub open spec fn short(k: Digest) -> u64 {
    ((k[0] as u64) + (k[1] as u64) * 256 + (k[2] as u64) * 65536 + (k[3] as u64) * 16777216) as u64
}

pub fn short_of(k: &Digest) -> (r: u64)
    ensures
        r == short(*k),
{
    (k[0] as u64) + (k[1] as u64) * 256 + (k[2] as u64) * 65536 + (k[3] as u64) * 16777216
}

/// Abstract index membership: page `b` is a candidate for key `k` (`b ∈ Index[k]`).
pub open spec fn in_index(keys: Seq<Option<Digest>>, k: Digest, b: usize) -> bool {
    (b as int) < keys.len() && keys[b as int] == Some(k)
}

/// Bucket entries are valid published pages with the bucket's short key.
pub open spec fn entry_ok(keys: Seq<Option<Digest>>, s: u64, b: usize) -> bool {
    &&& (b as int) < keys.len()
    &&& keys[b as int] is Some
    &&& short(keys[b as int]->Some_0) == s
}

pub open spec fn rep_ok(m: Map<u64, Vec<usize>>, keys: Seq<Option<Digest>>) -> bool {
    &&& forall|s: u64, j: int|
        #![trigger m[s]@[j]]
        m.contains_key(s) && 0 <= j < m[s]@.len() ==> entry_ok(keys, s, m[s]@[j])
    &&& forall|s: u64| #[trigger] m.contains_key(s) ==> m[s]@.no_duplicates()
    &&& forall|b: usize|
        #![trigger keys[b as int]]
        (b as int) < keys.len() && keys[b as int] is Some ==> {
            let s = short(keys[b as int]->Some_0);
            m.contains_key(s) && m[s]@.contains(b)
        }
}

pub struct KeyIndex {
    map: HashMap<u64, Vec<usize>>,
}

/// After `v.swap_remove(i)`.
pub open spec fn swap_removed(v0: Seq<usize>, v1: Seq<usize>, i: int) -> bool {
    &&& 0 <= i < v0.len()
    &&& v1.len() == v0.len() - 1
    &&& forall|j: int| 0 <= j < v1.len() && j != i ==> v1[j] == v0[j]
    &&& i < v1.len() ==> v1[i] == v0[v0.len() - 1]
}

proof fn lemma_swap_removed(v0: Seq<usize>, v1: Seq<usize>, i: int)
    requires
        swap_removed(v0, v1, i),
        v0.no_duplicates(),
    ensures
        v1.no_duplicates(),
        forall|x: usize| #[trigger] v1.contains(x) <==> (v0.contains(x) && x != v0[i]),
{
    assert forall|p: int, q: int| 0 <= p < v1.len() && 0 <= q < v1.len() && p != q implies v1[p] != v1[q] by {
        let pp = if p == i { v0.len() - 1 } else { p };
        let qq = if q == i { v0.len() - 1 } else { q };
        assert(v1[p] == v0[pp]);
        assert(v1[q] == v0[qq]);
    }
    assert forall|x: usize| #[trigger] v1.contains(x) <==> (v0.contains(x) && x != v0[i]) by {
        if v1.contains(x) {
            let p = choose|p: int| 0 <= p < v1.len() && v1[p] == x;
            let pp = if p == i { v0.len() - 1 } else { p };
            assert(v0[pp] == x);
            assert(pp != i);
        }
        if v0.contains(x) && x != v0[i] {
            let p = choose|p: int| 0 <= p < v0.len() && v0[p] == x;
            if p == v0.len() - 1 {
                assert(v1[i] == x);
            } else {
                assert(v1[p] == x);
            }
        }
    }
}

proof fn lemma_remove_rep(
    m0: Map<u64, Vec<usize>>,
    m1: Map<u64, Vec<usize>>,
    keys: Seq<Option<Digest>>,
    b: usize,
    k: Digest,
    v1: Vec<usize>,
)
    requires
        rep_ok(m0, keys),
        (b as int) < keys.len(),
        keys[b as int] == Some(k),
        m0.contains_key(short(k)),
        v1@.no_duplicates(),
        forall|x: usize| #[trigger] v1@.contains(x) <==> (m0[short(k)]@.contains(x) && x != b),
        m1 == m0.insert(short(k), v1),
    ensures
        rep_ok(m1, keys.update(b as int, None)),
{
    let s = short(k);
    let keys2 = keys.update(b as int, None);
    assert forall|s2: u64, j: int| m1.contains_key(s2) && 0 <= j < m1[s2]@.len() implies entry_ok(
        keys2,
        s2,
        #[trigger] m1[s2]@[j],
    ) by {
        let x = m1[s2]@[j];
        if s2 == s {
            assert(v1@.contains(x));
            let jj = choose|jj: int| 0 <= jj < m0[s]@.len() && m0[s]@[jj] == x;
            assert(entry_ok(keys, s, m0[s]@[jj]));
        } else {
            assert(m0[s2]@[j] == x);
            assert(entry_ok(keys, s2, m0[s2]@[j]));
        }
    }
    assert forall|b2: usize|
        (b2 as int) < keys2.len() && #[trigger] keys2[b2 as int] is Some implies {
            let s2 = short(keys2[b2 as int]->Some_0);
            m1.contains_key(s2) && m1[s2]@.contains(b2)
        } by {
        assert(b2 != b);
        assert(keys2[b2 as int] == keys[b2 as int]);
        let s2 = short(keys[b2 as int]->Some_0);
        assert(m0.contains_key(s2) && m0[s2]@.contains(b2));
    }
}

proof fn lemma_add_rep(
    m0: Map<u64, Vec<usize>>,
    m1: Map<u64, Vec<usize>>,
    keys: Seq<Option<Digest>>,
    b: usize,
    k: Digest,
    v0: Seq<usize>,
    v1: Vec<usize>,
)
    requires
        rep_ok(m0, keys),
        (b as int) < keys.len(),
        keys[b as int] is None,
        m0.contains_key(short(k)) ==> v0 == m0[short(k)]@,
        !m0.contains_key(short(k)) ==> v0 == Seq::<usize>::empty(),
        v1@ == v0.push(b),
        m1 == m0.insert(short(k), v1),
    ensures
        rep_ok(m1, keys.update(b as int, Some(k))),
{
    let s = short(k);
    let keys2 = keys.update(b as int, Some(k));
    assert(!v0.contains(b)) by {
        if v0.contains(b) {
            let j = choose|j: int| 0 <= j < v0.len() && v0[j] == b;
            assert(entry_ok(keys, s, m0[s]@[j]));
        }
    }
    assert forall|s2: u64, j: int| m1.contains_key(s2) && 0 <= j < m1[s2]@.len() implies entry_ok(
        keys2,
        s2,
        #[trigger] m1[s2]@[j],
    ) by {
        if s2 == s {
            if j < v0.len() {
                assert(entry_ok(keys, s, m0[s]@[j]));
                assert(v0[j] != b) by {
                    assert(v0.contains(v0[j]));
                }
            }
        } else {
            assert(entry_ok(keys, s2, m0[s2]@[j]));
            assert(m0[s2]@[j] != b);
        }
    }
    assert forall|s2: u64| #[trigger] m1.contains_key(s2) implies m1[s2]@.no_duplicates() by {
        if s2 == s {
            assert forall|i: int, j: int| 0 <= i < v1@.len() && 0 <= j < v1@.len() && i != j implies v1@[i]
                != v1@[j] by {
                if i < v0.len() && j < v0.len() {
                    if m0.contains_key(s) {
                        assert(m0[s]@.no_duplicates());
                    }
                } else if i < v0.len() {
                    assert(v0.contains(v0[i]));
                } else if j < v0.len() {
                    assert(v0.contains(v0[j]));
                }
            }
        }
    }
    assert forall|b2: usize|
        (b2 as int) < keys2.len() && #[trigger] keys2[b2 as int] is Some implies {
            let s2 = short(keys2[b2 as int]->Some_0);
            m1.contains_key(s2) && m1[s2]@.contains(b2)
        } by {
        if b2 == b {
            assert(v1@[v0.len() as int] == b);
        } else {
            assert(keys2[b2 as int] == keys[b2 as int]);
            let s2 = short(keys[b2 as int]->Some_0);
            assert(m0.contains_key(s2) && m0[s2]@.contains(b2));
            if s2 == s {
                let j = choose|j: int| 0 <= j < v0.len() && v0[j] == b2;
                assert(v1@[j] == b2);
            }
        }
    }
}

impl KeyIndex {
    pub closed spec fn wf(&self, keys: Seq<Option<Digest>>) -> bool {
        rep_ok(self.map@, keys)
    }

    pub fn new(Ghost(keys): Ghost<Seq<Option<Digest>>>) -> (r: Self)
        requires
            forall|b: int| 0 <= b < keys.len() ==> keys[b] is None,
        ensures
            r.wf(keys),
    {
        let r = KeyIndex { map: HashMap::new() };
        assert forall|b: usize| (b as int) < keys.len() && #[trigger] keys[b as int] is Some implies false by {
            assert(keys[b as int] is None);
        }
        r
    }

    /// Publishes page `b` under key `k`.
    pub fn add(&mut self, Ghost(keys): Ghost<Seq<Option<Digest>>>, b: usize, k: &Digest)
        requires
            old(self).wf(keys),
            (b as int) < keys.len(),
            keys[b as int] is None,
        ensures
            final(self).wf(keys.update(b as int, Some(*k))),
    {
        let s = short_of(k);
        let ghost m0 = self.map@;
        let bucket = self.map.remove(&s);
        let mut v: Vec<usize> = match bucket {
            Some(v) => v,
            None => Vec::new(),
        };
        let ghost v0 = v@;
        v.push(b);
        let ghost v1 = v;
        self.map.insert(s, v);
        proof {
            assert(self.map@ =~= m0.insert(s, v1));
            lemma_add_rep(m0, self.map@, keys, b, *k, v0, v1);
        }
    }

    /// Revokes page `b`'s key.
    pub fn remove(&mut self, Ghost(keys): Ghost<Seq<Option<Digest>>>, b: usize, k: &Digest)
        requires
            old(self).wf(keys),
            (b as int) < keys.len(),
            keys[b as int] == Some(*k),
        ensures
            final(self).wf(keys.update(b as int, None)),
    {
        let s = short_of(k);
        let ghost m0 = self.map@;
        assert(m0.contains_key(s) && m0[s]@.contains(b));
        let bucket = self.map.remove(&s);
        let mut v: Vec<usize> = bucket.unwrap();
        let ghost v0 = v@;
        let i = find_pos(&v, b);
        v.swap_remove(i);
        let ghost v1 = v;
        proof {
            assert(swap_removed(v0, v1@, i as int));
            lemma_swap_removed(v0, v1@, i as int);
        }
        self.map.insert(s, v);
        proof {
            assert(self.map@ =~= m0.insert(s, v1));
            lemma_remove_rep(m0, self.map@, keys, b, *k, v1);
        }
    }

    /// Finds a candidate page for key `k`, preferring a referenced one (D9).
    ///
    /// Returns `None` iff `Index[k]` is empty. `Some((b, active))`: `b` is a candidate, and
    /// `active` iff `refs[b] > 0`; if `!active`, no candidate is referenced.
    pub fn lookup(&self, keys: &Vec<Option<Digest>>, refs: &Vec<u64>, k: &Digest) -> (r: Option<(usize, bool)>)
        requires
            self.wf(keys@),
            refs@.len() == keys@.len(),
        ensures
            r is None ==> forall|b: usize| !#[trigger] in_index(keys@, *k, b),
            r matches Some((b, active)) ==> {
                &&& in_index(keys@, *k, b)
                &&& active == (refs@[b as int] > 0)
                &&& !active ==> forall|b2: usize| #[trigger] in_index(keys@, *k, b2) ==> refs@[b2 as int] == 0
            },
    {
        let s = short_of(k);
        match self.map.get(&s) {
            None => {
                proof {
                    assert forall|b: usize| !#[trigger] in_index(keys@, *k, b) by {
                        if in_index(keys@, *k, b) {
                            assert(keys@[b as int] is Some);
                        }
                    }
                }
                None
            },
            Some(v) => {
                proof {
                    assert(self.map@.contains_key(s) && self.map@[s] == *v);
                    assert forall|j: int| 0 <= j < v@.len() implies (#[trigger] v@[j] as int) < keys@.len() by {
                        assert(entry_ok(keys@, s, self.map@[s]@[j]));
                    }
                    assert forall|b2: usize| #[trigger] in_index(keys@, *k, b2) implies v@.contains(b2) by {
                        assert(keys@[b2 as int] is Some);
                    }
                }
                scan_bucket(v, keys, refs, k)
            },
        }
    }
}

/// Position of `b` in `v` (which must contain it).
fn find_pos(v: &Vec<usize>, b: usize) -> (i: usize)
    requires
        v@.contains(b),
    ensures
        (i as int) < v@.len(),
        v@[i as int] == b,
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v@.len(),
            v@.contains(b),
            forall|j: int| 0 <= j < i ==> v@[j] != b,
        decreases v@.len() - i,
    {
        if v[i] == b {
            return i;
        }
        i += 1;
    }
    proof {
        let j = choose|j: int| 0 <= j < v@.len() && v@[j] == b;
        assert(v@[j] != b);
    }
    0
}

/// Scans one bucket for pages whose full key equals `k`, preferring a referenced page.
fn scan_bucket(v: &Vec<usize>, keys: &Vec<Option<Digest>>, refs: &Vec<u64>, k: &Digest) -> (r: Option<(usize, bool)>)
    requires
        refs@.len() == keys@.len(),
        forall|j: int| 0 <= j < v@.len() ==> (#[trigger] v@[j] as int) < keys@.len(),
        forall|b2: usize| #[trigger] in_index(keys@, *k, b2) ==> v@.contains(b2),
    ensures
        r is None ==> forall|b: usize| !#[trigger] in_index(keys@, *k, b),
        r matches Some((b, active)) ==> {
            &&& in_index(keys@, *k, b)
            &&& active == (refs@[b as int] > 0)
            &&& !active ==> forall|b2: usize| #[trigger] in_index(keys@, *k, b2) ==> refs@[b2 as int] == 0
        },
{
    let mut found: Option<usize> = None;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            refs@.len() == keys@.len(),
            forall|j: int| 0 <= j < v@.len() ==> (#[trigger] v@[j] as int) < keys@.len(),
            0 <= i <= v@.len(),
            found matches Some(b) ==> in_index(keys@, *k, b) && refs@[b as int] == 0,
            found is None ==> forall|j: int| 0 <= j < i ==> !#[trigger] in_index(keys@, *k, v@[j]),
            forall|j: int| 0 <= j < i && #[trigger] in_index(keys@, *k, v@[j]) ==> refs@[v@[j] as int] == 0,
        decreases v@.len() - i,
    {
        let b = v[i];
        let hit = match &keys[b] {
            Some(kb) => digest_eq(kb, k),
            None => false,
        };
        if hit {
            if refs[b] > 0 {
                return Some((b, true));
            }
            if found.is_none() {
                found = Some(b);
            }
        }
        i += 1;
    }
    proof {
        assert forall|b2: usize| #[trigger] in_index(keys@, *k, b2) implies refs@[b2 as int] == 0 by {
            let j = choose|j: int| 0 <= j < v@.len() && v@[j] == b2;
            assert(in_index(keys@, *k, v@[j]));
        }
    }
    match found {
        Some(b) => Some((b, false)),
        None => {
            proof {
                assert forall|b2: usize| !#[trigger] in_index(keys@, *k, b2) by {
                    if in_index(keys@, *k, b2) {
                        let j = choose|j: int| 0 <= j < v@.len() && v@[j] == b2;
                        assert(in_index(keys@, *k, v@[j]));
                    }
                }
            }
            None
        },
    }
}

} // verus!
