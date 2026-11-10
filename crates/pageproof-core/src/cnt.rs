//! Counting helpers for the slab plan (§3.5): `cnt(n, f)` is `|{s < n | f(s)}|`, and `ssum` sums a
//! prefix of a sequence. All proved; no trusted content.
use vstd::prelude::*;

verus! {

/// `|{ s in [0, n) | f(s) }|`.
pub open spec fn cnt(n: int, f: spec_fn(int) -> bool) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        cnt(n - 1, f) + if f(n - 1) {
            1nat
        } else {
            0nat
        }
    }
}

pub proof fn lemma_cnt_ext(n: int, f: spec_fn(int) -> bool, g: spec_fn(int) -> bool)
    requires
        forall|i: int| 0 <= i < n ==> #[trigger] f(i) == g(i),
    ensures
        cnt(n, f) == cnt(n, g),
    decreases n,
{
    if n > 0 {
        lemma_cnt_ext(n - 1, f, g);
    }
}

/// Changing `f` at one point changes the count by the difference at that point.
pub proof fn lemma_cnt_point(n: int, f: spec_fn(int) -> bool, g: spec_fn(int) -> bool, s: int)
    requires
        0 <= s < n,
        forall|i: int| 0 <= i < n && i != s ==> #[trigger] f(i) == g(i),
    ensures
        cnt(n, g) + (if f(s) {
            1nat
        } else {
            0nat
        }) == cnt(n, f) + (if g(s) {
            1nat
        } else {
            0nat
        }),
    decreases n,
{
    if s < n - 1 {
        lemma_cnt_point(n - 1, f, g, s);
    } else {
        lemma_cnt_ext(n - 1, f, g);
    }
}

pub proof fn lemma_cnt_pos(n: int, f: spec_fn(int) -> bool)
    requires
        cnt(n, f) > 0,
    ensures
        exists|s: int| 0 <= s < n && #[trigger] f(s),
    decreases n,
{
    if n > 0 && !f(n - 1) {
        lemma_cnt_pos(n - 1, f);
    }
}

pub proof fn lemma_cnt_zero(n: int, f: spec_fn(int) -> bool)
    requires
        forall|i: int| 0 <= i < n ==> !#[trigger] f(i),
    ensures
        cnt(n, f) == 0,
    decreases n,
{
    if n > 0 {
        lemma_cnt_zero(n - 1, f);
    }
}

pub proof fn lemma_cnt_le(n: int, f: spec_fn(int) -> bool)
    requires
        n >= 0,
    ensures
        cnt(n, f) <= n,
    decreases n,
{
    if n > 0 {
        lemma_cnt_le(n - 1, f);
    }
}

/// `Σ_{i<k} s[i]`.
pub open spec fn ssum(s: Seq<usize>, k: int) -> nat
    decreases k,
{
    if k <= 0 {
        0
    } else {
        ssum(s, k - 1) + s[k - 1] as nat
    }
}

pub proof fn lemma_ssum_update(s: Seq<usize>, k: int, i: int, x: usize)
    requires
        0 <= i < k <= s.len(),
    ensures
        ssum(s.update(i, x), k) + s[i] as nat == ssum(s, k) + x as nat,
    decreases k,
{
    if i < k - 1 {
        lemma_ssum_update(s, k - 1, i, x);
    } else {
        lemma_ssum_ext(s, s.update(i, x), k - 1);
    }
}

pub proof fn lemma_ssum_ext(s: Seq<usize>, t: Seq<usize>, k: int)
    requires
        forall|i: int| 0 <= i < k ==> #[trigger] s[i] == t[i],
    ensures
        ssum(s, k) == ssum(t, k),
    decreases k,
{
    if k > 0 {
        lemma_ssum_ext(s, t, k - 1);
    }
}

pub proof fn lemma_ssum_pos(s: Seq<usize>, k: int)
    requires
        ssum(s, k) > 0,
    ensures
        exists|i: int| 0 <= i < k && #[trigger] s[i] > 0,
    decreases k,
{
    if k > 0 && s[k - 1] == 0 {
        lemma_ssum_pos(s, k - 1);
    }
}

pub proof fn lemma_ssum_bound(s: Seq<usize>, k: int, bnd: nat)
    requires
        k >= 0,
        forall|i: int| 0 <= i < k ==> #[trigger] s[i] as nat <= bnd,
    ensures
        ssum(s, k) <= k * bnd,
    decreases k,
{
    if k > 0 {
        lemma_ssum_bound(s, k - 1, bnd);
        assert((k - 1) * bnd + bnd == k * bnd) by (nonlinear_arith);
    }
}

pub proof fn lemma_ssum_mono(s: Seq<usize>, t: Seq<usize>, k: int)
    requires
        forall|i: int| 0 <= i < k ==> #[trigger] s[i] >= t[i],
    ensures
        ssum(s, k) >= ssum(t, k),
    decreases k,
{
    if k > 0 {
        lemma_ssum_mono(s, t, k - 1);
    }
}

pub proof fn lemma_ssum_prefix_le(s: Seq<usize>, k1: int, k2: int)
    requires
        0 <= k1 <= k2,
    ensures
        ssum(s, k1) <= ssum(s, k2),
    decreases k2 - k1,
{
    if k1 < k2 {
        lemma_ssum_prefix_le(s, k1, k2 - 1);
    }
}

/// `cnt` is monotone under pointwise implication.
pub proof fn lemma_cnt_imp(n: int, f: spec_fn(int) -> bool, g: spec_fn(int) -> bool)
    requires
        forall|i: int| 0 <= i < n && #[trigger] f(i) ==> g(i),
    ensures
        cnt(n, f) <= cnt(n, g),
    decreases n,
{
    if n > 0 {
        lemma_cnt_imp(n - 1, f, g);
    }
}

/// `Σ_{i<k} f(i)`.
pub open spec fn nsum(k: int, f: spec_fn(int) -> nat) -> nat
    decreases k,
{
    if k <= 0 {
        0
    } else {
        nsum(k - 1, f) + f(k - 1)
    }
}

pub proof fn lemma_nsum_ext(k: int, f: spec_fn(int) -> nat, g: spec_fn(int) -> nat)
    requires
        forall|i: int| 0 <= i < k ==> #[trigger] f(i) == g(i),
    ensures
        nsum(k, f) == nsum(k, g),
    decreases k,
{
    if k > 0 {
        lemma_nsum_ext(k - 1, f, g);
    }
}

pub proof fn lemma_nsum_point(k: int, f: spec_fn(int) -> nat, g: spec_fn(int) -> nat, c: int)
    requires
        0 <= c < k,
        forall|i: int| 0 <= i < k && i != c ==> #[trigger] f(i) == g(i),
    ensures
        nsum(k, g) + f(c) == nsum(k, f) + g(c),
    decreases k,
{
    if c < k - 1 {
        lemma_nsum_point(k - 1, f, g, c);
    } else {
        lemma_nsum_ext(k - 1, f, g);
    }
}

pub proof fn lemma_nsum_ge(k: int, f: spec_fn(int) -> nat, g: spec_fn(int) -> nat)
    requires
        forall|i: int| 0 <= i < k ==> #[trigger] f(i) >= g(i),
    ensures
        nsum(k, f) >= nsum(k, g),
    decreases k,
{
    if k > 0 {
        lemma_nsum_ge(k - 1, f, g);
    }
}

pub proof fn lemma_nsum_zero(k: int, f: spec_fn(int) -> nat)
    requires
        forall|i: int| 0 <= i < k ==> #[trigger] f(i) == 0,
    ensures
        nsum(k, f) == 0,
    decreases k,
{
    if k > 0 {
        lemma_nsum_zero(k - 1, f);
    }
}

pub proof fn lemma_nsum_pos(k: int, f: spec_fn(int) -> nat)
    requires
        nsum(k, f) > 0,
    ensures
        exists|i: int| 0 <= i < k && #[trigger] f(i) > 0,
    decreases k,
{
    if k > 0 && f(k - 1) == 0 {
        lemma_nsum_pos(k - 1, f);
    }
}

pub proof fn lemma_nsum_le(k: int, f: spec_fn(int) -> nat, i: int)
    requires
        0 <= i < k,
    ensures
        f(i) <= nsum(k, f),
    decreases k,
{
    if i < k - 1 {
        lemma_nsum_le(k - 1, f, i);
    }
}

pub proof fn lemma_nsum_bound(k: int, f: spec_fn(int) -> nat, bnd: nat)
    requires
        k >= 0,
        forall|i: int| 0 <= i < k ==> #[trigger] f(i) <= bnd,
    ensures
        nsum(k, f) <= k * bnd,
    decreases k,
{
    if k > 0 {
        lemma_nsum_bound(k - 1, f, bnd);
        assert((k - 1) * bnd + bnd == k * bnd) by (nonlinear_arith);
    }
}

/// A set of `usize` described by a predicate on `[0, n)` has `cnt` elements.
pub proof fn lemma_cnt_set(n: int, f: spec_fn(int) -> bool, s: Set<usize>)
    requires
        0 <= n <= usize::MAX,
        forall|x: usize| #[trigger] s.contains(x) <==> ((x as int) < n && f(x as int)),
    ensures
        s.len() == cnt(n, f),
    decreases n,
{
    if n > 0 {
        let y = (n - 1) as usize;
        let s2 = s.remove(y);
        assert forall|x: usize| #[trigger] s2.contains(x) <==> ((x as int) < n - 1 && f(x as int)) by {}
        lemma_cnt_set(n - 1, f, s2);
        if f(n - 1) {
            assert(s.contains(y));
            vstd::set::lemma_set_remove_len(s, y);
        } else {
            assert(s2 =~= s);
        }
    } else {
        assert(s =~= Set::<usize>::empty());
    }
}

} // verus!
