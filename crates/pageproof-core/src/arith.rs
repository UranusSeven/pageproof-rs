//! Arithmetic facts for block/slot addressing (§3.3). All proved; no trusted content.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;

verus! {

/// `ceil(l / b)` for `b > 0`.
pub open spec fn cdiv(l: nat, b: nat) -> nat
    recommends b > 0,
{
    ((l + b - 1) as nat / b) as nat
}

/// Upper bound on `P*B` accepted by `create`; keeps every slot, length and position far from
/// `usize` overflow.
pub open spec fn max_slots() -> nat {
    0x100_0000_0000  // 2^40
}

pub const MAX_SLOTS: u64 = 0x100_0000_0000;

pub proof fn lemma_div_bounds(j: nat, b: nat)
    requires
        b > 0,
    ensures
        (j / b) * b <= j < (j / b + 1) * b,
        j % b < b,
        j == (j / b) * b + j % b,
{
    lemma_fundamental_div_mod(j as int, b as int);
    lemma_mod_bound(j as int, b as int);
    lemma_mul_is_commutative((j / b) as int, b as int);
    assert((j / b + 1) * b == (j / b) * b + b) by (nonlinear_arith);
}

/// `j / b == i  <==>  i*b <= j < (i+1)*b`.
pub proof fn lemma_div_unique(j: nat, b: nat, i: nat)
    requires
        b > 0,
        i * b <= j < (i + 1) * b,
    ensures
        j / b == i,
        j % b == j - i * b,
{
    lemma_div_bounds(j, b);
    let q = j / b;
    if q < i {
        assert(q + 1 <= i);
        assert((q + 1) * b <= i * b) by (nonlinear_arith) requires q + 1 <= i;
    } else if q > i {
        assert(i + 1 <= q);
        assert((i + 1) * b <= q * b) by (nonlinear_arith) requires i + 1 <= q;
    }
}

/// `(i+1)*b <= c  <==>  i < c / b`.
pub proof fn lemma_block_complete(i: nat, c: nat, b: nat)
    requires
        b > 0,
    ensures
        ((i + 1) * b <= c) <==> (i < c / b),
{
    lemma_div_bounds(c, b);
    let q = c / b;
    if (i + 1) * b <= c {
        if i >= q {
            assert((q + 1) * b <= (i + 1) * b) by (nonlinear_arith) requires q <= i;
        }
    }
    if i < q {
        assert((i + 1) * b <= q * b) by (nonlinear_arith) requires i + 1 <= q;
    }
}

/// `j < l  ==>  j / b < cdiv(l, b)`, and the number of blocks covers the length exactly.
pub proof fn lemma_cdiv_props(l: nat, b: nat)
    requires
        b > 0,
    ensures
        cdiv(l, b) * b >= l,
        l > 0 ==> (cdiv(l, b) - 1) * b < l,
        forall|j: nat| j < l ==> #[trigger] (j / b) < cdiv(l, b),
        l > 0 ==> cdiv(l, b) >= 1,
{
    let x = (l + b - 1) as nat;
    lemma_div_bounds(x, b);
    let q = cdiv(l, b);
    assert(q * b <= x < (q + 1) * b);
    assert((q + 1) * b == q * b + b) by (nonlinear_arith);
    assert(q * b >= l);
    if l > 0 {
        assert(q >= 1) by {
            if q == 0 {
                assert(q * b == 0);
            }
        }
        assert((q - 1) * b == q * b - b) by (nonlinear_arith) requires q >= 1;
    }
    assert forall|j: nat| j < l implies #[trigger] (j / b) < cdiv(l, b) by {
        lemma_div_bounds(j, b);
        if j / b >= q {
            assert(q * b <= (j / b) * b) by (nonlinear_arith) requires q <= j / b;
        }
    }
}

/// Monotonicity of `cdiv`, and its bound by the page count.
pub proof fn lemma_cdiv_mono(l1: nat, l2: nat, b: nat)
    requires
        b > 0,
        l1 <= l2,
    ensures
        cdiv(l1, b) <= cdiv(l2, b),
{
    lemma_div_is_ordered((l1 + b - 1) as int, (l2 + b - 1) as int, b as int);
}

pub proof fn lemma_cdiv_le(l: nat, b: nat, p: nat)
    requires
        b > 0,
        l <= p * b,
    ensures
        cdiv(l, b) <= p,
{
    lemma_cdiv_mono(l, p * b, b);
    let x = (p * b + b - 1) as nat;
    lemma_div_bounds(x, b);
    let q = x / b;
    if q > p {
        assert((p + 1) * b <= q * b) by (nonlinear_arith) requires p + 1 <= q;
        assert((p + 1) * b == p * b + b) by (nonlinear_arith);
    }
}

/// Slot addresses lie in `[0, P*B)`.
pub proof fn lemma_slot_bound(pg: nat, off: nat, b: nat, p: nat)
    requires
        pg < p,
        off < b,
    ensures
        pg * b + off < p * b,
        pg * b + off >= 0,
{
    assert(pg * b + b <= p * b) by (nonlinear_arith) requires pg + 1 <= p;
}

/// Slots of different (page, offset) pairs differ.
pub proof fn lemma_slot_inj(pg1: nat, off1: nat, pg2: nat, off2: nat, b: nat)
    requires
        off1 < b,
        off2 < b,
        pg1 * b + off1 == pg2 * b + off2,
    ensures
        pg1 == pg2,
        off1 == off2,
{
    if pg1 < pg2 {
        assert(pg1 * b + b <= pg2 * b) by (nonlinear_arith) requires pg1 + 1 <= pg2;
    } else if pg2 < pg1 {
        assert(pg2 * b + b <= pg1 * b) by (nonlinear_arith) requires pg2 + 1 <= pg1;
    }
}

/// Slot `pg*b + off` decomposes back into its page and offset.
pub proof fn lemma_slot_decomp(pg: nat, off: nat, b: nat)
    requires
        b > 0,
        off < b,
    ensures
        (pg * b + off) / b == pg,
        (pg * b + off) % b == off,
{
    let s = pg * b + off;
    assert(pg * b <= s < (pg + 1) * b) by (nonlinear_arith) requires off < b, s == pg * b + off;
    lemma_div_unique(s, b, pg);
}

pub proof fn lemma_mul_mono(a: nat, a2: nat, b: nat)
    requires
        a <= a2,
    ensures
        a * b <= a2 * b,
{
    assert(a * b <= a2 * b) by (nonlinear_arith) requires a <= a2;
}

pub proof fn lemma_mul_succ(a: nat, b: nat)
    ensures
        (a + 1) * b == a * b + b,
{
    assert((a + 1) * b == a * b + b) by (nonlinear_arith);
}

pub proof fn lemma_div_is_ordered_nat(x: nat, y: nat, b: nat)
    requires
        b > 0,
        x <= y,
    ensures
        x / b <= y / b,
{
    lemma_div_is_ordered(x as int, y as int, b as int);
}

} // verus!
