//! Abstract invariant `Valid(S)` (contract §4) over `MgrV`, plus frame lemmas.
//!
//! The invariant is split into opaque per-lease / per-page / per-ticket predicates so that each
//! transition proof only unfolds what it touches. No trusted content.
use vstd::prelude::*;
use crate::spec::*;
use crate::types::*;
use crate::arith::*;
#[cfg(verus_keep_ghost)]
use crate::index::in_index;

verus! {

pub type Log = Map<Digest, Seq<u8>>;

/// I1 (configuration part), I10, and the seed of the key chain.
pub open spec fn cfg_ok(v: MgrV, log: Log) -> bool {
    &&& v.p >= 1
    &&& v.b >= 1
    &&& v.p * v.b <= max_slots()
    &&& ns_ok(v.ns)
    &&& v.refs.len() == v.p
    &&& v.keys.len() == v.p
    &&& v.holders.len() == v.p
    &&& v.pdep.len() == v.p
    &&& v.ptoks.len() == v.p
    &&& log.contains_key(seed_of(v.ns))
    &&& log[seed_of(v.ns)] == seed_input(v.ns)
}

/// Block `i` of lease `l`: published iff complete and computed (I5 second part + I5b), and then
/// its key is `K(h,i)`, logged on the E8 chain.
pub open spec fn blk_ok(v: MgrV, log: Log, l: LeaseV, i: nat) -> bool {
    &&& (v.keys[l.table[i as int] as int] is Some) == ((i + 1) * v.b <= l.c)
    &&& (i + 1) * v.b <= l.c ==> {
        &&& v.keys[l.table[i as int] as int] == Some(v.key_of(l.toks, i))
        &&& chain_logged(log, v.ns, l.toks, v.b, i)
    }
}

/// I1, I4, I5 (lease part), I5b, I9 (lease -> Pending direction).
#[verifier::opaque]
pub open spec fn lease_ok(v: MgrV, log: Log, h: u64) -> bool {
    let l = v.leases[h];
    &&& h < v.next_handle
    &&& 1 <= l.toks.len() <= v.p * v.b
    &&& blocks_for(l.toks.len(), v.b, l.table.len())
    &&& l.table.no_duplicates()
    &&& forall|i: int| 0 <= i < l.table.len() ==> (#[trigger] l.table[i] as nat) < v.p
    &&& l.c <= l.toks.len()
    &&& forall|j: int|
        0 <= j < l.c ==> (v.vmap)(#[trigger] slot_of(v.b, l.table, j)) == l.toks.subrange(0, j + 1)
    &&& forall|i: nat| i < l.table.len() ==> #[trigger] blk_ok(v, log, l, i)
    &&& l.pending matches Some(t) ==> v.pend.contains_key(t) && v.pend[t].lease == h
}

/// I2 (exact reference count) via the ghost holder set.
pub open spec fn hold_ok(v: MgrV, x: PageId) -> bool {
    &&& forall|h: u64|
        #[trigger] v.holders[x as int].contains(h) <==> (v.leases.contains_key(h) && v.leases[h].table.contains(x))
    &&& v.refs[x as int] as nat == v.holders[x as int].len()
}

/// I5 (published-page part): a published page carries the last full block of the prefix its key
/// denotes, with valid KV for every slot.
#[verifier::opaque]
pub open spec fn pub_ok(v: MgrV, log: Log, x: PageId) -> bool {
    let q = v.pdep[x as int];
    let tau = v.ptoks[x as int];
    &&& tau.len() == (q + 1) * v.b
    &&& chain_logged(log, v.ns, tau, v.b, q)
    &&& v.keys[x as int] == Some(v.key_of(tau, q))
    &&& forall|off: int|
        0 <= off < v.b ==> (v.vmap)(#[trigger] sl(v.b, x as int, off)) == tau.subrange(0, q * v.b + off + 1)
}

/// I2, I6, I5 for one page; plus the reference-count overflow bound.
#[verifier::opaque]
pub open spec fn page_ok(v: MgrV, log: Log, x: PageId) -> bool {
    &&& hold_ok(v, x)
    &&& v.refs[x as int] <= v.next_handle
    &&& v.refs[x as int] > 1 ==> v.keys[x as int] is Some
    &&& v.keys[x as int] is Some ==> pub_ok(v, log, x)
}

/// I9 (Pending -> lease direction) and the derived `c_h = a` invariant.
#[verifier::opaque]
pub open spec fn pend_ok(v: MgrV, t: u64) -> bool {
    let r = v.pend[t];
    &&& t < v.next_ticket
    &&& v.leases.contains_key(r.lease)
    &&& v.leases[r.lease].pending == Some(t)
    &&& r.a == v.leases[r.lease].c
    &&& r.a < r.z <= v.leases[r.lease].toks.len()
}

/// `Valid(S)`.
pub open spec fn inv(v: MgrV, log: Log) -> bool {
    &&& cfg_ok(v, log)
    &&& forall|h: u64| #[trigger] v.leases.contains_key(h) ==> lease_ok(v, log, h)
    &&& forall|x: PageId| (x as nat) < v.p ==> #[trigger] page_ok(v, log, x)
    &&& forall|t: u64| #[trigger] v.pend.contains_key(t) ==> pend_ok(v, t)
}

// ---------------------------------------------------------------------------------------------
// Frame lemmas
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_logged_mono_all(log: Log, log2: Log, ns: Seq<u8>, toks: Seq<Token>, bsz: nat, i: nat)
    requires
        log.submap_of(log2),
        chain_logged(log, ns, toks, bsz, i),
    ensures
        chain_logged(log2, ns, toks, bsz, i),
{
    lemma_chain_logged_mono(log, log2, ns, toks, bsz, i);
}

pub proof fn lemma_lease_frame(v: MgrV, v2: MgrV, log: Log, log2: Log, h: u64)
    requires
        lease_ok(v, log, h),
        v.same_config(v2),
        v2.leases[h] == v.leases[h],
        v.next_handle <= v2.next_handle,
        log.submap_of(log2),
        forall|i: int|
            0 <= i < v.leases[h].table.len() ==> v2.keys[#[trigger] v.leases[h].table[i] as int]
                == v.keys[v.leases[h].table[i] as int],
        forall|j: int|
            0 <= j < v.leases[h].c ==> (v2.vmap)(#[trigger] slot_of(v.b, v.leases[h].table, j)) == (v.vmap)(
                slot_of(v.b, v.leases[h].table, j),
            ),
        v.leases[h].pending matches Some(t) ==> v2.pend.contains_key(t) && v2.pend[t].lease == h,
    ensures
        lease_ok(v2, log2, h),
{
    reveal(lease_ok);
    let l = v.leases[h];
    assert forall|i: nat| i < l.table.len() implies #[trigger] blk_ok(v2, log2, l, i) by {
        assert(blk_ok(v, log, l, i));
        assert(v2.keys[l.table[i as int] as int] == v.keys[l.table[i as int] as int]);
        if (i + 1) * v.b <= l.c {
            lemma_chain_logged_mono(log, log2, v.ns, l.toks, v.b, i);
        }
    }
    assert forall|j: int| 0 <= j < l.c implies (v2.vmap)(#[trigger] slot_of(v2.b, l.table, j)) == l.toks.subrange(
        0,
        j + 1,
    ) by {
        assert((v.vmap)(slot_of(v.b, l.table, j)) == l.toks.subrange(0, j + 1));
    }
}

pub proof fn lemma_pub_frame(v: MgrV, v2: MgrV, log: Log, log2: Log, x: PageId)
    requires
        pub_ok(v, log, x),
        v.same_config(v2),
        log.submap_of(log2),
        v2.keys[x as int] == v.keys[x as int],
        v2.pdep[x as int] == v.pdep[x as int],
        v2.ptoks[x as int] == v.ptoks[x as int],
        forall|off: int| 0 <= off < v.b ==> (v2.vmap)(#[trigger] sl(v.b, x as int, off)) == (v.vmap)(sl(v.b, x as int, off)),
    ensures
        pub_ok(v2, log2, x),
{
    reveal(pub_ok);
    lemma_chain_logged_mono(log, log2, v.ns, v.ptoks[x as int], v.b, v.pdep[x as int]);
    assert forall|off: int| 0 <= off < v2.b implies (v2.vmap)(#[trigger] sl(v2.b, x as int, off))
        == v2.ptoks[x as int].subrange(0, v2.pdep[x as int] * v2.b + off + 1) by {
        assert((v.vmap)(sl(v.b, x as int, off)) == v.ptoks[x as int].subrange(0, v.pdep[x as int] * v.b + off + 1));
    }
}

pub proof fn lemma_pend_frame(v: MgrV, v2: MgrV, t: u64)
    requires
        pend_ok(v, t),
        v2.pend[t] == v.pend[t],
        v.next_ticket <= v2.next_ticket,
        v2.leases.contains_key(v.pend[t].lease),
        v2.leases[v.pend[t].lease] == v.leases[v.pend[t].lease],
    ensures
        pend_ok(v2, t),
{
    reveal(pend_ok);
}

// ---------------------------------------------------------------------------------------------
// Derived facts
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_set_len1(s: Set<u64>, h: u64)
    requires
        s.contains(h),
        s.len() <= 1,
    ensures
        s == Set::<u64>::empty().insert(h),
{
    assert(s.remove(h).len() == 0) by {
        vstd::set::lemma_set_remove_len(s, h);
    }
    assert forall|y: u64| s.contains(y) implies y == h by {
        if y != h {
            assert(s.remove(h).contains(y));
            vstd::set_lib::lemma_set_empty_equivalency_len(s.remove(h));
        }
    }
    assert(s =~= Set::<u64>::empty().insert(h));
}

/// A block of lease `h` that is not yet computed lies on an exclusive, unpublished page.
pub proof fn lemma_uncomputed_exclusive(v: MgrV, log: Log, h: u64, i: nat)
    requires
        inv(v, log),
        v.leases.contains_key(h),
        i < v.leases[h].table.len(),
        (i + 1) * v.b > v.leases[h].c,
    ensures
        v.keys[v.leases[h].table[i as int] as int] is None,
        v.refs[v.leases[h].table[i as int] as int] == 1,
        v.holders[v.leases[h].table[i as int] as int] == Set::<u64>::empty().insert(h),
        forall|h2: u64|
            v.leases.contains_key(h2) && h2 != h ==> !(#[trigger] v.leases[h2].table).contains(v.leases[h].table[i as int]),
{
    reveal(lease_ok);
    reveal(page_ok);
    let l = v.leases[h];
    let x = l.table[i as int];
    assert(lease_ok(v, log, h));
    assert(blk_ok(v, log, l, i));
    assert((x as nat) < v.p);
    assert(page_ok(v, log, x));
    assert(l.table.contains(x));
    assert(v.holders[x as int].contains(h));
    lemma_set_len1(v.holders[x as int], h);
    vstd::set::lemma_set_insert_len(Set::<u64>::empty(), h);
    assert forall|h2: u64| v.leases.contains_key(h2) && h2 != h implies !(#[trigger] v.leases[h2].table).contains(x) by {
        if v.leases[h2].table.contains(x) {
            assert(v.holders[x as int].contains(h2));
        }
    }
}

/// Positions of a lease's table map to distinct slots in `[0, P*B)`.
pub proof fn lemma_slot_of_props(b: nat, p: nat, table: Seq<PageId>, j: int)
    requires
        b > 0,
        0 <= j,
        j / (b as int) < table.len(),
        forall|i: int| 0 <= i < table.len() ==> (#[trigger] table[i] as nat) < p,
    ensures
        0 <= slot_of(b, table, j) < p * b,
        slot_of(b, table, j) == sl(b, table[j / (b as int)] as int, j % (b as int)),
        0 <= j % (b as int) < b,
{
    lemma_div_bounds(j as nat, b);
    let i = j / (b as int);
    assert((table[i] as nat) < p);
    lemma_slot_bound(table[i] as nat, (j % (b as int)) as nat, b, p);
}

pub proof fn lemma_slot_of_inj(b: nat, table: Seq<PageId>, j1: int, j2: int)
    requires
        b > 0,
        0 <= j1,
        0 <= j2,
        j1 / (b as int) < table.len(),
        j2 / (b as int) < table.len(),
        table.no_duplicates(),
        slot_of(b, table, j1) == slot_of(b, table, j2),
    ensures
        j1 == j2,
{
    lemma_div_bounds(j1 as nat, b);
    lemma_div_bounds(j2 as nat, b);
    let i1 = j1 / (b as int);
    let i2 = j2 / (b as int);
    lemma_slot_inj(table[i1] as nat, (j1 % (b as int)) as nat, table[i2] as nat, (j2 % (b as int)) as nat, b);
    assert(i1 == i2);
}

/// A slot `sl(b, x, off)` that equals a table slot identifies the table page.
pub proof fn lemma_sl_page(b: nat, table: Seq<PageId>, j: int, x: int, off: int)
    requires
        b > 0,
        0 <= j,
        j / (b as int) < table.len(),
        0 <= off < b,
        x >= 0,
        sl(b, x, off) == slot_of(b, table, j),
    ensures
        table[j / (b as int)] as int == x,
        j % (b as int) == off,
{
    lemma_div_bounds(j as nat, b);
    lemma_slot_inj(x as nat, off as nat, table[j / (b as int)] as nat, (j % (b as int)) as nat, b);
}

/// Position `i*b + off` of a table is the slot `sl(b, table[i], off)`.
pub proof fn lemma_slot_of_block(b: nat, table: Seq<PageId>, i: int, off: int)
    requires
        b > 0,
        0 <= i,
        0 <= off < b,
    ensures
        (i * b + off) / (b as int) == i,
        (i * b + off) % (b as int) == off,
        slot_of(b, table, i * b + off) == sl(b, table[i] as int, off),
{
    lemma_slot_decomp(i as nat, off as nat, b);
}


/// Inserting a consistent entry extends the log.
pub proof fn lemma_insert_submap(log: Log, d: Digest, x: Seq<u8>)
    requires
        log.contains_key(d) ==> log[d] == x,
    ensures
        log.submap_of(log.insert(d, x)),
{
    assert forall|k: Digest| #[trigger] log.contains_key(k) implies log.insert(d, x).contains_key(k) && log.insert(
        d,
        x,
    )[k] == log[k] by {
        if k == d {
        }
    }
}

/// `Valid` is monotone in the E8 log.
pub proof fn lemma_inv_log_mono(v: MgrV, log: Log, log2: Log)
    requires
        inv(v, log),
        log.submap_of(log2),
    ensures
        inv(v, log2),
{
    reveal(page_ok);
    assert(log2.contains_key(seed_of(v.ns)) && log2[seed_of(v.ns)] == log[seed_of(v.ns)]);
    assert forall|h: u64| #[trigger] v.leases.contains_key(h) implies lease_ok(v, log2, h) by {
        assert(lease_ok(v, log, h));
        reveal(lease_ok);
        if v.leases[h].pending is Some {
        }
        lemma_lease_frame(v, v, log, log2, h);
    }
    assert forall|x: PageId| (x as nat) < v.p implies #[trigger] page_ok(v, log2, x) by {
        assert(page_ok(v, log, x));
        if v.keys[x as int] is Some {
            lemma_pub_frame(v, v, log, log2, x);
        }
    }
}

} // verus!
