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
    &&& v.cfg.mu <= max_slots()
    &&& v.cfg.delta <= 1
    &&& ns_ok(v.ns)
    &&& v.refs.len() == v.p
    &&& v.keys.len() == v.p
    &&& v.holders.len() == v.p
    &&& v.pdep.len() == v.p
    &&& v.ptoks.len() == v.p
    &&& v.own.len() == v.p
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

/// `L̂_h`: the planned input length, with the deferred position (§3.2).
pub open spec fn lhat(l: LeaseV) -> nat {
    l.toks.len() + if l.dfr { 1nat } else { 0nat }
}

/// I1, I4, I5 (lease part), I5b, I9 (lease -> Pending direction), I16, I17.
#[verifier::opaque]
pub open spec fn lease_ok(v: MgrV, log: Log, h: u64) -> bool {
    let l = v.leases[h];
    &&& h < v.next_handle
    &&& 1 <= l.toks.len()
    &&& lhat(l) <= l.rho
    &&& l.rho <= lhat(l) + v.cfg.mu
    &&& l.rho <= v.p * v.b
    &&& l.toks.len() <= v.p * v.b
    &&& blocks_for(l.rho, v.b, l.table.len())
    &&& l.table.no_duplicates()
    &&& forall|i: int| 0 <= i < l.table.len() ==> (#[trigger] l.table[i] as nat) < v.p
    &&& l.c <= l.toks.len()
    // I16: with no ticket in flight and input left, the reservation is whole.
    &&& (l.pending.len() == 0 && l.c < l.toks.len()) ==> l.rho == l.toks.len() + v.cfg.mu
    &&& forall|j: int|
        0 <= j < l.c ==> (v.vmap)(#[trigger] slot_of(v.b, l.table, j)) == l.toks.subrange(0, j + 1)
    &&& forall|i: nat| i < l.table.len() ==> #[trigger] blk_ok(v, log, l, i)
    // I9, D21: Q_h holds at most δ + 1 <= 2 tickets of this lease, in issue order, each starting
    // where the one before it ends.
    &&& l.pending.len() <= v.cfg.delta + 1
    &&& l.pending.len() <= 2
    &&& l.pending.no_duplicates()
    &&& forall|i: int| 0 <= i < l.pending.len() ==> v.pend.contains_key(#[trigger] l.pending[i]) && v.pend[l.pending[i]].lease == h
    &&& l.pending.len() == 2 ==> v.pend[l.pending[1]].a == v.pend[l.pending[0]].z
    // I17: the deferred tail is the oldest ticket, it has no drafts, and it ends at L_h.
    &&& l.dfr ==> {
        &&& v.cfg.delta == 1
        &&& l.pending.len() >= 1
        &&& v.pend[l.pending[0]].z == l.toks.len()
        &&& v.pend[l.pending[0]].drafts.len() == 0
    }
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
    // I13: only owned units are referenced or published.
    &&& v.refs[x as int] > 0 ==> v.own[x as int]
    &&& v.keys[x as int] is Some ==> v.own[x as int]
}

/// I9 (Pending -> lease direction) and the derived `c_h = a` invariant.
#[verifier::opaque]
pub open spec fn pend_ok(v: MgrV, t: u64) -> bool {
    let r = v.pend[t];
    &&& t < v.next_ticket
    &&& v.leases.contains_key(r.lease)
    &&& v.leases[r.lease].pending.contains(t)
    // The oldest ticket starts at the frontier; a later one starts past it (§3.4).
    &&& v.leases[r.lease].pending[0] == t ==> r.a == v.leases[r.lease].c
    &&& v.leases[r.lease].c <= r.a
    // A continuation's input is the deferred position (D24), so z <= L̂_h.
    &&& r.a < r.z <= lhat(v.leases[r.lease])
    // D16: drafts follow the whole planned input and fit the reservation (D18, I16).
    &&& r.drafts.len() > 0 ==> r.z == lhat(v.leases[r.lease])
    &&& r.z + r.drafts.len() <= v.leases[r.lease].rho
    &&& r.z < lhat(v.leases[r.lease]) ==> v.leases[r.lease].rho == lhat(v.leases[r.lease]) + v.cfg.mu
}

/// `Valid(S)`.
pub open spec fn inv(v: MgrV, log: Log) -> bool {
    &&& cfg_ok(v, log)
    &&& forall|h: u64| #[trigger] v.leases.contains_key(h) ==> lease_ok(v, log, h)
    &&& forall|x: PageId| (x as nat) < v.p ==> #[trigger] page_ok(v, log, x)
    &&& forall|t: u64| #[trigger] v.pend.contains_key(t) ==> pend_ok(v, t)
    &&& last_ok(v)
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
        forall|i: int|
            0 <= i < v.leases[h].pending.len() ==> v2.pend.contains_key(#[trigger] v.leases[h].pending[i]) && v2.pend[v.leases[h].pending[i]].lease
                == h,
        v.leases[h].pending.len() == 2 ==> v2.pend[v.leases[h].pending[1]].a == v.pend[v.leases[h].pending[1]].a
            && v2.pend[v.leases[h].pending[0]].z == v.pend[v.leases[h].pending[0]].z,
        v.leases[h].dfr ==> v2.pend[v.leases[h].pending[0]].z == v.pend[v.leases[h].pending[0]].z
            && v2.pend[v.leases[h].pending[0]].drafts.len() == v.pend[v.leases[h].pending[0]].drafts.len(),
        v2.cfg == v.cfg,
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
        v2.cfg == v.cfg,
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
        lemma_lease_frame(v, v, log, log2, h);
    }
    assert forall|x: PageId| (x as nat) < v.p implies #[trigger] page_ok(v, log2, x) by {
        assert(page_ok(v, log, x));
        if v.keys[x as int] is Some {
            lemma_pub_frame(v, v, log, log2, x);
        }
    }
    lemma_last_frame(v, v);
}


/// The last page of a lease.
pub open spec fn last_page(v: MgrV, h: u64) -> PageId {
    v.leases[h].table[v.leases[h].table.len() - 1]
}

/// I11a: distinct live leases have distinct last pages. (A lease's last page is always taken fresh, by
/// `attach` because `k* <= m-1`, or by `extend`; tables never change afterwards.) This makes
/// `h -> last_page(h)` injective, which bounds the number of leases by `P`.
#[verifier::opaque]
pub open spec fn last_ok(v: MgrV) -> bool {
    forall|h1: u64, h2: u64|
        v.leases.contains_key(h1) && v.leases.contains_key(h2) && h1 != h2 ==> #[trigger] last_page(v, h1)
            != #[trigger] last_page(v, h2)
}

/// `last_ok` is preserved when leases are only removed or keep their tables.
pub proof fn lemma_last_frame(v: MgrV, v2: MgrV)
    requires
        last_ok(v),
        forall|h: u64| #[trigger] v2.leases.contains_key(h) ==> v.leases.contains_key(h) && v2.leases[h].table
            == v.leases[h].table,
    ensures
        last_ok(v2),
{
    reveal(last_ok);
    assert forall|h1: u64, h2: u64|
        v2.leases.contains_key(h1) && v2.leases.contains_key(h2) && h1 != h2 implies #[trigger] last_page(v2, h1)
        != #[trigger] last_page(v2, h2) by {
        assert(last_page(v2, h1) == last_page(v, h1));
        assert(last_page(v2, h2) == last_page(v, h2));
    }
}

/// `last_ok` is preserved when lease `h` gets a table whose last page was free (or is unchanged),
/// and every other lease keeps its table.
pub proof fn lemma_last_fresh(v: MgrV, log: Log, v2: MgrV, h: u64)
    requires
        inv(v, log),
        v2.leases.dom() == v.leases.dom().insert(h),
        forall|h1: u64| #[trigger] v2.leases.contains_key(h1) && h1 != h ==> v2.leases[h1].table == v.leases[h1].table,
        v2.leases[h].table.len() >= 1,
        (v.leases.contains_key(h) && last_page(v2, h) == last_page(v, h)) || ((last_page(v2, h) as nat) < v.p
            && v.refs[last_page(v2, h) as int] == 0),
    ensures
        last_ok(v2),
{
    reveal(last_ok);
    reveal(lease_ok);
    reveal(page_ok);
    let x = last_page(v2, h);
    assert forall|h1: u64, h2: u64|
        v2.leases.contains_key(h1) && v2.leases.contains_key(h2) && h1 != h2 implies #[trigger] last_page(v2, h1)
        != #[trigger] last_page(v2, h2) by {
        if h1 != h && h2 != h {
            assert(last_page(v2, h1) == last_page(v, h1));
            assert(last_page(v2, h2) == last_page(v, h2));
        } else {
            let o = if h1 == h { h2 } else { h1 };
            assert(v.leases.contains_key(o));
            assert(lease_ok(v, log, o));
            let y = last_page(v, o);
            assert(last_page(v2, o) == y);
            if v.leases.contains_key(h) && last_page(v2, h) == last_page(v, h) {
                assert(last_page(v, h) != last_page(v, o));
            } else if x == y {
                // y is on o's table, so o holds it and refs[y] > 0.
                assert(v.leases[o].table.contains(y));
                assert(page_ok(v, log, y));
                assert(v.holders[y as int].contains(o));
                vstd::set::lemma_set_contains_len(v.holders[y as int], o);
            }
        }
    }
}

/// I11 (contract §4, bounded metadata): at most `P` leases, at most `δ + 1` pending tickets per
/// lease, each lease's table at most `P` entries and input at most `P*B` tokens.
pub proof fn lemma_counts_bounded(v: MgrV, log: Log)
    requires
        inv(v, log),
    ensures
        v.leases.dom().len() <= v.p,
        v.pend.dom().len() <= (v.cfg.delta + 1) * v.leases.dom().len(),
        forall|h: u64| #[trigger] v.leases.contains_key(h) ==> v.leases[h].table.len() <= v.p && v.leases[h].toks.len()
            <= v.p * v.b,
{
    reveal(lease_ok);
    reveal(pend_ok);
    reveal(last_ok);
    assert(v.p <= v.p * v.b) by (nonlinear_arith) requires v.b >= 1;
    let pu = v.p as usize;
    assert(pu as nat == v.p);
    vstd::set_lib::range_set_properties::<usize>(0usize, pu);
    let pages = Set::<usize>::range(0usize, pu);
    assert(pages.len() == v.p);
    assert forall|x: usize| (x as nat) < v.p implies #[trigger] pages.contains(x) by {}
    // Leases inject into pages via their last page.
    let dom = v.leases.dom();
    let f = |h: u64| last_page(v, h);
    let img = dom.map(f);
    assert(dom.injective_on(f)) by {
        assert forall|h1: u64, h2: u64| dom.contains(h1) && dom.contains(h2) && #[trigger] f(h1) == #[trigger] f(h2) implies h1
            == h2 by {
            if h1 != h2 {
                assert(last_page(v, h1) != last_page(v, h2));
            }
        }
    }
    vstd::set_lib::lemma_map_size(dom, img, f);
    assert forall|x: usize| #[trigger] img.contains(x) implies pages.contains(x) by {
        dom.lemma_map_contains(f, x);
        let h = choose|h: u64| dom.contains(h) && x == f(h);
        assert(lease_ok(v, log, h));
        let t = v.leases[h].table;
        assert(t.len() >= 1) by {
            assert(blocks_for(v.leases[h].rho, v.b, t.len()));
        }
        assert((t[t.len() - 1] as nat) < v.p);
    }
    vstd::set_lib::lemma_len_subset(img, pages);
    // Pending tickets: the oldest of each queue, and the second of each queue, each inject into
    // the leases (I9: at most two per lease, at most one with δ = 0).
    let pd = v.pend.dom();
    let g = |t: u64| v.pend[t].lease;
    let heads = pd.filter(|t: u64| v.leases[v.pend[t].lease].pending[0] == t);
    let seconds = pd.filter(|t: u64| v.leases[v.pend[t].lease].pending[0] != t);
    assert(pd =~= heads.union(seconds));
    assert(heads.injective_on(g)) by {
        assert forall|t1: u64, t2: u64| heads.contains(t1) && heads.contains(t2) && #[trigger] g(t1) == #[trigger] g(t2) implies t1
            == t2 by {}
    }
    assert(seconds.injective_on(g)) by {
        assert forall|t1: u64, t2: u64| seconds.contains(t1) && seconds.contains(t2) && #[trigger] g(t1) == #[trigger] g(t2) implies t1
            == t2 by {
            assert(pend_ok(v, t1));
            assert(pend_ok(v, t2));
            let h = g(t1);
            assert(lease_ok(v, log, h));
            let q = v.leases[h].pending;
            let i1 = choose|i: int| 0 <= i < q.len() && q[i] == t1;
            let i2 = choose|i: int| 0 <= i < q.len() && q[i] == t2;
            assert(i1 == 1 && i2 == 1);
        }
    }
    let hi = heads.map(g);
    let si = seconds.map(g);
    vstd::set_lib::lemma_map_size(heads, hi, g);
    vstd::set_lib::lemma_map_size(seconds, si, g);
    assert forall|h: u64| #[trigger] hi.contains(h) implies dom.contains(h) by {
        heads.lemma_map_contains(g, h);
        let t = choose|t: u64| heads.contains(t) && h == g(t);
        assert(pend_ok(v, t));
    }
    assert forall|h: u64| #[trigger] si.contains(h) implies dom.contains(h) by {
        seconds.lemma_map_contains(g, h);
        let t = choose|t: u64| seconds.contains(t) && h == g(t);
        assert(pend_ok(v, t));
    }
    vstd::set_lib::lemma_len_subset(hi, dom);
    vstd::set_lib::lemma_len_subset(si, dom);
    vstd::set_lib::lemma_len_union(heads, seconds);
    if v.cfg.delta == 0 {
        // With δ = 0 every queue holds one ticket, so every pending ticket is the oldest.
        assert(seconds =~= Set::<u64>::empty()) by {
            assert forall|t: u64| !seconds.contains(t) by {
                if seconds.contains(t) {
                    assert(pend_ok(v, t));
                    assert(lease_ok(v, log, v.pend[t].lease));
                    let q = v.leases[v.pend[t].lease].pending;
                    let i = choose|i: int| 0 <= i < q.len() && q[i] == t;
                }
            }
        }
    }
    assert(v.pend.dom().len() <= (v.cfg.delta + 1) * v.leases.dom().len()) by (nonlinear_arith)
        requires
            v.pend.dom().len() <= heads.len() + seconds.len(),
            heads.len() <= v.leases.dom().len(),
            seconds.len() <= v.leases.dom().len(),
            v.cfg.delta == 0 ==> seconds.len() == 0,
            v.cfg.delta <= 1,
    ;
    // Tables: no duplicates, all entries < P.
    assert forall|h: u64| #[trigger] v.leases.contains_key(h) implies v.leases[h].table.len() <= v.p
        && v.leases[h].toks.len() <= v.p * v.b by {
        assert(lease_ok(v, log, h));
        let t = v.leases[h].table;
        t.unique_seq_to_set();
        assert forall|x: usize| #[trigger] t.to_set().contains(x) implies pages.contains(x) by {
            t.to_set_ensures();
            let i = choose|i: int| 0 <= i < t.len() && t[i] == x;
            assert((t[i] as nat) < v.p);
        }
        vstd::set_lib::lemma_len_subset(t.to_set(), pages);
    }
}

} // verus!
