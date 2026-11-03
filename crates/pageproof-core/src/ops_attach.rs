//! C1 `attach`: chained-key prefix lookup, k*/u/d capacity rule, active-candidate preference.
use vstd::prelude::*;
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::arith::*;
use crate::manager::*;
use crate::e8::*;
use crate::idxset::IdxSet;
use crate::index::KeyIndex;
#[cfg(verus_keep_ghost)]
use crate::index::in_index;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

// ---------------------------------------------------------------------------------------------
// Specification of C1
// ---------------------------------------------------------------------------------------------

/// `keys` with every page in `fresh` revoked (key and Index entry removed).
pub open spec fn revoke(keys: Seq<Option<Digest>>, fresh: Seq<PageId>) -> Seq<Option<Digest>> {
    Seq::new(keys.len(), |x: int| if fresh.contains(x as PageId) { None } else { keys[x] })
}

/// Legal page-table choice for `attach` (C1 success postconditions on the table).
pub open spec fn attach_choice(v: MgrV, toks: Seq<Token>, table: Seq<PageId>, kstar: nat) -> bool {
    &&& 1 <= toks.len() <= v.p * v.b
    &&& blocks_for(toks.len(), v.b, table.len())
    &&& is_kstar(v, toks, table.len(), kstar)
    &&& table.no_duplicates()
    &&& forall|i: int| 0 <= i < table.len() ==> (#[trigger] table[i] as nat) < v.p
    // i < k*: chosen from the call-time Index; an active candidate is used whenever one exists.
    &&& forall|i: int|
        #![trigger table[i]]
        0 <= i < kstar ==> in_index(v.keys, v.key_of(toks, i as nat), table[i]) && (v.has_active_hit(
            v.key_of(toks, i as nat),
        ) ==> v.refs[table[i] as int] > 0)
    // i >= k*: fresh pages taken from F (distinct from the hit pages by no_duplicates).
    &&& forall|i: int| #![trigger table[i]] kstar <= i < table.len() ==> v.refs[table[i] as int] == 0
    &&& v.next_handle < u64::MAX
}

/// Abstract state after a successful `attach`.
pub open spec fn attached(v: MgrV, toks: Seq<Token>, table: Seq<PageId>, kstar: nat) -> MgrV {
    let h = v.next_handle;
    MgrV {
        leases: v.leases.insert(h, LeaseV { toks, table, c: kstar * v.b, pending: None }),
        refs: inc_seq(v.refs, table, table.len() as int),
        keys: revoke(v.keys, table.subrange(kstar as int, table.len() as int)),
        holders: Seq::new(
            v.p,
            |x: int| if table.contains(x as PageId) { v.holders[x].insert(h) } else { v.holders[x] },
        ),
        next_handle: (h + 1) as u64,
        ..v
    }
}

/// The complete C1 contract (all inputs, all results).
pub open spec fn attach_result(
    v: MgrV,
    v2: MgrV,
    toks: Seq<Token>,
    r: Result<(Handle, usize, PageTableView), Error>,
) -> bool {
    let m = cdiv(toks.len(), v.b);
    let ok_in = 1 <= toks.len() <= v.p * v.b;
    &&& toks.len() == 0 ==> r == Err::<(Handle, usize, PageTableView), Error>(Error::InvalidArgument)
    &&& (toks.len() > 0 && toks.len() > v.p * v.b) ==> r == Err::<(Handle, usize, PageTableView), Error>(
        Error::RequestTooLarge,
    )
    &&& (ok_in && v.next_handle == u64::MAX) ==> r == Err::<(Handle, usize, PageTableView), Error>(
        Error::IdentifierExhausted,
    )
    &&& (ok_in && v.next_handle < u64::MAX) ==> (r is Ok || r == Err::<(Handle, usize, PageTableView), Error>(
        Error::NoCapacity,
    ))
    &&& r == Err::<(Handle, usize, PageTableView), Error>(Error::NoCapacity) ==> exists|k: nat|
        is_kstar(v, toks, m, k) && v.free_set().len() < m - count_active(v, toks, k)
    &&& r matches Ok((h, cached, view)) ==> {
        let kstar = cached as nat / v.b;
        &&& ok_in
        &&& h == Handle { mgr: v.id, id: v.next_handle }
        &&& cached as nat == kstar * v.b
        &&& view.pages@.len() == m
        &&& is_kstar(v, toks, m, kstar)
        &&& v.free_set().len() >= m - count_active(v, toks, kstar)
        &&& attach_choice(v, toks, view.pages@, kstar)
        &&& v2 == attached(v, toks, view.pages@, kstar)
    }
}

pub proof fn lemma_kstar_unique(v: MgrV, toks: Seq<Token>, m: nat, k1: nat, k2: nat)
    requires
        is_kstar(v, toks, m, k1),
        is_kstar(v, toks, m, k2),
    ensures
        k1 == k2,
{
    if k1 < k2 {
        assert(v.has_hit(v.key_of(toks, k1)));
    }
    if k2 < k1 {
        assert(v.has_hit(v.key_of(toks, k2)));
    }
}

/// C1 success condition as an equivalence: for valid input and a free handle id, `attach`
/// succeeds iff `|F| >= d = m - u` (computed at the unique `k*`), and otherwise returns
/// `NoCapacity`.
pub proof fn lemma_attach_capacity_iff(
    v: MgrV,
    v2: MgrV,
    toks: Seq<Token>,
    r: Result<(Handle, usize, PageTableView), Error>,
    k: nat,
)
    requires
        attach_result(v, v2, toks, r),
        1 <= toks.len() <= v.p * v.b,
        v.next_handle < u64::MAX,
        is_kstar(v, toks, cdiv(toks.len(), v.b), k),
    ensures
        r is Ok <==> v.free_set().len() >= cdiv(toks.len(), v.b) - count_active(v, toks, k),
        r is Err ==> r == Err::<(Handle, usize, PageTableView), Error>(Error::NoCapacity),
        r matches Ok((h, cached, view)) ==> cached as nat == k * v.b,
{
    let m = cdiv(toks.len(), v.b);
    if r is Ok {
        let (h, cached, view) = r->Ok_0;
        lemma_kstar_unique(v, toks, m, cached as nat / v.b, k);
    } else {
        let k2 = choose|k2: nat| is_kstar(v, toks, m, k2) && v.free_set().len() < m - count_active(v, toks, k2);
        lemma_kstar_unique(v, toks, m, k2, k);
    }
}

// ---------------------------------------------------------------------------------------------
// Proof
// ---------------------------------------------------------------------------------------------

pub open spec fn hit_ok(v: MgrV, toks: Seq<Token>, hits: Seq<(PageId, bool)>) -> bool {
    forall|j: int|
        #![trigger hits[j]]
        0 <= j < hits.len() ==> {
            &&& in_index(v.keys, v.key_of(toks, j as nat), hits[j].0)
            &&& hits[j].1 == v.has_active_hit(v.key_of(toks, j as nat))
            &&& hits[j].1 == (v.refs[hits[j].0 as int] > 0)
        }
}

pub open spec fn n_active(hits: Seq<(PageId, bool)>, j: nat) -> nat
    decreases j,
{
    if j == 0 {
        0
    } else {
        n_active(hits, (j - 1) as nat) + if hits[j - 1].1 {
            1nat
        } else {
            0nat
        }
    }
}

proof fn lemma_n_active_eq(v: MgrV, toks: Seq<Token>, hits: Seq<(PageId, bool)>, j: nat)
    requires
        hit_ok(v, toks, hits),
        j <= hits.len(),
    ensures
        n_active(hits, j) == count_active(v, toks, j),
        n_active(hits, j) <= j,
    decreases j,
{
    if j > 0 {
        lemma_n_active_eq(v, toks, hits, (j - 1) as nat);
        assert(hits[j - 1].1 == v.has_active_hit(v.key_of(toks, (j - 1) as nat)));
    }
}

pub proof fn lemma_chain_logged_le(log: Log, ns: Seq<u8>, toks: Seq<Token>, b: nat, j: nat, k: nat)
    requires
        j <= k,
        chain_logged(log, ns, toks, b, k),
    ensures
        chain_logged(log, ns, toks, b, j),
    decreases k - j,
{
    if j < k {
        lemma_chain_logged_le(log, ns, toks, b, j, (k - 1) as nat);
    }
}

/// Two indexed hits at different chain positions are different pages (E8 via `lemma_chain_inj`).
proof fn lemma_hit_pages_distinct(v: MgrV, log: Log, toks: Seq<Token>, i1: nat, i2: nat, x: PageId)
    requires
        cfg_ok(v, log),
        (i1 + 1) * v.b <= toks.len(),
        (i2 + 1) * v.b <= toks.len(),
        chain_logged(log, v.ns, toks, v.b, i1),
        chain_logged(log, v.ns, toks, v.b, i2),
        in_index(v.keys, v.key_of(toks, i1), x),
        in_index(v.keys, v.key_of(toks, i2), x),
    ensures
        i1 == i2,
{
    lemma_chain_inj(log, v.b, v.ns, toks, i1, v.ns, toks, i2);
}

/// KV provenance of an indexed hit page (I5 + chain lemma).
proof fn lemma_hit_page_kv(v: MgrV, log: Log, x: PageId, toks: Seq<Token>, i: nat)
    requires
        inv(v, log),
        in_index(v.keys, v.key_of(toks, i), x),
        chain_logged(log, v.ns, toks, v.b, i),
        (i + 1) * v.b <= toks.len(),
    ensures
        forall|off: int|
            0 <= off < v.b ==> (v.vmap)(#[trigger] sl(v.b, x as int, off)) == toks.subrange(0, i * v.b + off + 1),
{
    reveal(page_ok);
    reveal(pub_ok);
    assert(page_ok(v, log, x));
    assert(pub_ok(v, log, x));
    let q = v.pdep[x as int];
    let tau = v.ptoks[x as int];
    lemma_chain_inj(log, v.b, v.ns, tau, q, v.ns, toks, i);
    let pre = toks.subrange(0, ((i + 1) * v.b) as int);
    assert(tau =~= tau.subrange(0, ((q + 1) * v.b) as int));
    assert(tau == pre);
    lemma_mul_succ(i, v.b);
    assert forall|off: int| 0 <= off < v.b implies (v.vmap)(#[trigger] sl(v.b, x as int, off)) == toks.subrange(
        0,
        i * v.b + off + 1,
    ) by {
        assert((v.vmap)(sl(v.b, x as int, off)) == tau.subrange(0, q * v.b + off + 1));
        assert(pre.subrange(0, i * v.b + off + 1) =~= toks.subrange(0, i * v.b + off + 1));
    }
}

proof fn lemma_suffix_contains(table: Seq<PageId>, k: int, i: int)
    requires
        table.no_duplicates(),
        0 <= k <= table.len(),
        0 <= i < table.len(),
    ensures
        table.subrange(k, table.len() as int).contains(table[i]) <==> i >= k,
{
    let s = table.subrange(k, table.len() as int);
    if i >= k {
        assert(s[i - k] == table[i]);
    }
    if s.contains(table[i]) {
        let j = choose|j: int| 0 <= j < s.len() && s[j] == table[i];
        assert(table[k + j] == table[i]);
    }
}

/// `Valid` is preserved by `attached`.
pub proof fn lemma_attach_inv(v: MgrV, log: Log, toks: Seq<Token>, table: Seq<PageId>, kstar: nat)
    requires
        inv(v, log),
        attach_choice(v, toks, table, kstar),
        kstar > 0 ==> chain_logged(log, v.ns, toks, v.b, (kstar - 1) as nat),
    ensures
        inv(attached(v, toks, table, kstar), log),
{
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    let h = v.next_handle;
    let v2 = attached(v, toks, table, kstar);
    let m = table.len();
    let fresh = table.subrange(kstar as int, m as int);
    let l = v2.leases[h];
    assert(!v.leases.contains_key(h)) by {
        if v.leases.contains_key(h) {
            assert(lease_ok(v, log, h));
        }
    }
    assert(table.subrange(0, m as int) =~= table);
    lemma_mul_mono(kstar, (m - 1) as nat, v.b);
    // The new lease.
    assert forall|j: int| 0 <= j < l.c implies (v2.vmap)(#[trigger] slot_of(v2.b, l.table, j)) == l.toks.subrange(
        0,
        j + 1,
    ) by {
        lemma_div_bounds(j as nat, v.b);
        let i = j / (v.b as int);
        if i >= kstar {
            lemma_mul_mono(kstar, i as nat, v.b);
        }
        lemma_mul_mono((i + 1) as nat, kstar, v.b);
        lemma_chain_logged_le(log, v.ns, toks, v.b, i as nat, (kstar - 1) as nat);
        assert(in_index(v.keys, v.key_of(toks, i as nat), table[i]));
        lemma_hit_page_kv(v, log, table[i], toks, i as nat);
        let off = j % (v.b as int);
        assert((v.vmap)(sl(v.b, table[i] as int, off)) == toks.subrange(0, i * v.b + off + 1));
    }
    assert forall|i: nat| i < l.table.len() implies #[trigger] blk_ok(v2, log, l, i) by {
        lemma_suffix_contains(table, kstar as int, i as int);
        if i < kstar {
            lemma_mul_mono(i + 1, kstar, v.b);
            lemma_chain_logged_le(log, v.ns, toks, v.b, i, (kstar - 1) as nat);
            assert(in_index(v.keys, v.key_of(toks, i), table[i as int]));
        } else {
            lemma_mul_mono(kstar, i, v.b);
            lemma_mul_succ(i, v.b);
        }
    }
    assert(lease_ok(v2, log, h));
    // Other leases: their pages are referenced, hence not fresh, hence keep their keys.
    assert forall|h2: u64| #[trigger] v2.leases.contains_key(h2) implies lease_ok(v2, log, h2) by {
        if h2 != h {
            assert(v.leases.contains_key(h2));
            assert(lease_ok(v, log, h2));
            let l2 = v.leases[h2];
            assert forall|i: int| 0 <= i < l2.table.len() implies v2.keys[#[trigger] l2.table[i] as int]
                == v.keys[l2.table[i] as int] by {
                let x = l2.table[i];
                assert(page_ok(v, log, x));
                assert(v.holders[x as int].contains(h2));
                vstd::set::lemma_set_contains_len(v.holders[x as int], h2);
                if fresh.contains(x) {
                    let j = choose|j: int| 0 <= j < fresh.len() && fresh[j] == x;
                    assert(table[kstar + j] == x);
                }
            }
            lemma_lease_frame(v, v2, log, log, h2);
        }
    }
    // Pages.
    assert forall|x: PageId| (x as nat) < v2.p implies #[trigger] page_ok(v2, log, x) by {
        assert(page_ok(v, log, x));
        assert(hold_ok(v, x));
        let hs = v.holders[x as int];
        if table.contains(x) {
            let i = choose|i: int| 0 <= i < m && table[i] == x;
            lemma_suffix_contains(table, kstar as int, i);
            assert(!hs.contains(h));
            vstd::set::lemma_set_insert_len(hs, h);
            assert(v2.refs[x as int] == v.refs[x as int] + 1);
            assert forall|h2: u64| #[trigger] v2.holders[x as int].contains(h2) <==> (v2.leases.contains_key(h2)
                && v2.leases[h2].table.contains(x)) by {
            }
            if i < kstar as int {
                assert(in_index(v.keys, v.key_of(toks, i as nat), table[i]));
            }
        } else {
            assert(!fresh.contains(x)) by {
                if fresh.contains(x) {
                    let j = choose|j: int| 0 <= j < fresh.len() && fresh[j] == x;
                    assert(table[kstar + j] == x);
                }
            }
            assert forall|h2: u64| #[trigger] v2.holders[x as int].contains(h2) <==> (v2.leases.contains_key(h2)
                && v2.leases[h2].table.contains(x)) by {
            }
        }
        assert(hold_ok(v2, x));
        if v2.keys[x as int] is Some {
            assert(v.keys[x as int] is Some);
            lemma_pub_frame(v, v2, log, log, x);
        }
    }
    assert forall|t: u64| #[trigger] v2.pend.contains_key(t) implies pend_ok(v2, t) by {
        assert(pend_ok(v, t));
        lemma_pend_frame(v, v2, t);
    }
}

// ---------------------------------------------------------------------------------------------
// Executable helpers
// ---------------------------------------------------------------------------------------------

/// Plan phase: walks the key chain from `Seed(ns)` and looks each complete block (except the
/// last logical block) up in the Index. Mutates only the ghost E8 log.
fn probe(
    index: &KeyIndex,
    keys: &Vec<Option<Digest>>,
    refs: &Vec<u64>,
    seed: &Digest,
    toks: &[Token],
    b: usize,
    m: usize,
    Ghost(v): Ghost<MgrV>,
    Tracked(log): Tracked<&mut DenLog>,
) -> (r: (Vec<(PageId, bool)>, Digest))
    requires
        index.wf(keys@),
        keys@ == v.keys,
        refs@ == v.refs,
        keys@.len() == refs@.len(),
        *seed == v.seed(),
        b as nat == v.b,
        b > 0,
        old(log)@.contains_key(v.seed()),
        old(log)@[v.seed()] == seed_input(v.ns),
        blocks_for(toks@.len(), b as nat, m as nat),
        toks@.len() <= max_slots(),
    ensures
        old(log)@.submap_of(final(log)@),
        is_kstar(v, toks@, m as nat, r.0@.len() as nat),
        hit_ok(v, toks@, r.0@),
        r.0@.len() > 0 ==> chain_logged(final(log)@, v.ns, toks@, v.b, (r.0@.len() - 1) as nat),
        r.1 == chain_parent(v.seed(), toks@, v.b, r.0@.len() as nat),
{
    let ghost log0 = log@;
    let mut hits: Vec<(PageId, bool)> = Vec::new();
    let mut head: Digest = *seed;
    let mut i: usize = 0;
    let mut stop = false;
    while i + 1 < m && !stop
        invariant
            index.wf(keys@),
            keys@ == v.keys,
            refs@ == v.refs,
            keys@.len() == refs@.len(),
            *seed == v.seed(),
            b as nat == v.b,
            b > 0,
            blocks_for(toks@.len(), b as nat, m as nat),
            toks@.len() <= max_slots(),
            log0.submap_of(log@),
            log@.contains_key(v.seed()),
            log@[v.seed()] == seed_input(v.ns),
            i + 1 <= m,
            hits@.len() == i,
            hit_ok(v, toks@, hits@),
            i > 0 ==> chain_logged(log@, v.ns, toks@, v.b, (i - 1) as nat),
            head == chain_parent(v.seed(), toks@, v.b, i as nat),
            stop ==> i + 1 < m && !v.has_hit(v.key_of(toks@, i as nat)),
        decreases m - i, if stop { 0int } else { 1int },
    {
        proof {
            lemma_mul_mono((i + 1) as nat, (m - 1) as nat, v.b);
            lemma_mul_succ(i as nat, v.b);
        }
        let lo = i * b;
        let hi = lo + b;
        let blk = vstd::slice::slice_subrange(toks, lo, hi);
        let ghost logp = log@;
        let k = hash_node(&head, blk, Tracked(log));
        proof {
            lemma_insert_submap(logp, k, node_input(head, blk@));
            vstd::map_lib::lemma_submap_of_trans(log0, logp, log@);
            assert(blk@ =~= block(toks@, v.b, i as nat));
            assert(k == v.key_of(toks@, i as nat));
            if i > 0 {
                lemma_chain_logged_mono(logp, log@, v.ns, toks@, v.b, (i - 1) as nat);
            }
            assert(log@.contains_key(v.seed()) && log@[v.seed()] == logp[v.seed()]);
            assert(chain_logged(log@, v.ns, toks@, v.b, i as nat));
        }
        match index.lookup(keys, refs, &k) {
            None => {
                stop = true;
            },
            Some(x) => {
                let ghost hits0 = hits@;
                proof {
                    if x.1 {
                        assert(v.has_active_hit(k));
                    } else {
                        assert(!v.has_active_hit(k));
                    }
                }
                hits.push(x);
                head = k;
                i = i + 1;
                proof {
                    assert forall|j: int| #![trigger hits@[j]] 0 <= j < hits@.len() implies {
                        &&& in_index(v.keys, v.key_of(toks@, j as nat), hits@[j].0)
                        &&& hits@[j].1 == v.has_active_hit(v.key_of(toks@, j as nat))
                        &&& hits@[j].1 == (v.refs[hits@[j].0 as int] > 0)
                    } by {
                        if j < hits0.len() {
                            assert(hits0[j] == hits@[j]);
                        }
                    }
                }
            },
        }
    }
    proof {
        assert forall|j: nat| j < hits@.len() implies v.has_hit(#[trigger] v.key_of(toks@, j)) by {
            assert(in_index(v.keys, v.key_of(toks@, j), hits@[j as int].0));
        }
    }
    (hits, head)
}

fn count_hits_active(hits: &Vec<(PageId, bool)>) -> (u: usize)
    ensures
        u as nat == n_active(hits@, hits@.len() as nat),
        u <= hits@.len(),
{
    let mut u: usize = 0;
    let mut j: usize = 0;
    while j < hits.len()
        invariant
            0 <= j <= hits@.len(),
            u as nat == n_active(hits@, j as nat),
            u <= j,
        decreases hits@.len() - j,
    {
        if hits[j].1 {
            u += 1;
        }
        j += 1;
    }
    u
}

/// Commit, part 1: take the hit pages; inactive (free) cache pages are reactivated.
fn take_hits(free: &mut IdxSet, hits: &Vec<(PageId, bool)>, Ghost(p): Ghost<nat>, Ghost(refs): Ghost<Seq<u64>>) -> (table: Vec<PageId>)
    requires
        p <= max_slots(),
        refs.len() == p,
        old(free).wf(),
        old(free).universe() == p,
        old(free)@ == free_of(p, refs),
        forall|j: int|
            #![trigger hits@[j]]
            0 <= j < hits@.len() ==> (hits@[j].0 as nat) < p && hits@[j].1 == (refs[hits@[j].0 as int] > 0),
        forall|j1: int, j2: int|
            0 <= j1 < hits@.len() && 0 <= j2 < hits@.len() && j1 != j2 ==> #[trigger] hits@[j1].0 != #[trigger] hits@[j2].0,
    ensures
        final(free).wf(),
        final(free).universe() == p,
        table@.len() == hits@.len(),
        forall|j: int| #![trigger table@[j]] 0 <= j < hits@.len() ==> table@[j] == hits@[j].0,
        forall|y: PageId| #[trigger] final(free)@.contains(y) <==> (free_of(p, refs).contains(y) && !table@.contains(y)),
        final(free)@.len() + (hits@.len() - n_active(hits@, hits@.len() as nat)) == old(free)@.len(),
        n_active(hits@, hits@.len() as nat) <= hits@.len(),
{
    let ghost f0 = free@;
    let mut table: Vec<PageId> = Vec::new();
    let mut j: usize = 0;
    proof {
        lemma_free_of(p, refs);
    }
    while j < hits.len()
        invariant
            p <= max_slots(),
            refs.len() == p,
            free.wf(),
            free.universe() == p,
            f0 == free_of(p, refs),
            forall|y: PageId| #[trigger] free_of(p, refs).contains(y) <==> ((y as nat) < p && refs[y as int] == 0),
            forall|k: int|
                #![trigger hits@[k]]
                0 <= k < hits@.len() ==> (hits@[k].0 as nat) < p && hits@[k].1 == (refs[hits@[k].0 as int] > 0),
            forall|j1: int, j2: int|
                0 <= j1 < hits@.len() && 0 <= j2 < hits@.len() && j1 != j2 ==> #[trigger] hits@[j1].0
                    != #[trigger] hits@[j2].0,
            0 <= j <= hits@.len(),
            table@.len() == j,
            forall|k: int| #![trigger table@[k]] 0 <= k < j ==> table@[k] == hits@[k].0,
            forall|y: PageId| #[trigger] free@.contains(y) <==> (free_of(p, refs).contains(y) && !table@.contains(y)),
            free@.len() + (j - n_active(hits@, j as nat)) == f0.len(),
            n_active(hits@, j as nat) <= j,
        decreases hits@.len() - j,
    {
        let (x, act) = hits[j];
        let ghost t0 = table@;
        let ghost fb = free@;
        proof {
            assert(hits@[j as int].0 == x);
            assert(!t0.contains(x)) by {
                if t0.contains(x) {
                    let k = choose|k: int| 0 <= k < t0.len() && t0[k] == x;
                    assert(table@[k] == hits@[k].0);
                }
            }
        }
        if !act {
            proof {
                assert(fb.contains(x));
            }
            free.remove(x);
            proof {
                vstd::set::lemma_set_remove_len(fb, x);
            }
        }
        table.push(x);
        proof {
            assert forall|y: PageId| #[trigger] free@.contains(y) <==> (free_of(p, refs).contains(y)
                && !table@.contains(y)) by {
                vstd::seq_lib::lemma_seq_contains_after_push(t0, x, y);
            }
        }
        j += 1;
    }
    table
}

/// Commit, part 2: pop `n` fresh pages from F and revoke their old keys.
pub(crate) fn take_fresh(
    free: &mut IdxSet,
    keys: &mut Vec<Option<Digest>>,
    index: &mut KeyIndex,
    table: &mut Vec<PageId>,
    n: usize,
    Ghost(p): Ghost<nat>,
)
    requires
        p <= max_slots(),
        old(free).wf(),
        old(free).universe() == p,
        old(free)@.len() >= n,
        old(keys)@.len() == p,
        old(index).wf(old(keys)@),
        old(table)@.no_duplicates(),
        forall|y: PageId| #[trigger] old(free)@.contains(y) ==> !old(table)@.contains(y),
    ensures
        final(free).wf(),
        final(free).universe() == p,
        final(table)@.len() == old(table)@.len() + n,
        final(table)@.subrange(0, old(table)@.len() as int) == old(table)@,
        final(table)@.no_duplicates(),
        forall|j: int|
            old(table)@.len() <= j < final(table)@.len() ==> old(free)@.contains(#[trigger] final(table)@[j]),
        forall|y: PageId| #[trigger] final(free)@.contains(y) <==> (old(free)@.contains(y) && !final(table)@.contains(y)),
        final(keys)@ == revoke(old(keys)@, final(table)@.subrange(old(table)@.len() as int, final(table)@.len() as int)),
        final(index).wf(final(keys)@),
{
    let ghost t0 = table@;
    let ghost k0 = keys@;
    let ghost f0 = free@;
    let mut c: usize = 0;
    proof {
        assert(table@.subrange(0, t0.len() as int) =~= t0);
        assert(revoke(k0, table@.subrange(t0.len() as int, table@.len() as int)) =~= k0);
    }
    while c < n
        invariant
            p <= max_slots(),
            free.wf(),
            free.universe() == p,
            keys@.len() == p,
            index.wf(keys@),
            0 <= c <= n,
            f0.len() >= n,
            table@.len() == t0.len() + c,
            table@.subrange(0, t0.len() as int) == t0,
            table@.no_duplicates(),
            forall|j: int| t0.len() <= j < table@.len() ==> f0.contains(#[trigger] table@[j]),
            forall|y: PageId| #[trigger] free@.contains(y) <==> (f0.contains(y) && !table@.contains(y)),
            forall|y: PageId| #[trigger] f0.contains(y) ==> !t0.contains(y),
            free@.len() + c == f0.len(),
            keys@ == revoke(k0, table@.subrange(t0.len() as int, table@.len() as int)),
        decreases n - c,
    {
        proof {
            free.lemma_bounds();
        }
        let ghost fb = free@;
        let x = free.pop_any();
        proof {
            vstd::set::lemma_set_remove_len(fb, x);
        }
        let ghost kb = keys@;
        let kx = keys[x];
        match kx {
            Some(kd) => {
                index.remove(Ghost(keys@), x, &kd);
                keys.set(x, None);
            },
            None => {},
        }
        let ghost tb = table@;
        table.push(x);
        c += 1;
        proof {
            assert(!tb.contains(x));
            assert(table@.subrange(0, t0.len() as int) =~= tb.subrange(0, t0.len() as int));
            assert(table@.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < table@.len() && 0 <= j < table@.len() && i != j implies table@[i]
                    != table@[j] by {
                    if i < tb.len() && j < tb.len() {
                    } else if i < tb.len() {
                        assert(tb.contains(tb[i]));
                    } else if j < tb.len() {
                        assert(tb.contains(tb[j]));
                    }
                }
            }
            assert forall|j: int| t0.len() <= j < table@.len() implies f0.contains(#[trigger] table@[j]) by {
                if j < tb.len() {
                    assert(tb[j] == table@[j]);
                }
            }
            assert forall|y: PageId| #[trigger] free@.contains(y) <==> (f0.contains(y) && !table@.contains(y)) by {
                vstd::seq_lib::lemma_seq_contains_after_push(tb, x, y);
            }
            let fr0 = tb.subrange(t0.len() as int, tb.len() as int);
            let fr1 = table@.subrange(t0.len() as int, table@.len() as int);
            assert(fr1 =~= fr0.push(x));
            assert(!fr0.contains(x)) by {
                if fr0.contains(x) {
                    let j = choose|j: int| 0 <= j < fr0.len() && fr0[j] == x;
                    assert(tb[t0.len() + j] == x);
                }
            }
            assert(kb[x as int] == k0[x as int]);
            assert(keys@[x as int] is None);
            assert forall|y: int| 0 <= y < p implies keys@[y] == revoke(k0, fr1)[y] by {
                vstd::seq_lib::lemma_seq_contains_after_push(fr0, x, y as PageId);
                assert((y as PageId) as int == y);
                if y != x as int {
                    assert(keys@[y] == kb[y]);
                    assert((y as PageId) != x);
                }
            }
            assert(keys@ =~= revoke(k0, fr1));
        }
    }
}

/// Commit, part 3: one reference per page-table entry.
fn inc_pages(refs: &mut Vec<u64>, tbl: &Vec<PageId>)
    requires
        tbl@.no_duplicates(),
        forall|i: int| 0 <= i < tbl@.len() ==> (#[trigger] tbl@[i] as int) < old(refs)@.len(),
        forall|i: int| 0 <= i < tbl@.len() ==> old(refs)@[#[trigger] tbl@[i] as int] < u64::MAX,
    ensures
        final(refs)@ == inc_seq(old(refs)@, tbl@, tbl@.len() as int),
{
    let ghost r0 = refs@;
    let mut i: usize = 0;
    proof {
        assert(inc_seq(r0, tbl@, 0) =~= r0);
    }
    while i < tbl.len()
        invariant
            0 <= i <= tbl@.len(),
            refs@ == inc_seq(r0, tbl@, i as int),
            tbl@.no_duplicates(),
            forall|k: int| 0 <= k < tbl@.len() ==> (#[trigger] tbl@[k] as int) < r0.len(),
            forall|k: int| 0 <= k < tbl@.len() ==> r0[#[trigger] tbl@[k] as int] < u64::MAX,
        decreases tbl@.len() - i,
    {
        let x = tbl[i];
        let ghost before = refs@;
        let ghost pre = tbl@.subrange(0, i as int);
        proof {
            assert(!pre.contains(x)) by {
                if pre.contains(x) {
                    let k = choose|k: int| 0 <= k < i && pre[k] == x;
                    assert(tbl@[k] == tbl@[i as int]);
                }
            }
            assert(refs@[x as int] == r0[x as int]);
        }
        let nv = refs[x] + 1;
        refs.set(x, nv);
        proof {
            let post = tbl@.subrange(0, i + 1);
            assert(post =~= pre.push(x));
            assert forall|y: int| 0 <= y < r0.len() implies refs@[y] == inc_seq(r0, tbl@, i + 1)[y] by {
                vstd::seq_lib::lemma_seq_contains_after_push(pre, x, y as PageId);
                if y == x as int {
                    assert(post[i as int] == x);
                } else {
                    assert(before[y] == inc_seq(r0, tbl@, i as int)[y]);
                }
            }
            assert(refs@ =~= inc_seq(r0, tbl@, i + 1));
        }
        i += 1;
    }
}

// ---------------------------------------------------------------------------------------------
// C1
// ---------------------------------------------------------------------------------------------

impl Manager {
    /// C1. `attach(T)`: reserve pages for all of `T`, reusing the longest indexed prefix of
    /// complete blocks except the last logical block (D2/D3).
    pub fn attach(&mut self, toks: &[Token]) -> (r: Result<(Handle, usize, PageTableView), Error>)
        requires
            old(self).valid(),
        ensures
            final(self).valid(),
            old(self).den_log().submap_of(final(self).den_log()),
            r is Err ==> final(self)@ == old(self)@,
            attach_result(old(self)@, final(self)@, toks@, r),
    {
        let n = toks.len();
        if n == 0 {
            return Err(Error::InvalidArgument);
        }
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        let b = self.b;
        let p = self.p;
        if n > p * b {
            return Err(Error::RequestTooLarge);
        }
        if self.next_handle == u64::MAX {
            return Err(Error::IdentifierExhausted);
        }
        proof {
            assert(b as nat <= (p as nat) * (b as nat)) by (nonlinear_arith) requires p >= 1;
            assert(p as nat <= (p as nat) * (b as nat)) by (nonlinear_arith) requires b >= 1;
        }
        let m = (n + b - 1) / b;
        let ghost v = self@;
        let ghost log0 = self.den_log();
        proof {
            lemma_cdiv_props(n as nat, b as nat);
            assert(m as nat == cdiv(n as nat, b as nat));
            assert(blocks_for(n as nat, b as nat, m as nat));
        }
        let (hits, head) = probe(
            &self.index,
            &self.keys,
            &self.refs,
            &self.seed,
            toks,
            b,
            m,
            Ghost(v),
            Tracked(self.log.borrow_mut()),
        );
        let kstar = hits.len();
        let u = count_hits_active(&hits);
        let ghost log1 = self.den_log();
        proof {
            lemma_n_active_eq(v, toks@, hits@, kstar as nat);
            lemma_inv_log_mono(v, log0, log1);
            lemma_mul_mono(kstar as nat, (m - 1) as nat, v.b);
        }
        let need = m - u;
        if self.free.len() < need {
            proof {
                assert(is_kstar(v, toks@, m as nat, kstar as nat) && v.free_set().len() < m - count_active(
                    v,
                    toks@,
                    kstar as nat,
                ));
            }
            return Err(Error::NoCapacity);
        }
        // Hits are distinct pages below P.
        proof {
            assert forall|j: int| #![trigger hits@[j]] 0 <= j < hits@.len() implies (hits@[j].0 as nat) < v.p
                && hits@[j].1 == (v.refs[hits@[j].0 as int] > 0) by {
                assert(in_index(v.keys, v.key_of(toks@, j as nat), hits@[j].0));
            }
            assert forall|j1: int, j2: int|
                0 <= j1 < hits@.len() && 0 <= j2 < hits@.len() && j1 != j2 implies #[trigger] hits@[j1].0
                != #[trigger] hits@[j2].0 by {
                if hits@[j1].0 == hits@[j2].0 {
                    lemma_mul_mono((j1 + 1) as nat, kstar as nat, v.b);
                    lemma_mul_mono((j2 + 1) as nat, kstar as nat, v.b);
                    lemma_chain_logged_le(log1, v.ns, toks@, v.b, j1 as nat, (kstar - 1) as nat);
                    lemma_chain_logged_le(log1, v.ns, toks@, v.b, j2 as nat, (kstar - 1) as nat);
                    assert(in_index(v.keys, v.key_of(toks@, j1 as nat), hits@[j1].0));
                    assert(in_index(v.keys, v.key_of(toks@, j2 as nat), hits@[j2].0));
                    lemma_hit_pages_distinct(v, log1, toks@, j1 as nat, j2 as nat, hits@[j1].0);
                }
            }
        }
        let mut table = take_hits(&mut self.free, &hits, Ghost(p as nat), Ghost(v.refs));
        let ghost tab_h = table@;
        proof {
            assert(table@.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < table@.len() && 0 <= j < table@.len() && i != j implies table@[i]
                    != table@[j] by {
                    assert(table@[i] == hits@[i].0);
                    assert(table@[j] == hits@[j].0);
                }
            }
        }
        take_fresh(&mut self.free, &mut self.keys, &mut self.index, &mut table, m - kstar, Ghost(p as nat));
        proof {
            lemma_free_of(p as nat, v.refs);
            assert forall|i: int| 0 <= i < table@.len() implies (#[trigger] table@[i] as nat) < v.p && v.refs[table@[i] as int]
                < u64::MAX by {
                if i < kstar {
                    assert(table@[i] == tab_h[i]);
                    assert(tab_h[i] == hits@[i].0);
                } else {
                    assert(free_of(p as nat, v.refs).contains(table@[i]));
                }
                assert(page_ok(v, log1, table@[i])) by {
                    reveal(page_ok);
                }
                reveal(page_ok);
            }
        }
        inc_pages(&mut self.refs, &table);
        let h = self.next_handle;
        self.next_handle = h + 1;
        let tcopy = vstd::slice::slice_to_vec(table.as_slice());
        let lease = LeaseC { toks: vstd::slice::slice_to_vec(toks), table: tcopy, c: kstar * b, pending: None, head };
        self.leases.insert(h, lease);
        let ghost v2 = attached(v, toks@, table@, kstar as nat);
        proof {
            // The choice is legal.
            assert forall|i: int| #![trigger table@[i]] 0 <= i < kstar implies in_index(
                v.keys,
                v.key_of(toks@, i as nat),
                table@[i],
            ) && (v.has_active_hit(v.key_of(toks@, i as nat)) ==> v.refs[table@[i] as int] > 0) by {
                assert(table@[i] == tab_h[i]);
                assert(tab_h[i] == hits@[i].0);
            }
            assert forall|i: int| #![trigger table@[i]] kstar <= i < table@.len() implies v.refs[table@[i] as int]
                == 0 by {
                assert(free_of(p as nat, v.refs).contains(table@[i]));
            }
            assert(attach_choice(v, toks@, table@, kstar as nat));
            lemma_attach_inv(v, log1, toks@, table@, kstar as nat);
        }
        self.g = Ghost(v2);
        proof {
            lemma_slot_decomp(kstar as nat, 0, v.b);
            assert(self.leases@.dom() =~= v2.leases.dom());
            assert forall|h2: u64| #[trigger] self.leases@.contains_key(h2) implies lease_view(self.leases@[h2])
                == v2.leases[h2] && Self::head_ok(v2, self.leases@[h2]) by {
                if h2 != h {
                    assert(Self::head_ok(v, self.leases@[h2]));
                } else {
                    assert(lease_view(self.leases@[h2]).toks =~= toks@);
                }
            }
            lemma_free_of(p as nat, self.refs@);
            lemma_free_of(p as nat, v.refs);
            assert(table@.subrange(0, table@.len() as int) =~= table@);
            assert forall|y: PageId| #[trigger] self.free@.contains(y) <==> v2.free_set().contains(y) by {
                if tab_h.contains(y) {
                    let k = choose|k: int| 0 <= k < tab_h.len() && tab_h[k] == y;
                    assert(table@.subrange(0, tab_h.len() as int)[k] == y);
                    assert(table@[k] == y);
                }
                if (y as nat) < v.p {
                    if table@.contains(y) {
                        let k = choose|k: int| 0 <= k < table@.len() && table@[k] == y;
                        assert(v.refs[table@[k] as int] < u64::MAX);
                        assert(self.refs@[y as int] == v.refs[y as int] + 1);
                    } else {
                        assert(self.refs@[y as int] == v.refs[y as int]);
                    }
                }
            }
            assert(self.free@ =~= v2.free_set());
        }
        let ghost cached = kstar * b;
        proof {
            assert((cached as nat) / v.b == kstar as nat);
        }
        Ok((Handle { mgr: self.id, id: h }, kstar * b, PageTableView { pages: table }))
    }
}

} // verus!
