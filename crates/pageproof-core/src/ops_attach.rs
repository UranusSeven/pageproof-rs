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

/// Legal page-table choice for `attach` (C1 success postconditions on the table), at an exact
/// `k*` of this class.
pub open spec fn attach_choice(v: MgrV, toks: Seq<Token>, table: Seq<PageId>, kstar: nat) -> bool {
    &&& is_kstar(v, toks, cdiv(toks.len(), v.b), kstar)
    &&& attach_choice_k(v, toks, table, kstar)
}

/// Legal page-table choice for a given hit prefix `k` (no maximality: the coordinator's joint
/// `k*` may be shorter than this class's own run).
pub open spec fn attach_choice_k(v: MgrV, toks: Seq<Token>, table: Seq<PageId>, kstar: nat) -> bool {
    &&& 1 <= toks.len()
    &&& toks.len() + v.cfg.mu <= v.p * v.b
    // The table covers the reach L + μ (D18); k* is capped by the input's own blocks.
    &&& blocks_for(toks.len() + v.cfg.mu, v.b, table.len())
    &&& kstar + 1 <= cdiv(toks.len(), v.b)
    &&& kstar + 1 <= table.len()
    &&& table.no_duplicates()
    &&& forall|i: int| 0 <= i < table.len() ==> (#[trigger] table[i] as nat) < v.p
    // i < k*: chosen from the call-time Index; an active candidate is used whenever one exists.
    &&& forall|i: int|
        #![trigger table[i]]
        0 <= i < kstar ==> in_index(v.keys, v.key_of(toks, i as nat), table[i]) && (v.has_active_hit(
            v.key_of(toks, i as nat),
        ) ==> v.refs[table[i] as int] > 0)
    // i >= k*: fresh pages taken from F (distinct from the hit pages by no_duplicates).
    &&& forall|i: int| #![trigger table[i]] kstar <= i < table.len() ==> v.refs[table[i] as int] == 0 && v.own[table[i] as int]
    &&& v.next_handle < u64::MAX
}

/// Abstract state after a successful `attach`.
pub open spec fn attached(v: MgrV, toks: Seq<Token>, table: Seq<PageId>, kstar: nat) -> MgrV {
    let h = v.next_handle;
    MgrV {
        leases: v.leases.insert(h, LeaseV { toks, table, c: kstar * v.b, pending: Seq::empty(), rho: toks.len() + v.cfg.mu, dfr: false, stopped: false }),
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
    let mr = cdiv(toks.len() + v.cfg.mu, v.b);
    let ok_in = 1 <= toks.len() && toks.len() + v.cfg.mu <= v.p * v.b;
    &&& toks.len() == 0 ==> r == Err::<(Handle, usize, PageTableView), Error>(Error::InvalidArgument)
    &&& (toks.len() > 0 && toks.len() + v.cfg.mu > v.p * v.b) ==> r == Err::<(Handle, usize, PageTableView), Error>(
        Error::RequestTooLarge,
    )
    &&& (ok_in && v.next_handle == u64::MAX) ==> r == Err::<(Handle, usize, PageTableView), Error>(
        Error::IdentifierExhausted,
    )
    &&& (ok_in && v.next_handle < u64::MAX) ==> (r is Ok || r == Err::<(Handle, usize, PageTableView), Error>(
        Error::NoCapacity,
    ))
    &&& r == Err::<(Handle, usize, PageTableView), Error>(Error::NoCapacity) ==> exists|k: nat|
        is_kstar(v, toks, m, k) && v.free_set().len() < mr - count_active(v, toks, k)
    &&& r matches Ok((h, cached, view)) ==> {
        let kstar = cached as nat / v.b;
        &&& ok_in
        &&& h == Handle { mgr: v.id, id: v.next_handle }
        &&& cached as nat == kstar * v.b
        &&& view.pages@.len() == mr
        &&& is_kstar(v, toks, m, kstar)
        &&& v.free_set().len() >= mr - count_active(v, toks, kstar)
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
        1 <= toks.len(),
        toks.len() + v.cfg.mu <= v.p * v.b,
        v.next_handle < u64::MAX,
        is_kstar(v, toks, cdiv(toks.len(), v.b), k),
    ensures
        r is Ok <==> v.free_set().len() >= cdiv(toks.len() + v.cfg.mu, v.b) - count_active(v, toks, k),
        r is Err ==> r == Err::<(Handle, usize, PageTableView), Error>(Error::NoCapacity),
        r matches Ok((h, cached, view)) ==> cached as nat == k * v.b,
{
    let m = cdiv(toks.len(), v.b);
    if r is Ok {
        let (h, cached, view) = r->Ok_0;
        lemma_kstar_unique(v, toks, m, cached as nat / v.b, k);
    } else {
        let mr = cdiv(toks.len() + v.cfg.mu, v.b);
        let k2 = choose|k2: nat| is_kstar(v, toks, m, k2) && v.free_set().len() < mr - count_active(v, toks, k2);
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

pub proof fn lemma_n_active_eq(v: MgrV, toks: Seq<Token>, hits: Seq<(PageId, bool)>, j: nat)
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
        attach_choice_k(v, toks, table, kstar),
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
    lemma_cdiv_props(toks.len(), v.b);
    lemma_mul_mono(kstar, (cdiv(toks.len(), v.b) - 1) as nat, v.b);
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
    // The last block index m-1 >= k*, so the last page is fresh.
    assert(v2.leases.dom() =~= v.leases.dom().insert(h));
    assert(v.refs[table[m - 1] as int] == 0);
    lemma_last_fresh(v, log, v2, h);
}

// ---------------------------------------------------------------------------------------------
// Executable helpers
// ---------------------------------------------------------------------------------------------

/// Plan phase: walks the key chain from `Seed(ns)` and looks each complete block (except the
/// last logical block) up in the Index. Mutates only the ghost E8 log.
// `m` is read only by the contract and loop invariants, which rustc does not see.
#[allow(unused_variables)]
fn probe(
    index: &KeyIndex,
    keys: &Vec<Option<Digest>>,
    refs: &Vec<u64>,
    seed: &Digest,
    toks: &[Token],
    b: usize,
    m: usize,
    cap: usize,
    Ghost(v): Ghost<MgrV>,
    Tracked(log): Tracked<&mut DenLog>,
) -> (r: (Vec<(PageId, bool)>, Digest, Vec<Digest>))
    requires
        cap + 1 <= m,
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
        is_kcap(v, toks@, cap as nat, r.0@.len() as nat),
        hit_ok(v, toks@, r.0@),
        r.2@.len() == r.0@.len(),
        forall|j: int| #![trigger r.2@[j]] 0 <= j < r.2@.len() ==> r.2@[j] == v.key_of(toks@, j as nat),
        r.0@.len() > 0 ==> chain_logged(final(log)@, v.ns, toks@, v.b, (r.0@.len() - 1) as nat),
        r.1 == chain_parent(v.seed(), toks@, v.b, r.0@.len() as nat),
{
    let ghost log0 = log@;
    let mut hits: Vec<(PageId, bool)> = Vec::new();
    let mut ks: Vec<Digest> = Vec::new();
    let mut head: Digest = *seed;
    let mut i: usize = 0;
    let mut stop = false;
    while i < cap && !stop
        invariant
            cap + 1 <= m,
            i <= cap,
            ks@.len() == i,
            forall|j: int| #![trigger ks@[j]] 0 <= j < ks@.len() ==> ks@[j] == v.key_of(toks@, j as nat),
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
            stop ==> i < cap && !v.has_hit(v.key_of(toks@, i as nat)),
        decreases cap - i, if stop { 0int } else { 1int },
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
                let ghost ks0 = ks@;
                hits.push(x);
                ks.push(k);
                head = k;
                i = i + 1;
                proof {
                    assert forall|j: int| #![trigger ks@[j]] 0 <= j < ks@.len() implies ks@[j] == v.key_of(toks@, j as nat) by {
                        if j < ks0.len() {
                            assert(ks0[j] == ks@[j]);
                        }
                    }
                }
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
    (hits, head, ks)
}

pub fn count_hits_active(hits: &Vec<(PageId, bool)>) -> (u: usize)
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
fn take_hits(
    free: &mut IdxSet,
    hits: &Vec<(PageId, bool)>,
    Ghost(p): Ghost<nat>,
    Ghost(refs): Ghost<Seq<u64>>,
    Ghost(own): Ghost<Seq<bool>>,
) -> (table: Vec<PageId>)
    requires
        p <= max_slots(),
        refs.len() == p,
        forall|j: int| #![trigger hits@[j]] 0 <= j < hits@.len() ==> own[hits@[j].0 as int],
        old(free).wf(),
        old(free).universe() == p,
        old(free)@ == free_of(p, refs, own),
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
        forall|y: PageId| #[trigger] final(free)@.contains(y) <==> (free_of(p, refs, own).contains(y) && !table@.contains(y)),
        final(free)@.len() + (hits@.len() - n_active(hits@, hits@.len() as nat)) == old(free)@.len(),
        n_active(hits@, hits@.len() as nat) <= hits@.len(),
{
    let ghost f0 = free@;
    let mut table: Vec<PageId> = Vec::new();
    let mut j: usize = 0;
    proof {
        lemma_free_of(p, refs, own);
    }
    while j < hits.len()
        invariant
            p <= max_slots(),
            refs.len() == p,
            free.wf(),
            free.universe() == p,
            f0 == free_of(p, refs, own),
            forall|y: PageId| #[trigger] free_of(p, refs, own).contains(y) <==> ((y as nat) < p && refs[y as int] == 0
                && own[y as int]),
            forall|k: int| #![trigger hits@[k]] 0 <= k < hits@.len() ==> own[hits@[k].0 as int],
            forall|k: int|
                #![trigger hits@[k]]
                0 <= k < hits@.len() ==> (hits@[k].0 as nat) < p && hits@[k].1 == (refs[hits@[k].0 as int] > 0),
            forall|j1: int, j2: int|
                0 <= j1 < hits@.len() && 0 <= j2 < hits@.len() && j1 != j2 ==> #[trigger] hits@[j1].0
                    != #[trigger] hits@[j2].0,
            0 <= j <= hits@.len(),
            table@.len() == j,
            forall|k: int| #![trigger table@[k]] 0 <= k < j ==> table@[k] == hits@[k].0,
            forall|y: PageId| #[trigger] free@.contains(y) <==> (free_of(p, refs, own).contains(y) && !table@.contains(y)),
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
            assert forall|y: PageId| #[trigger] free@.contains(y) <==> (free_of(p, refs, own).contains(y)
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
            assert(r0[tbl@[i as int] as int] < u64::MAX);
            assert forall|y: int| 0 <= y < r0.len() implies refs@[y] == inc_seq(r0, tbl@, i + 1)[y] by {
                vstd::seq_lib::lemma_seq_contains_after_push(pre, x, y as PageId);
                assert(tbl@.subrange(0, i + 1) == post);
                if y == x as int {
                    assert(post[i as int] == x);
                    assert(post.contains(x));
                    assert(refs@[y] == r0[y] + 1);
                } else {
                    assert(before[y] == inc_seq(r0, tbl@, i as int)[y]);
                    assert(refs@[y] == before[y]);
                    assert(post.contains(y as PageId) == pre.contains(y as PageId));
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

/// Result of a prefix probe of one paged class: hit pages (with their active flag), the chain
/// head after the run, and the chained keys of the run.
pub struct Probe {
    pub hits: Vec<(PageId, bool)>,
    pub head: Digest,
    pub keys: Vec<Digest>,
}

/// A probe's hits are valid in state `v`: each is an Index candidate for its chained key, active
/// iff referenced, and an active candidate is chosen whenever one exists; the chain is logged.
pub open spec fn probe_ok(v: MgrV, log: Log, toks: Seq<Token>, pr: Probe) -> bool {
    let k = pr.hits@.len();
    &&& hit_ok(v, toks, pr.hits@)
    &&& pr.keys@.len() == k
    &&& forall|j: int| #![trigger pr.keys@[j]] 0 <= j < k ==> pr.keys@[j] == v.key_of(toks, j as nat)
    &&& k > 0 ==> chain_logged(log, v.ns, toks, v.b, (k - 1) as nat)
    &&& pr.head == chain_parent(v.seed(), toks, v.b, k as nat)
    &&& (k + 1) * v.b <= toks.len() + v.b
}

/// The hits of a probe are owned, distinct pages below `P`.
pub proof fn lemma_probe_pages(v: MgrV, log: Log, toks: Seq<Token>, pr: Probe)
    requires
        inv(v, log),
        probe_ok(v, log, toks, pr),
        pr.hits@.len() * v.b <= toks.len(),
    ensures
        forall|j: int|
            #![trigger pr.hits@[j]]
            0 <= j < pr.hits@.len() ==> (pr.hits@[j].0 as nat) < v.p && pr.hits@[j].1 == (v.refs[pr.hits@[j].0 as int]
                > 0) && v.own[pr.hits@[j].0 as int],
        forall|j1: int, j2: int|
            0 <= j1 < pr.hits@.len() && 0 <= j2 < pr.hits@.len() && j1 != j2 ==> #[trigger] pr.hits@[j1].0
                != #[trigger] pr.hits@[j2].0,
{
    let hits = pr.hits@;
    let kstar = hits.len();
    assert forall|j: int| #![trigger hits[j]] 0 <= j < hits.len() implies (hits[j].0 as nat) < v.p
        && hits[j].1 == (v.refs[hits[j].0 as int] > 0) && v.own[hits[j].0 as int] by {
        assert(in_index(v.keys, v.key_of(toks, j as nat), hits[j].0));
        reveal(page_ok);
        assert(page_ok(v, log, hits[j].0));
    }
    assert forall|j1: int, j2: int|
        0 <= j1 < hits.len() && 0 <= j2 < hits.len() && j1 != j2 implies #[trigger] hits[j1].0 != #[trigger] hits[j2].0 by {
        if hits[j1].0 == hits[j2].0 {
            lemma_mul_mono((j1 + 1) as nat, kstar as nat, v.b);
            lemma_mul_mono((j2 + 1) as nat, kstar as nat, v.b);
            lemma_chain_logged_le(log, v.ns, toks, v.b, j1 as nat, (kstar - 1) as nat);
            lemma_chain_logged_le(log, v.ns, toks, v.b, j2 as nat, (kstar - 1) as nat);
            assert(in_index(v.keys, v.key_of(toks, j1 as nat), hits[j1].0));
            assert(in_index(v.keys, v.key_of(toks, j2 as nat), hits[j2].0));
            lemma_hit_pages_distinct(v, log, toks, j1 as nat, j2 as nat, hits[j1].0);
        }
    }
}

impl Manager {
    /// Probe phase of C1: the longest indexed prefix of complete-block keys, capped at `cap`.
    /// Changes nothing but the ghost E8 log.
    pub fn probe_prefix(&mut self, toks: &[Token], cap: usize) -> (r: Probe)
        requires
            old(self).valid(),
            1 <= toks@.len() <= old(self)@.p * old(self)@.b,
            cap + 1 <= cdiv(toks@.len(), old(self)@.b),
        ensures
            final(self).valid(),
            final(self)@ == old(self)@,
            old(self).den_log().submap_of(final(self).den_log()),
            is_kcap(old(self)@, toks@, cap as nat, r.hits@.len() as nat),
            probe_ok(old(self)@, final(self).den_log(), toks@, r),
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        let ghost v = self@;
        let ghost log0 = self.den_log();
        let b = self.b;
        let n = toks.len();
        proof {
            assert(b as nat <= v.p * v.b) by (nonlinear_arith) requires v.p >= 1, b as nat == v.b;
        }
        let m = (n + b - 1) / b;
        proof {
            lemma_cdiv_props(n as nat, b as nat);
            assert(m as nat == cdiv(n as nat, b as nat));
        }
        let (hits, head, keys) = probe(
            &self.index,
            &self.keys,
            &self.refs,
            &self.seed,
            toks,
            b,
            m,
            cap,
            Ghost(v),
            Tracked(self.log.borrow_mut()),
        );
        proof {
            lemma_inv_log_mono(v, log0, self.den_log());
            lemma_mul_mono((hits@.len() + 1) as nat, m as nat, v.b);
            lemma_mul_succ((m - 1) as nat, v.b);
        }
        Probe { hits, head, keys }
    }

    /// Shortens a probe to its first `k` hits (the coordinator's joint `k*`).
    pub fn truncate_probe(&self, pr: Probe, k: usize, Ghost(toks): Ghost<Seq<Token>>) -> (r: Probe)
        requires
            self.valid(),
            probe_ok(self@, self.den_log(), toks, pr),
            k <= pr.hits@.len(),
        ensures
            probe_ok(self@, self.den_log(), toks, r),
            r.hits@ == pr.hits@.subrange(0, k as int),
    {
        let ghost v = self@;
        let ghost log = self.den_log();
        let hits = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(pr.hits.as_slice(), 0, k));
        let keys = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(pr.keys.as_slice(), 0, k));
        let head = if k == 0 { self.seed } else { pr.keys[k - 1] };
        proof {
            self.lemma_valid();
            let r = Probe { hits, head, keys };
            assert forall|j: int| #![trigger hits@[j]] 0 <= j < hits@.len() implies {
                &&& in_index(v.keys, v.key_of(toks, j as nat), hits@[j].0)
                &&& hits@[j].1 == v.has_active_hit(v.key_of(toks, j as nat))
                &&& hits@[j].1 == (v.refs[hits@[j].0 as int] > 0)
            } by {
                assert(hits@[j] == pr.hits@[j]);
            }
            assert forall|j: int| #![trigger keys@[j]] 0 <= j < k implies keys@[j] == v.key_of(toks, j as nat) by {
                assert(keys@[j] == pr.keys@[j]);
            }
            if k > 0 {
                lemma_chain_logged_le(log, v.ns, toks, v.b, (k - 1) as nat, (pr.hits@.len() - 1) as nat);
            }
            lemma_mul_mono((k + 1) as nat, (pr.hits@.len() + 1) as nat, v.b);
        }
        Probe { hits, head, keys }
    }

    /// Commit phase of C1: build the table from the probe's hits plus fresh pages from `F`.
    pub fn attach_commit(&mut self, toks: &[Token], pr: Probe) -> (r: (Handle, usize, PageTableView))
        requires
            old(self).valid(),
            1 <= toks@.len(),
            toks@.len() + old(self)@.cfg.mu <= old(self)@.p * old(self)@.b,
            old(self)@.next_handle < u64::MAX,
            probe_ok(old(self)@, old(self).den_log(), toks@, pr),
            pr.hits@.len() + 1 <= cdiv(toks@.len(), old(self)@.b),
            old(self)@.free_set().len() >= cdiv(toks@.len() + old(self)@.cfg.mu, old(self)@.b) - count_active(
                old(self)@,
                toks@,
                pr.hits@.len() as nat,
            ),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            r.0 == (Handle { mgr: old(self)@.id, id: old(self)@.next_handle }),
            r.1 as nat == pr.hits@.len() * old(self)@.b,
            r.2.pages@.len() == cdiv(toks@.len() + old(self)@.cfg.mu, old(self)@.b),
            attach_choice_k(old(self)@, toks@, r.2.pages@, pr.hits@.len() as nat),
            final(self)@ == attached(old(self)@, toks@, r.2.pages@, pr.hits@.len() as nat),
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        let ghost v = self@;
        let ghost log1 = self.den_log();
        let b = self.b;
        let p = self.p;
        let n = toks.len();
        proof {
            assert(b as nat <= (p as nat) * (b as nat)) by (nonlinear_arith) requires p >= 1;
            assert(p as nat <= (p as nat) * (b as nat)) by (nonlinear_arith) requires b >= 1;
        }
        let _ = p;
        let m = (n + b - 1) / b;
        proof {
            lemma_cdiv_props(n as nat, b as nat);
            assert(m as nat == cdiv(n as nat, b as nat));
            assert(blocks_for(n as nat, b as nat, m as nat));
        }
        let _ = m;
        // The table covers the reach `L + μ` (D18).
        let nr = n + self.cfg.mu;
        let mr = (nr + b - 1) / b;
        proof {
            lemma_cdiv_props(nr as nat, b as nat);
            lemma_cdiv_mono(n as nat, nr as nat, b as nat);
            assert(mr as nat == cdiv(nr as nat, b as nat));
            assert(blocks_for(nr as nat, b as nat, mr as nat));
        }
        let hits = pr.hits;
        let head = pr.head;
        let kstar = hits.len();
        proof {
            lemma_n_active_eq(v, toks@, hits@, kstar as nat);
            lemma_mul_mono(kstar as nat, (m - 1) as nat, v.b);
            lemma_mul_mono((kstar + 1) as nat, m as nat, v.b);
            lemma_cdiv_props(n as nat, v.b);
            lemma_probe_pages(v, log1, toks@, Probe { hits, head, keys: pr.keys });
        }
        proof {
            assert forall|j: int| #![trigger hits@[j]] 0 <= j < hits@.len() implies (hits@[j].0 as nat) < v.p
                && hits@[j].1 == (v.refs[hits@[j].0 as int] > 0) && v.own[hits@[j].0 as int] by {
                assert(in_index(v.keys, v.key_of(toks@, j as nat), hits@[j].0));
                reveal(page_ok);
                assert(page_ok(v, log1, hits@[j].0));
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
        let mut table = take_hits(&mut self.free, &hits, Ghost(p as nat), Ghost(v.refs), Ghost(v.own));
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
        take_fresh(&mut self.free, &mut self.keys, &mut self.index, &mut table, mr - kstar, Ghost(p as nat));
        proof {
            lemma_free_of(p as nat, v.refs, v.own);
            assert forall|i: int| 0 <= i < table@.len() implies (#[trigger] table@[i] as nat) < v.p && v.refs[table@[i] as int]
                < u64::MAX by {
                if i < kstar {
                    assert(table@[i] == tab_h[i]);
                    assert(tab_h[i] == hits@[i].0);
                } else {
                    assert(free_of(p as nat, v.refs, v.own).contains(table@[i]));
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
        let lease = LeaseC { toks: vstd::slice::slice_to_vec(toks), table: tcopy, c: kstar * b, pending: Vec::new(), rho: nr, dfr: false, stopped: false, head };
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
                == 0 && v.own[table@[i] as int] by {
                assert(free_of(p as nat, v.refs, v.own).contains(table@[i]));
            }
            assert(attach_choice_k(v, toks@, table@, kstar as nat));
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
            lemma_free_of(p as nat, self.refs@, v.own);
            lemma_free_of(p as nat, v.refs, v.own);
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
        (Handle { mgr: self.id, id: h }, kstar * b, PageTableView { pages: table })
    }

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
        if n > p * b || self.cfg.mu > p * b - n {
            return Err(Error::RequestTooLarge);
        }
        if self.next_handle == u64::MAX {
            return Err(Error::IdentifierExhausted);
        }
        proof {
            assert(b as nat <= (p as nat) * (b as nat)) by (nonlinear_arith) requires p >= 1;
        }
        let m = (n + b - 1) / b;
        let ghost v = self@;
        proof {
            lemma_cdiv_props(n as nat, b as nat);
            assert(m as nat == cdiv(n as nat, b as nat));
        }
        let mr = (n + self.cfg.mu + b - 1) / b;
        proof {
            lemma_cdiv_props((n + self.cfg.mu) as nat, b as nat);
            lemma_cdiv_mono(n as nat, (n + self.cfg.mu) as nat, b as nat);
            assert(mr as nat == cdiv((n + self.cfg.mu) as nat, b as nat));
        }
        let pr = self.probe_prefix(toks, m - 1);
        let ghost kstar = pr.hits@.len();
        let u = count_hits_active(&pr.hits);
        proof {
            lemma_n_active_eq(v, toks@, pr.hits@, kstar as nat);
            assert(is_kstar(v, toks@, m as nat, kstar as nat));
        }
        if self.free.len() < mr - u {
            proof {
                assert(is_kstar(v, toks@, m as nat, kstar as nat) && v.free_set().len() < mr - count_active(
                    v,
                    toks@,
                    kstar as nat,
                ));
            }
            return Err(Error::NoCapacity);
        }
        let ghost log1 = self.den_log();
        let (h, cached, view) = self.attach_commit(toks, pr);
        proof {
            assert(attach_choice(v, toks@, view.pages@, kstar as nat));
            assert((cached as nat) / v.b == kstar as nat) by {
                lemma_slot_decomp(kstar as nat, 0, v.b);
            }
        }
        Ok((h, cached, view))
    }
}

} // verus!

verus! {

/// `count_active` depends only on `has_active_hit` (and the key chain).
pub proof fn lemma_count_active_eq(v: MgrV, w: MgrV, toks: Seq<Token>, k: nat)
    requires
        v.ns == w.ns,
        v.b == w.b,
        forall|key: Digest| #[trigger] w.has_active_hit(key) == v.has_active_hit(key),
    ensures
        count_active(w, toks, k) == count_active(v, toks, k),
    decreases k,
{
    if k > 0 {
        lemma_count_active_eq(v, w, toks, (k - 1) as nat);
        assert(w.has_active_hit(w.key_of(toks, (k - 1) as nat)) == v.has_active_hit(v.key_of(toks, (k - 1) as nat)));
    }
}

/// A probe taken in `v` stays valid in `w`, where `w` differs from `v` only by ownership and by
/// keys revoked on unreferenced pages whose slab is unprotected, provided every inactive hit's
/// slab is protected. Active candidates are referenced, so they survive; `w`'s Index is a subset
/// of `v`'s, so `has_active_hit` is unchanged.
pub proof fn lemma_probe_transfer(v: MgrV, w: MgrV, log: Log, toks: Seq<Token>, pr: Probe, per: nat, prot: Seq<bool>)
    requires
        probe_ok(v, log, toks, pr),
        w == (MgrV { own: w.own, keys: w.keys, ..v }),
        w.keys.len() == v.keys.len(),
        per >= 1,
        forall|x: int|
            #![trigger w.keys[x]]
            0 <= x < v.p ==> w.keys[x] == v.keys[x] || (w.keys[x] is None && v.refs[x] == 0 && !prot[x / (per as int)]),
        v.keys.len() == v.p,
        forall|j: int| #![trigger pr.hits@[j]] 0 <= j < pr.hits@.len() && !pr.hits@[j].1 ==> prot[pr.hits@[j].0 as int / (per as int)],
    ensures
        probe_ok(w, log, toks, pr),
        forall|key: Digest| #[trigger] w.has_active_hit(key) == v.has_active_hit(key),
        forall|key: Digest, x: PageId| #[trigger] in_index(w.keys, key, x) ==> in_index(v.keys, key, x),
        count_active(w, toks, pr.hits@.len() as nat) == count_active(v, toks, pr.hits@.len() as nat),
{
    assert forall|key: Digest, x: PageId| #[trigger] in_index(w.keys, key, x) implies in_index(v.keys, key, x) by {
        assert(w.keys[x as int] == v.keys[x as int] || w.keys[x as int] is None);
    }
    assert forall|key: Digest| #[trigger] w.has_active_hit(key) == v.has_active_hit(key) by {
        if v.has_active_hit(key) {
            let x = choose|x: PageId| #[trigger] in_index(v.keys, key, x) && v.refs[x as int] > 0;
            assert(w.keys[x as int] == v.keys[x as int]);
            assert(in_index(w.keys, key, x));
        }
        if w.has_active_hit(key) {
            let x = choose|x: PageId| #[trigger] in_index(w.keys, key, x) && w.refs[x as int] > 0;
            assert(in_index(v.keys, key, x));
        }
    }
    let hits = pr.hits@;
    assert forall|j: int| #![trigger hits[j]] 0 <= j < hits.len() implies {
        &&& in_index(w.keys, w.key_of(toks, j as nat), hits[j].0)
        &&& hits[j].1 == w.has_active_hit(w.key_of(toks, j as nat))
        &&& hits[j].1 == (w.refs[hits[j].0 as int] > 0)
    } by {
        let x = hits[j].0;
        assert(in_index(v.keys, v.key_of(toks, j as nat), x));
        if hits[j].1 {
            assert(v.refs[x as int] > 0);
            assert(w.keys[x as int] == v.keys[x as int]);
        } else {
            assert(prot[x as int / (per as int)]);
            assert(w.keys[x as int] == v.keys[x as int]);
        }
    }
    lemma_count_active_eq(v, w, toks, hits.len() as nat);
}

impl Manager {
    /// Every live lease id is below `next_handle`.
    pub(crate) proof fn lemma_handles_lt(&self)
        requires
            self.valid(),
        ensures
            forall|h: u64| #[trigger] self@.leases.contains_key(h) ==> h < self@.next_handle,
            forall|t: u64| #[trigger] self@.pend.contains_key(t) ==> t < self@.next_ticket,
    {
        reveal(lease_ok);
        reveal(pend_ok);
        assert forall|h: u64| #[trigger] self@.leases.contains_key(h) implies h < self@.next_handle by {
            assert(lease_ok(self@, self.den_log(), h));
        }
        assert forall|t: u64| #[trigger] self@.pend.contains_key(t) implies t < self@.next_ticket by {
            assert(pend_ok(self@, t));
        }
    }
}

} // verus!

verus! {

/// A copy of a probe (same views).
pub fn copy_probe(pr: &Probe) -> (r: Probe)
    ensures
        r.hits@ == pr.hits@,
        r.keys@ == pr.keys@,
        r.head == pr.head,
{
    Probe {
        hits: vstd::slice::slice_to_vec(pr.hits.as_slice()),
        keys: vstd::slice::slice_to_vec(pr.keys.as_slice()),
        head: pr.head,
    }
}

/// `probe_ok` depends only on the probe's views.
pub proof fn lemma_probe_ok_views(v: MgrV, log: Log, toks: Seq<Token>, a: Probe, b: Probe)
    requires
        probe_ok(v, log, toks, a),
        a.hits@ == b.hits@,
        a.keys@ == b.keys@,
        a.head == b.head,
    ensures
        probe_ok(v, log, toks, b),
{
}

/// `probe_ok` is monotone in the E8 log.
pub proof fn lemma_probe_ok_log(v: MgrV, log: Log, log2: Log, toks: Seq<Token>, pr: Probe)
    requires
        probe_ok(v, log, toks, pr),
        log.submap_of(log2),
    ensures
        probe_ok(v, log2, toks, pr),
{
    if pr.hits@.len() > 0 {
        lemma_chain_logged_mono(log, log2, v.ns, toks, v.b, (pr.hits@.len() - 1) as nat);
    }
}

} // verus!
