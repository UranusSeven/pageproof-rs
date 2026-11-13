//! C2 `extend`: append a suffix to a fully computed lease and atomically reserve its capacity.
use vstd::prelude::*;
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::arith::*;
use crate::manager::*;
use crate::idxset::IdxSet;
use crate::index::KeyIndex;
use crate::ops_attach::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// Abstract state after a successful `extend`: `T' = T ++ suffix`, table grows by `fresh`.
/// The input length after C2 (`suffix`) or C2b (`dfr`: the deferred position), `L̂'`.
pub open spec fn glen(l: LeaseV, suffix: Seq<Token>, dfr: bool) -> nat {
    if dfr { l.toks.len() + 1 } else { l.toks.len() + suffix.len() }
}

/// C2 and C2b: lease `h` grows by `suffix` (extend), or by the deferred position (extend_deferred,
/// `dfr`, with an empty suffix), and its table by `fresh`; the reach becomes `L̂' + μ` (D18, D22).
pub open spec fn grown(v: MgrV, h: u64, suffix: Seq<Token>, fresh: Seq<PageId>, dfr: bool) -> MgrV {
    let l = v.leases[h];
    MgrV {
        leases: v.leases.insert(
            h,
            LeaseV {
                toks: l.toks + suffix,
                table: l.table + fresh,
                rho: glen(l, suffix, dfr) + v.cfg.mu,
                dfr: l.dfr || dfr,
                ..l
            },
        ),
        refs: inc_seq(v.refs, fresh, fresh.len() as int),
        keys: revoke(v.keys, fresh),
        holders: Seq::new(
            v.p,
            |x: int| if fresh.contains(x as PageId) { v.holders[x].insert(h) } else { v.holders[x] },
        ),
        ..v
    }
}

pub open spec fn extended(v: MgrV, h: u64, suffix: Seq<Token>, fresh: Seq<PageId>) -> MgrV {
    grown(v, h, suffix, fresh, false)
}

/// C2's Busy (D21): the queue is full, or its oldest ticket has drafts or proposal rows.
pub open spec fn extend_busy(v: MgrV, l: LeaseV) -> bool {
    l.pending.len() > v.cfg.delta || (l.pending.len() > 0 && (v.pend[l.pending[0]].drafts.len() > 0
        || v.pend[l.pending[0]].propose))
}

/// Busy for C2 and C2b: extend needs a queue with room whose oldest ticket has no drafts or
/// proposal rows (D21); extend_deferred only a queue with room, so it may follow a verify (C2b).
pub open spec fn grow_busy(v: MgrV, l: LeaseV, dfr: bool) -> bool {
    if dfr { l.pending.len() > v.cfg.delta } else { extend_busy(v, l) }
}

/// The planned frontier of a lease (§3.2), as `ops_write::pfront`.
pub open spec fn pfront_x(v: MgrV, l: LeaseV) -> nat {
    if l.pending.len() == 0 { l.c } else { v.pend[l.pending[l.pending.len() - 1]].z }
}

/// The complete C2 (`dfr` false) and C2b (`dfr`, empty suffix) contracts.
pub open spec fn grow_result(v: MgrV, v2: MgrV, h: Handle, suffix: Seq<Token>, dfr: bool, r: Result<PageTableView, Error>) -> bool {
    let live0 = h.mgr == v.id && v.leases.contains_key(h.id);
    let l = v.leases[h.id];
    // A stopped lease accepts no new work (D25), checked first.
    let live = live0 && !l.stopped;
    let l2 = glen(l, suffix, dfr);
    let d = cdiv(l2 + v.cfg.mu, v.b) - l.table.len();
    // Pending tickets are allowed if they have room and no drafts or proposal rows (D21); every
    // input position must be computed or covered by a pending ticket, and none may be deferred.
    // extend_deferred needs a pending ticket whose bonus position it appends (D22).
    let busy = grow_busy(v, l, dfr);
    let ph = !l.dfr && pfront_x(v, l) == l.toks.len() && (dfr ==> l.pending.len() > 0);
    let arg = dfr || suffix.len() > 0;
    &&& !live0 ==> r == Err::<PageTableView, Error>(Error::InvalidHandle)
    &&& (live0 && l.stopped) ==> r == Err::<PageTableView, Error>(Error::InvalidPhase)
    &&& (live && busy) ==> r == Err::<PageTableView, Error>(Error::Busy)
    &&& (live && !busy && !ph) ==> r == Err::<PageTableView, Error>(Error::InvalidPhase)
    &&& (live && !busy && ph && !arg) ==> r == Err::<PageTableView, Error>(Error::InvalidArgument)
    &&& (live && !busy && ph && arg && l2 + v.cfg.mu > v.p * v.b) ==> r == Err::<PageTableView, Error>(
        Error::RequestTooLarge,
    )
    &&& (live && !busy && ph && arg && l2 + v.cfg.mu <= v.p * v.b) ==> (r is Ok <==> v.free_set().len() >= d)
    &&& (live && !busy && ph && arg && l2 + v.cfg.mu <= v.p * v.b && v.free_set().len() < d) ==> r
        == Err::<PageTableView, Error>(Error::NoCapacity)
    &&& r matches Ok(view) ==> {
        let fresh = view.pages@.subrange(l.table.len() as int, view.pages@.len() as int);
        &&& live
        &&& view.pages@.len() == cdiv(l2 + v.cfg.mu, v.b)
        &&& view.pages@.subrange(0, l.table.len() as int) == l.table
        &&& fresh.len() == d
        &&& fresh.no_duplicates()
        &&& forall|j: int| 0 <= j < fresh.len() ==> v.is_free(#[trigger] fresh[j])
        &&& v2 == grown(v, h.id, suffix, fresh, dfr)
        &&& v2.leases[h.id].c == l.c
    }
}

pub open spec fn extend_result(v: MgrV, v2: MgrV, h: Handle, suffix: Seq<Token>, r: Result<PageTableView, Error>) -> bool {
    grow_result(v, v2, h, suffix, false, r)
}

/// `Valid` is preserved by `grown`.
pub proof fn lemma_grow_inv(v: MgrV, log: Log, h: u64, suffix: Seq<Token>, fresh: Seq<PageId>, dfr: bool)
    requires
        inv(v, log),
        v.leases.contains_key(h),
        !grow_busy(v, v.leases[h], dfr),
        !v.leases[h].dfr,
        !v.leases[h].stopped,
        pfront_x(v, v.leases[h]) == v.leases[h].toks.len(),
        dfr ==> suffix.len() == 0 && v.leases[h].pending.len() > 0,
        !dfr ==> suffix.len() > 0,
        v.leases[h].toks.len() + (if dfr { 1nat } else { suffix.len() }) + v.cfg.mu <= v.p * v.b,
        blocks_for(v.leases[h].toks.len() + (if dfr { 1nat } else { suffix.len() }) + v.cfg.mu, v.b, v.leases[h].table.len() + fresh.len()),
        fresh.no_duplicates(),
        forall|j: int| 0 <= j < fresh.len() ==> v.is_free(#[trigger] fresh[j]),
    ensures
        inv(grown(v, h, suffix, fresh, dfr), log),
        forall|x: PageId| (x as nat) < v.p ==> #[trigger] grown(v, h, suffix, fresh, dfr).refs[x as int] == if fresh.contains(x) {
            v.refs[x as int] + 1
        } else {
            v.refs[x as int] as int
        },
{
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    let v2 = grown(v, h, suffix, fresh, dfr);
    let l = v.leases[h];
    let l2 = v2.leases[h];
    let n = l.table.len();
    assert(lease_ok(v, log, h));
    assert(l2.dfr == dfr);
    assert(lhat(l2) == l.toks.len() + (if dfr { 1nat } else { suffix.len() }));
    // With δ <= 1 and room in the queue, at most one ticket is pending and it ends at L, so c <= L.
    // extend needs it without drafts; extend_deferred keeps its drafts, which fit the new reach.
    assert(l.pending.len() <= 1);
    assert(l2.pending == l.pending);
    if l.pending.len() == 1 {
        assert(v.pend.contains_key(l.pending[0]));
        assert(pend_ok(v, l.pending[0]));
        assert(v.pend[l.pending[0]].z == l.toks.len());
        assert(v.pend[l.pending[0]].drafts.len() <= v.cfg.lam);
        if !dfr {
            assert(v.pend[l.pending[0]].drafts.len() == 0);
        }
        assert(pfront(v2, l2) == l.toks.len());
        assert(sdr(v2, l2) == v.pend[l.pending[0]].drafts.len());
    } else {
        assert(pfront(v2, l2) == l.c);
        assert(sdr(v2, l2) == 0);
    }
    if dfr {
        // X_h becomes [Q_h[0]] (I17); δ = 1 because a ticket is pending with room in the queue.
        assert(v.cfg.delta <= 1);
        assert(v.cfg.delta == 1);
        assert(dlam(v.cfg) == v.cfg.lam);
    }
    assert(l2.rho == lhat(l2) + v.cfg.mu);
    assert(l.c <= l.toks.len());
    assert(fresh.subrange(0, fresh.len() as int) =~= fresh);
    // Old table pages are referenced by h, fresh pages are free: disjoint.
    assert forall|i: int, j: int| 0 <= i < n && 0 <= j < fresh.len() implies #[trigger] l.table[i] != #[trigger] fresh[j] by {
        let x = l.table[i];
        assert(page_ok(v, log, x));
        assert(v.holders[x as int].contains(h));
        vstd::set::lemma_set_contains_len(v.holders[x as int], h);
    }
    assert(l2.table.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < l2.table.len() && 0 <= j < l2.table.len() && i != j implies l2.table[i]
            != l2.table[j] by {
            if i < n && j >= n {
                assert(l2.table[j] == fresh[j - n]);
            } else if i >= n && j < n {
                assert(l2.table[i] == fresh[i - n]);
            }
        }
    }
    // Token prefix is unchanged up to the old length.
    assert forall|j: int| 0 <= j <= l.toks.len() implies #[trigger] l2.toks.subrange(0, j) == l.toks.subrange(0, j) by {
        assert(l2.toks.subrange(0, j) =~= l.toks.subrange(0, j));
    }
    // The new lease.
    assert forall|j: int| 0 <= j < l2.c implies (v2.vmap)(#[trigger] slot_of(v2.b, l2.table, j)) == l2.toks.subrange(
        0,
        j + 1,
    ) by {
        lemma_div_bounds(j as nat, v.b);
        lemma_cdiv_props(l.toks.len(), v.b);
        let i = j / (v.b as int);
        if i >= n {
            lemma_mul_mono(n, i as nat, v.b);
        }
        assert(l2.table[i] == l.table[i]);
        assert(slot_of(v.b, l2.table, j) == slot_of(v.b, l.table, j));
        assert(l2.toks.subrange(0, j + 1) == l.toks.subrange(0, j + 1));
    }
    assert forall|i: nat| i < l2.table.len() implies #[trigger] blk_ok(v2, log, l2, i) by {
        if i < n {
            assert(blk_ok(v, log, l, i));
            assert(l2.table[i as int] == l.table[i as int]);
            let x = l.table[i as int];
            assert(!fresh.contains(x)) by {
                if fresh.contains(x) {
                    let j = choose|j: int| 0 <= j < fresh.len() && fresh[j] == x;
                }
            }
            if (i + 1) * v.b <= l.c {
                lemma_chain_key_prefix(v.seed(), l.toks, l2.toks, v.b, i);
                lemma_chain_logged_prefix(log, v.ns, l.toks, l2.toks, v.b, i);
            }
        } else {
            let x = fresh[i - n];
            assert(l2.table[i as int] == x);
            assert(fresh.contains(x));
            // (i+1)*b > c because i >= n = ceil(c/b) >= c/b.
            lemma_cdiv_props(l.toks.len(), v.b);
            lemma_mul_mono(n, i, v.b);
            lemma_mul_succ(i, v.b);
        }
    }
    assert(lease_ok(v2, log, h));
    assert forall|h2: u64| #[trigger] v2.leases.contains_key(h2) implies lease_ok(v2, log, h2) by {
        if h2 != h {
            assert(lease_ok(v, log, h2));
            let lo = v.leases[h2];
            assert forall|i: int| 0 <= i < lo.table.len() implies v2.keys[#[trigger] lo.table[i] as int]
                == v.keys[lo.table[i] as int] by {
                let x = lo.table[i];
                assert(page_ok(v, log, x));
                assert(v.holders[x as int].contains(h2));
                vstd::set::lemma_set_contains_len(v.holders[x as int], h2);
                if fresh.contains(x) {
                    let j = choose|j: int| 0 <= j < fresh.len() && fresh[j] == x;
                }
            }
            lemma_lease_frame(v, v2, log, log, h2);
        }
    }
    assert forall|x: PageId| (x as nat) < v2.p implies #[trigger] page_ok(v2, log, x) by {
        assert(page_ok(v, log, x));
        assert(hold_ok(v, x));
        let hs = v.holders[x as int];
        if fresh.contains(x) {
            let j = choose|j: int| 0 <= j < fresh.len() && fresh[j] == x;
            assert(v.refs[x as int] == 0);
            assert(hs.len() == 0);
            assert(!hs.contains(h)) by {
                if hs.contains(h) {
                    vstd::set::lemma_set_contains_len(hs, h);
                }
            }
            vstd::set::lemma_set_insert_len(hs, h);
            assert(!l.table.contains(x)) by {
                if l.table.contains(x) {
                    let i = choose|i: int| 0 <= i < n && l.table[i] == x;
                }
            }
            assert forall|h2: u64| #[trigger] v2.holders[x as int].contains(h2) <==> (v2.leases.contains_key(h2)
                && v2.leases[h2].table.contains(x)) by {
                if h2 == h {
                    assert(l2.table[n + j] == x);
                }
            }
            assert(v.next_handle >= 1) by {
                assert(lease_ok(v, log, h));
            }
        } else {
            assert forall|h2: u64| #[trigger] v2.holders[x as int].contains(h2) <==> (v2.leases.contains_key(h2)
                && v2.leases[h2].table.contains(x)) by {
                if h2 == h {
                    if l2.table.contains(x) {
                        let i = choose|i: int| 0 <= i < l2.table.len() && l2.table[i] == x;
                        if i >= n {
                            assert(fresh[i - n] == x);
                        }
                        assert(l.table[i] == x);
                    }
                    if l.table.contains(x) {
                        let i = choose|i: int| 0 <= i < n && l.table[i] == x;
                        assert(l2.table[i] == x);
                    }
                }
            }
        }
        assert(hold_ok(v2, x));
        if v2.keys[x as int] is Some {
            lemma_pub_frame(v, v2, log, log, x);
        }
    }
    assert forall|t: u64| #[trigger] v2.pend.contains_key(t) implies pend_ok(v2, t) by {
        assert(pend_ok(v, t));
        if v.pend[t].lease == h {
            // The pending ticket is the oldest; the reach is now whole for the longer input (I16).
            assert(l.pending.contains(t));
            assert(l.pending[0] == t);
        } else {
            lemma_pend_frame(v, v2, t);
        }
    }
    // Either nothing was added (last page unchanged) or the new last page is a fresh free page.
    assert(v2.leases.dom() =~= v.leases.dom().insert(h));
    if fresh.len() > 0 {
        assert(l2.table[l2.table.len() - 1] == fresh[fresh.len() - 1]);
        assert(v.is_free(fresh[fresh.len() - 1]));
    } else {
        assert(l2.table =~= l.table);
    }
    lemma_last_fresh(v, log, v2, h);
}

/// Increment refs of `tbl[k..]`.
fn inc_suffix(refs: &mut Vec<u64>, tbl: &Vec<PageId>, k: usize)
    requires
        old(refs)@.len() <= max_slots(),
        k <= tbl@.len(),
        tbl@.no_duplicates(),
        forall|i: int| k <= i < tbl@.len() ==> (#[trigger] tbl@[i] as int) < old(refs)@.len(),
        forall|i: int| k <= i < tbl@.len() ==> old(refs)@[#[trigger] tbl@[i] as int] < u64::MAX,
    ensures
        final(refs)@ == inc_seq(old(refs)@, tbl@.subrange(k as int, tbl@.len() as int), tbl@.len() - k),
{
    let ghost r0 = refs@;
    let ghost fr = tbl@.subrange(k as int, tbl@.len() as int);
    let mut i: usize = k;
    proof {
        assert(inc_seq(r0, fr, 0) =~= r0);
    }
    while i < tbl.len()
        invariant
            r0.len() <= max_slots(),
            k <= i <= tbl@.len(),
            fr == tbl@.subrange(k as int, tbl@.len() as int),
            refs@ == inc_seq(r0, fr, i - k),
            tbl@.no_duplicates(),
            forall|q: int| k <= q < tbl@.len() ==> (#[trigger] tbl@[q] as int) < r0.len(),
            forall|q: int| k <= q < tbl@.len() ==> r0[#[trigger] tbl@[q] as int] < u64::MAX,
        decreases tbl@.len() - i,
    {
        let x = tbl[i];
        let ghost before = refs@;
        let ghost pre = fr.subrange(0, i - k);
        proof {
            assert(!pre.contains(x)) by {
                if pre.contains(x) {
                    let q = choose|q: int| 0 <= q < pre.len() && pre[q] == x;
                    assert(tbl@[k + q] == tbl@[i as int]);
                }
            }
            assert(refs@[x as int] == r0[x as int]);
        }
        let nv = refs[x] + 1;
        refs.set(x, nv);
        proof {
            let post = fr.subrange(0, i - k + 1);
            assert(post =~= pre.push(x));
            assert forall|y: int| 0 <= y < r0.len() implies refs@[y] == inc_seq(r0, fr, i - k + 1)[y] by {
                vstd::seq_lib::lemma_seq_contains_after_push(pre, x, y as PageId);
                assert((y as PageId) as int == y);
                if y == x as int {
                    assert(post[i - k] == x);
                } else {
                    assert(before[y] == inc_seq(r0, fr, i - k)[y]);
                }
            }
            assert(refs@ =~= inc_seq(r0, fr, i - k + 1));
        }
        i += 1;
    }
}

impl Manager {
    /// C2's gate on a live lease: `(Busy, p_h)` as in `extend_result`.
    pub fn extend_gate(&self, h: u64) -> (r: (bool, usize))
        requires
            self.valid(),
            self@.leases.contains_key(h),
        ensures
            r.0 == extend_busy(self@, self@.leases[h]),
            r.1 as nat == pfront_x(self@, self@.leases[h]),
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
            reveal(lease_ok);
            assert(lease_ok(self@, self.den_log(), h));
        }
        let l = self.leases.get(&h).unwrap();
        let q = l.pending.len();
        if q == 0 {
            (false, l.c)
        } else {
            let t0 = l.pending[0];
            let tl = l.pending[q - 1];
            proof {
                assert(self@.pend.contains_key(t0));
                assert(self@.pend.contains_key(tl));
            }
            let r0 = self.pend.get(&t0).unwrap();
            let rl = self.pend.get(&tl).unwrap();
            (q > self.cfg.delta || r0.drafts.len() > 0 || r0.propose, rl.z)
        }
    }

    /// C2. `extend(h, suffix)`.
    pub fn extend(&mut self, h: Handle, suffix: &[Token]) -> (r: Result<PageTableView, Error>)
        requires
            old(self).valid(),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            r is Err ==> final(self)@ == old(self)@,
            extend_result(old(self)@, final(self)@, h, suffix@, r),
    {
        self.grow(h, suffix, false)
    }

    /// C2b. `extend_deferred(h)`: append the bonus position of the newest pending ticket (D22).
    pub fn extend_deferred(&mut self, h: Handle) -> (r: Result<PageTableView, Error>)
        requires
            old(self).valid(),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            r is Err ==> final(self)@ == old(self)@,
            grow_result(old(self)@, final(self)@, h, Seq::<Token>::empty(), true, r),
    {
        let none: Vec<Token> = Vec::new();
        proof {
            assert(none@ =~= Seq::<Token>::empty());
        }
        self.grow(h, none.as_slice(), true)
    }

    /// C2 and C2b.
    pub(crate) fn grow(&mut self, h: Handle, suffix: &[Token], dfr: bool) -> (r: Result<PageTableView, Error>)
        requires
            old(self).valid(),
            dfr ==> suffix@.len() == 0,
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            r is Err ==> final(self)@ == old(self)@,
            grow_result(old(self)@, final(self)@, h, suffix@, dfr, r),
    {
        if !self.handle_ok(h) {
            return Err(Error::InvalidHandle);
        }
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        let ghost v = self@;
        let ghost log = self.den_log();
        if self.leases.get(&h.id).unwrap().stopped {
            return Err(Error::InvalidPhase);
        }
        let (l_len, l_c, q, m, l_dfr) = {
            let l = self.leases.get(&h.id).unwrap();
            (l.toks.len(), l.c, l.pending.len(), l.table.len(), l.dfr)
        };
        proof {
            reveal(lease_ok);
            reveal(pend_ok);
            assert(lease_ok(v, log, h.id));
        }
        // Busy (D21): the queue is full, or, for extend, its oldest ticket has drafts or proposal rows.
        let (busy0, pf) = if q == 0 {
            (false, l_c)
        } else {
            let t0 = self.leases.get(&h.id).unwrap().pending[0];
            let tl = self.leases.get(&h.id).unwrap().pending[q - 1];
            proof {
                assert(v.pend.contains_key(t0));
                assert(v.pend.contains_key(tl));
            }
            let r0 = self.pend.get(&t0).unwrap();
            let rl = self.pend.get(&tl).unwrap();
            (q > self.cfg.delta || r0.drafts.len() > 0 || r0.propose, rl.z)
        };
        let busy = if dfr { q > self.cfg.delta } else { busy0 };
        proof {
            assert(busy0 == extend_busy(v, v.leases[h.id]));
            assert(busy == grow_busy(v, v.leases[h.id], dfr));
            assert(pf as nat == pfront_x(v, v.leases[h.id]));
        }
        if busy {
            return Err(Error::Busy);
        }
        if l_dfr || pf != l_len || (dfr && q == 0) {
            return Err(Error::InvalidPhase);
        }
        if !dfr && suffix.len() == 0 {
            return Err(Error::InvalidArgument);
        }
        // The input grows by the suffix, or by the deferred position (D22).
        let add = if dfr { 1 } else { suffix.len() };
        let b = self.b;
        let p = self.p;
        proof {
            reveal(lease_ok);
            assert(lease_ok(v, log, h.id));
            assert(b as nat <= (p as nat) * (b as nat)) by (nonlinear_arith) requires p >= 1;
            assert(p as nat <= (p as nat) * (b as nat)) by (nonlinear_arith) requires b >= 1;
        }
        let mu = self.cfg.mu;
        if add > p * b - l_len || mu > p * b - l_len - add {
            return Err(Error::RequestTooLarge);
        }
        let l2 = l_len + add;
        let m2 = (l2 + mu + b - 1) / b;
        proof {
            lemma_cdiv_props(l_len as nat, b as nat);
            lemma_cdiv_props((l2 + mu) as nat, b as nat);
            // m = ceil(ρ/B) with ρ <= L + μ < L' + μ, so m <= m2 (D18).
            if (m as nat) > (m2 as nat) {
                lemma_mul_mono(m2 as nat, (m - 1) as nat, b as nat);
            }
            assert(m <= m2);
        }
        let d = m2 - m;
        if self.free.len() < d {
            return Err(Error::NoCapacity);
        }
        let mut l = self.leases.remove(&h.id).unwrap();
        let ghost t0 = l.table@;
        let ghost f_old = self.free@;
        proof {
            reveal(page_ok);
            lemma_free_of(p as nat, v.refs, v.own);
            assert forall|y: PageId| #[trigger] self.free@.contains(y) implies !l.table@.contains(y) by {
                if l.table@.contains(y) {
                    assert(page_ok(v, log, y));
                    assert(v.holders[y as int].contains(h.id));
                    vstd::set::lemma_set_contains_len(v.holders[y as int], h.id);
                }
            }
        }
        take_fresh(&mut self.free, &mut self.keys, &mut self.index, &mut l.table, d, Ghost(p as nat));
        let ghost fresh = l.table@.subrange(m as int, l.table@.len() as int);
        proof {
            assert forall|j: int| 0 <= j < fresh.len() implies v.is_free(#[trigger] fresh[j]) by {
                assert(l.table@[m + j] == fresh[j]);
            }
            assert(fresh.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < fresh.len() && 0 <= j < fresh.len() && i != j implies fresh[i]
                    != fresh[j] by {
                    assert(l.table@[m + i] == fresh[i]);
                    assert(l.table@[m + j] == fresh[j]);
                }
            }
            assert forall|i: int| m <= i < l.table@.len() implies (#[trigger] l.table@[i] as int) < v.refs.len()
                && v.refs[l.table@[i] as int] < u64::MAX by {
                assert(fresh[i - m] == l.table@[i]);
            }
        }
        inc_suffix(&mut self.refs, &l.table, m);
        l.toks.extend_from_slice(suffix);
        l.rho = l2 + mu;
        l.dfr = dfr;
        proof {
            assert(l.toks@ =~= v.leases[h.id].toks + suffix@);
            assert(l.table@ =~= t0 + fresh);
            lemma_grow_inv(v, log, h.id, suffix@, fresh, dfr);
        }
        let view = PageTableView { pages: vstd::slice::slice_to_vec(l.table.as_slice()) };
        self.leases.insert(h.id, l);
        let ghost v2 = grown(v, h.id, suffix@, fresh, dfr);
        self.g = Ghost(v2);
        proof {
            assert(self.leases@.dom() =~= v2.leases.dom());
            assert forall|h2: u64| #[trigger] self.leases@.contains_key(h2) implies lease_view(self.leases@[h2])
                == v2.leases[h2] && Self::head_ok(v2, self.leases@[h2]) by {
                if h2 != h.id {
                    assert(Self::head_ok(v, self.leases@[h2]));
                } else {
                    let lc = self.leases@[h2];
                    let q = lc.c as nat / v.b;
                    lemma_cdiv_props(l_len as nat, b as nat);
                    if q > 0 {
                        lemma_div_bounds(lc.c as nat, v.b);
                        lemma_mul_succ((q - 1) as nat, v.b);
                        assert(lc.toks@.subrange(0, (q * v.b) as int) =~= v.leases[h.id].toks.subrange(0, (q * v.b) as int));
                        lemma_chain_key_prefix(v.seed(), v.leases[h.id].toks, lc.toks@, v.b, (q - 1) as nat);
                    }
                }
            }
            lemma_free_of(p as nat, self.refs@, v.own);
            lemma_free_of(p as nat, v.refs, v.own);
            assert(fresh.subrange(0, fresh.len() as int) =~= fresh);
            self.free.lemma_bounds();
            assert(f_old == free_of(p as nat, v.refs, v.own));
            assert forall|y: PageId| #[trigger] self.free@.contains(y) <==> v2.free_set().contains(y) by {
                assert(self.free@.contains(y) <==> (f_old.contains(y) && !l.table@.contains(y)));
                if f_old.contains(y) {
                    assert(!t0.contains(y));
                }
                assert(l.table@.contains(y) <==> (t0.contains(y) || fresh.contains(y))) by {
                    if l.table@.contains(y) {
                        let k = choose|k: int| 0 <= k < l.table@.len() && l.table@[k] == y;
                        if k >= m {
                            assert(fresh[k - m] == y);
                        } else {
                            assert(t0[k] == y);
                        }
                    }
                    if fresh.contains(y) {
                        let k = choose|k: int| 0 <= k < fresh.len() && fresh[k] == y;
                        assert(l.table@[m + k] == y);
                    }
                    if t0.contains(y) {
                        let k = choose|k: int| 0 <= k < t0.len() && t0[k] == y;
                        assert(l.table@[k] == y);
                    }
                }
                if (y as nat) < v.p {
                    if fresh.contains(y) {
                        let k = choose|k: int| 0 <= k < fresh.len() && fresh[k] == y;
                        assert(v.is_free(fresh[k]));
                        assert(self.refs@[y as int] == 1);
                    } else {
                        assert(self.refs@[y as int] == v.refs[y as int]);
                    }
                }
            }
            assert(self.free@ =~= v2.free_set());
            assert(fresh.subrange(0, fresh.len() as int) =~= fresh);
            assert(view.pages@.subrange(0, m as int) =~= t0);
        }
        Ok(view)
    }
}

} // verus!
