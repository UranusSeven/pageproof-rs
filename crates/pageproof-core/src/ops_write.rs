//! C3 `begin_write` and C4 `finish_write`: the ticket protocol, ghost `V` provenance, and
//! publication of newly completed blocks (main theorem §9.0 (a)–(d)).
use vstd::prelude::*;
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::arith::*;
use crate::manager::*;
use crate::e8::*;
use crate::index::KeyIndex;
#[cfg(verus_keep_ghost)]
use crate::index::in_index;
#[cfg(verus_keep_ghost)]
use crate::ops_attach::lemma_chain_logged_le;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

// ---------------------------------------------------------------------------------------------
// C3 begin_write
// ---------------------------------------------------------------------------------------------

pub open spec fn began(v: MgrV, h: u64, n: nat) -> MgrV {
    began_d(v, h, n, Seq::empty(), false)
}

/// `p_h`, the planned frontier (§3.2): `c_h`, or the end of the newest pending ticket.
pub open spec fn pfront(v: MgrV, l: LeaseV) -> nat {
    if l.pending.len() == 0 { l.c } else { v.pend[l.pending[l.pending.len() - 1]].z }
}

/// `begin_write` of `[p_h, p_h + n)` with draft tokens `drafts` after it (D16, D21): the ticket
/// joins the end of the lease's queue.
pub open spec fn began_d(v: MgrV, h: u64, n: nat, drafts: Seq<Token>, propose: bool) -> MgrV {
    let l = v.leases[h];
    let t = v.next_ticket;
    let a = pfront(v, l);
    MgrV {
        leases: v.leases.insert(h, LeaseV { pending: l.pending.push(t), ..l }),
        pend: v.pend.insert(t, PendV { lease: h, a, z: a + n, drafts, propose }),
        next_ticket: (t + 1) as u64,
        ..v
    }
}

/// Page `x` is an exclusive, unpublished write page of lease `h` (I6/I7/I9).
pub open spec fn write_page_ok(v: MgrV, h: u64, x: PageId) -> bool {
    &&& v.keys[x as int] is None
    &&& v.refs[x as int] == 1
    &&& forall|h2: u64| v.leases.contains_key(h2) && h2 != h ==> !(#[trigger] v.leases[h2].table).contains(x)
}

/// Plan correctness (§9.0 (a)): exact inputs, positions and slots; slots distinct, in range, on
/// exclusive unpublished pages; page mapping for `[0, z)`.
pub open spec fn plan_ok(v: MgrV, h: u64, n: nat, plan: ExecutionPlan) -> bool {
    let l = v.leases[h];
    let a = l.c;
    let z = l.c + n;
    &&& plan.ticket == Ticket { mgr: v.id, id: v.next_ticket }
    &&& plan.handle == Handle { mgr: v.id, id: h }
    &&& plan.block_size as nat == v.b
    &&& plan.input_ids@ == l.toks.subrange(a as int, z as int)
    &&& plan.positions@.len() == n
    &&& forall|q: int| 0 <= q < n ==> #[trigger] plan.positions@[q] as int == a + q
    &&& plan.write_slots@.len() == n
    &&& forall|q: int| 0 <= q < n ==> #[trigger] plan.write_slots@[q] as int == slot_of(v.b, l.table, a + q)
    &&& forall|q: int| 0 <= q < n ==> (#[trigger] plan.write_slots@[q] as nat) < v.p * v.b
    &&& forall|q1: int, q2: int|
        0 <= q1 < n && 0 <= q2 < n && q1 != q2 ==> #[trigger] plan.write_slots@[q1] != #[trigger] plan.write_slots@[q2]
    &&& forall|q: int| 0 <= q < n ==> write_page_ok(v, h, #[trigger] l.table[(a + q) / (v.b as int)])
    &&& plan.page_table@ == l.table.subrange(0, cdiv(z, v.b) as int)
}

/// Plan correctness with drafts (C3): inputs `T_h[a:z] ++ D` at `[a, z + k)`, and write slots for
/// `[a, z + k + ext)`, where `ext` is the class's extra write range (proposal rows, D20).
pub open spec fn plan_ok_d(v: MgrV, h: u64, n: nat, drafts: Seq<Token>, ext: nat, plan: ExecutionPlan) -> bool {
    let l = v.leases[h];
    let a = pfront(v, l);
    let z = a + n;
    let k = drafts.len();
    let w = z + k + ext;
    &&& plan.ticket == Ticket { mgr: v.id, id: v.next_ticket }
    &&& plan.handle == Handle { mgr: v.id, id: h }
    &&& plan.block_size as nat == v.b
    &&& plan.input_ids@ == l.toks.subrange(a as int, z as int) + drafts
    &&& plan.positions@.len() == n + k
    &&& forall|q: int| 0 <= q < n + k ==> #[trigger] plan.positions@[q] as int == a + q
    &&& plan.write_slots@.len() == w - a
    &&& forall|q: int| 0 <= q < w - a ==> #[trigger] plan.write_slots@[q] as int == slot_of(v.b, l.table, a + q)
    &&& forall|q: int| 0 <= q < w - a ==> (#[trigger] plan.write_slots@[q] as nat) < v.p * v.b
    &&& forall|q1: int, q2: int|
        0 <= q1 < w - a && 0 <= q2 < w - a && q1 != q2 ==> #[trigger] plan.write_slots@[q1] != #[trigger] plan.write_slots@[q2]
    &&& forall|q: int| 0 <= q < w - a ==> write_page_ok(v, h, #[trigger] l.table[(a + q) / (v.b as int)])
    &&& plan.page_table@ == l.table.subrange(0, cdiv(w, v.b) as int)
}

pub open spec fn begin_result(v: MgrV, v2: MgrV, h: Handle, n: usize, r: Result<(Ticket, ExecutionPlan), Error>) -> bool {
    let live = h.mgr == v.id && v.leases.contains_key(h.id);
    let l = v.leases[h.id];
    &&& !live ==> r is Err && r->Err_0 == Error::InvalidHandle
    &&& (live && l.pending.len() > 0) ==> r is Err && r->Err_0 == Error::Busy
    &&& (live && l.pending.len() == 0 && !(0 < n && l.c + n <= l.toks.len())) ==> r is Err && r->Err_0
        == Error::InvalidArgument
    &&& (live && l.pending.len() == 0 && 0 < n && l.c + n <= l.toks.len()) ==> (r is Ok <==> v.next_ticket < u64::MAX)
    &&& (live && l.pending.len() == 0 && 0 < n && l.c + n <= l.toks.len() && v.next_ticket == u64::MAX) ==> r is Err
        && r->Err_0 == Error::IdentifierExhausted
    &&& r matches Ok((t, plan)) ==> {
        &&& live
        &&& t == plan.ticket
        &&& plan_ok(v, h.id, n as nat, plan)
        // §9.0 (b): the context [0, a) is valid KV of the causal prefix.
        &&& forall|j: int| 0 <= j < l.c ==> (v.vmap)(#[trigger] slot_of(v.b, l.table, j)) == l.toks.subrange(0, j + 1)
        &&& v2 == began(v, h.id, n as nat)
    }
}

/// Arguments `begin_write_v` accepts on a live lease whose queue has room: input `[p, p + n)` from
/// the planned frontier `p`, drafts and proposal rows only after the whole input, and the write
/// range `[p, p + n + k + ext)` inside the reach.
pub open spec fn begin_args_ok(l: LeaseV, p: nat, n: nat, k: nat, ext: nat, propose: bool) -> bool {
    &&& 0 < n
    &&& p + n <= l.toks.len()
    &&& (k > 0 || ext > 0 || propose) ==> p + n == l.toks.len()
    &&& p + n + k + ext <= l.rho
}

pub open spec fn begin_result_v(
    v: MgrV,
    v2: MgrV,
    h: Handle,
    n: usize,
    drafts: Seq<Token>,
    ext: usize,
    propose: bool,
    r: Result<(Ticket, ExecutionPlan), Error>,
) -> bool {
    let live = h.mgr == v.id && v.leases.contains_key(h.id);
    let l = v.leases[h.id];
    // D21: the queue holds at most δ + 1 tickets.
    let busy = l.pending.len() > v.cfg.delta;
    let ok = begin_args_ok(l, pfront(v, l), n as nat, drafts.len(), ext as nat, propose);
    &&& !live ==> r is Err && r->Err_0 == Error::InvalidHandle
    &&& (live && busy) ==> r is Err && r->Err_0 == Error::Busy
    &&& (live && !busy && !ok) ==> r is Err && r->Err_0 == Error::InvalidArgument
    &&& (live && !busy && ok) ==> (r is Ok <==> v.next_ticket < u64::MAX)
    &&& (live && !busy && ok && v.next_ticket == u64::MAX) ==> r is Err && r->Err_0
        == Error::IdentifierExhausted
    &&& r matches Ok((t, plan)) ==> {
        &&& live
        &&& t == plan.ticket
        &&& plan_ok_d(v, h.id, n as nat, drafts, ext as nat, plan)
        // §9.0 (b): the computed prefix [0, c) is valid KV of the causal prefix.
        &&& forall|j: int| 0 <= j < l.c ==> (v.vmap)(#[trigger] slot_of(v.b, l.table, j)) == l.toks.subrange(0, j + 1)
        &&& v2 == began_d(v, h.id, n as nat, drafts, propose)
    }
}

pub proof fn lemma_begin_inv(v: MgrV, log: Log, h: u64, n: nat, drafts: Seq<Token>, propose: bool)
    requires
        inv(v, log),
        v.leases.contains_key(h),
        v.leases[h].pending.len() <= v.cfg.delta,
        begin_args_ok(v.leases[h], pfront(v, v.leases[h]), n, drafts.len(), 0, propose),
        v.next_ticket < u64::MAX,
    ensures
        inv(began_d(v, h, n, drafts, propose), log),
{
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    let v2 = began_d(v, h, n, drafts, propose);
    let t = v.next_ticket;
    let l = v.leases[h];
    let q = l.pending;
    assert(!v.pend.contains_key(t)) by {
        if v.pend.contains_key(t) {
            assert(pend_ok(v, t));
        }
    }
    assert(lease_ok(v, log, h));
    assert(!q.contains(t));
    if q.len() > 0 {
        assert(v.pend.contains_key(q[q.len() - 1]));
        assert(pend_ok(v, q[q.len() - 1]));
        assert(v.pend.contains_key(q[0]));
        assert(pend_ok(v, q[0]));
    }
    assert(v2.leases[h].pending == q.push(t));
    assert forall|h2: u64| #[trigger] v2.leases.contains_key(h2) implies lease_ok(v2, log, h2) by {
        assert(lease_ok(v, log, h2));
        let l2 = v2.leases[h2];
        assert forall|i: nat| i < l2.table.len() implies #[trigger] blk_ok(v2, log, l2, i) by {
            assert(blk_ok(v, log, v.leases[h2], i));
        }
        if h2 != h {
            assert forall|i: int| 0 <= i < l2.pending.len() implies v2.pend.contains_key(#[trigger] l2.pending[i])
                && v2.pend[l2.pending[i]].lease == h2 by {
                assert(v.pend.contains_key(l2.pending[i]));
            }
        } else {
            assert forall|i: int| 0 <= i < l2.pending.len() implies v2.pend.contains_key(#[trigger] l2.pending[i])
                && v2.pend[l2.pending[i]].lease == h2 by {
                if i < q.len() {
                    assert(l2.pending[i] == q[i]);
                    assert(v.pend.contains_key(q[i]));
                }
            }
            assert(l2.pending.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < l2.pending.len() && 0 <= j < l2.pending.len() && i != j implies l2.pending[i]
                    != l2.pending[j] by {
                    if i == q.len() {
                        assert(q.contains(l2.pending[j]) || j == q.len());
                    } else if j == q.len() {
                        assert(l2.pending[i] == q[i]);
                    }
                }
            }
        }
    }
    assert forall|x: PageId| (x as nat) < v2.p implies #[trigger] page_ok(v2, log, x) by {
        assert(page_ok(v, log, x));
        assert(hold_ok(v, x));
        assert forall|h2: u64| #[trigger] v2.holders[x as int].contains(h2) <==> (v2.leases.contains_key(h2)
            && v2.leases[h2].table.contains(x)) by {
        }
        if v.keys[x as int] is Some {
            lemma_pub_frame(v, v2, log, log, x);
        }
    }
    lemma_last_frame(v, v2);
    assert forall|t2: u64| #[trigger] v2.pend.contains_key(t2) implies pend_ok(v2, t2) by {
        if t2 != t {
            assert(pend_ok(v, t2));
            if v.pend[t2].lease == h {
                assert(q.contains(t2));
                assert(v2.leases[h].pending.contains(t2)) by {
                    let i = choose|i: int| 0 <= i < q.len() && q[i] == t2;
                    assert(v2.leases[h].pending[i] == t2);
                }
                assert(v2.leases[h].pending[0] == q[0]);
            } else {
                lemma_pend_frame(v, v2, t2);
            }
        } else {
            assert(v2.leases[h].pending[q.len() as int] == t);
            if q.len() == 0 {
                // With nothing in flight and input left, the reach is whole (I16).
                if l.c + n < l.toks.len() {
                    assert(l.c < l.toks.len());
                }
            } else {
                assert(v2.leases[h].pending[0] == q[0]);
                assert(q[0] != t);
            }
        }
    }
}

/// The plan's write pages are exclusive and unpublished; slots are in range and distinct, for any
/// write end `w` inside the reach.
proof fn lemma_plan_slots(v: MgrV, log: Log, h: u64, a: nat, w: nat)
    requires
        inv(v, log),
        v.leases.contains_key(h),
        v.leases[h].c <= a,
        a < w <= v.leases[h].rho,
    ensures
        forall|j: int|
            a <= j < w ==> {
                &&& 0 <= #[trigger] slot_of(v.b, v.leases[h].table, j) < v.p * v.b
                &&& (j / (v.b as int)) < v.leases[h].table.len()
                &&& write_page_ok(v, h, v.leases[h].table[j / (v.b as int)])
            },
        forall|j1: int, j2: int|
            a <= j1 < w && a <= j2 < w && j1 != j2 ==> #[trigger] slot_of(v.b, v.leases[h].table, j1) != #[trigger] slot_of(
                v.b,
                v.leases[h].table,
                j2,
            ),
{
    reveal(lease_ok);
    let l = v.leases[h];
    assert(lease_ok(v, log, h));
    assert forall|j: int| a <= j < w implies {
        &&& 0 <= #[trigger] slot_of(v.b, l.table, j) < v.p * v.b
        &&& (j / (v.b as int)) < l.table.len()
        &&& write_page_ok(v, h, l.table[j / (v.b as int)])
    } by {
        lemma_div_bounds(j as nat, v.b);
        let i = j / (v.b as int);
        let m = l.table.len();
        if i >= m {
            lemma_mul_mono(m, i as nat, v.b);
        }
        lemma_slot_of_props(v.b, v.p, l.table, j);
        // (i+1)*b > j >= a >= c.
        lemma_mul_succ(i as nat, v.b);
        lemma_uncomputed_exclusive(v, log, h, i as nat);
    }
    assert forall|j1: int, j2: int| a <= j1 < w && a <= j2 < w && j1 != j2 implies #[trigger] slot_of(v.b, l.table, j1)
        != #[trigger] slot_of(v.b, l.table, j2) by {
        lemma_div_bounds(j1 as nat, v.b);
        lemma_div_bounds(j2 as nat, v.b);
        let m = l.table.len();
        if j1 / (v.b as int) >= m {
            lemma_mul_mono(m, (j1 / (v.b as int)) as nat, v.b);
        }
        if j2 / (v.b as int) >= m {
            lemma_mul_mono(m, (j2 / (v.b as int)) as nat, v.b);
        }
        if slot_of(v.b, l.table, j1) == slot_of(v.b, l.table, j2) {
            lemma_slot_of_inj(v.b, l.table, j1, j2);
        }
    }
}

impl Manager {
    /// C3. `begin_write(h, n)`: issue a ticket and an immutable plan for `[c_h, c_h + n)`.
    pub fn begin_write(&mut self, h: Handle, n: usize) -> (r: Result<(Ticket, ExecutionPlan), Error>)
        requires
            old(self).valid(),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            r is Err ==> final(self)@ == old(self)@,
            begin_result(old(self)@, final(self)@, h, n, r),
    {
        let ghost v = self@;
        let ghost dl = self.den_log();
        proof {
            self.lemma_valid();
        }
        if self.handle_ok(h) {
            proof {
                self.lemma_rep_dom();
            }
            if self.leases.get(&h.id).unwrap().pending.len() > 0 {
                return Err(Error::Busy);
            }
        }
        let none: Vec<Token> = Vec::new();
        let r = self.begin_write_v(h, n, none.as_slice(), 0, false);
        proof {
            let e = Seq::<Token>::empty();
            assert(none@ =~= e);
            if h.mgr == v.id && v.leases.contains_key(h.id) {
                reveal(lease_ok);
                assert(lease_ok(v, dl, h.id));
                let l = v.leases[h.id];
                assert(pfront(v, l) == l.c);
                assert(begin_args_ok(l, l.c, n as nat, 0, 0, false) == (0 < n && l.c + n <= l.toks.len()));
            }
            if r is Ok {
                let plan = r->Ok_0.1;
                let l = v.leases[h.id];
                assert(l.toks.subrange(l.c as int, (l.c + n) as int) + e =~= l.toks.subrange(l.c as int, (l.c + n) as int));
                assert(plan_ok(v, h.id, n as nat, plan));
            }
        }
        r
    }

    /// C3 with drafts: issue a ticket and a plan feeding `T_h[c_h : c_h + n] ++ drafts`, with write
    /// slots for `ext` more positions (a drafter class's proposal rows, D20).
    pub fn begin_write_v(&mut self, h: Handle, n: usize, drafts: &[Token], ext: usize, propose: bool) -> (r: Result<(Ticket, ExecutionPlan), Error>)
        requires
            old(self).valid(),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            r is Err ==> final(self)@ == old(self)@,
            begin_result_v(old(self)@, final(self)@, h, n, drafts@, ext, propose, r),
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
        proof {
            reveal(lease_ok);
            assert(lease_ok(v, log, h.id));
            assert(v.p <= v.p * v.b) by (nonlinear_arith) requires v.b >= 1;
        }
        let q = self.leases.get(&h.id).unwrap().pending.len();
        if q > self.cfg.delta {
            return Err(Error::Busy);
        }
        // The planned frontier p_h: c_h, or the end of the newest pending ticket (§3.2).
        let a = if q == 0 {
            self.leases.get(&h.id).unwrap().c
        } else {
            let last = self.leases.get(&h.id).unwrap().pending[q - 1];
            proof {
                reveal(pend_ok);
                assert(v.pend.contains_key(last));
                assert(pend_ok(v, last));
            }
            self.pend.get(&last).unwrap().z
        };
        let mut l = self.leases.remove(&h.id).unwrap();
        let len = l.toks.len();
        let k = drafts.len();
        proof {
            assert(a as nat == pfront(v, v.leases[h.id]));
            assert(a <= len);
            assert(l.rho as nat <= v.p * v.b);
            assert(v.p * v.b <= max_slots());
        }
        if n == 0 || n > len - a || ((k > 0 || ext > 0 || propose) && a + n != len) || k > l.rho - a - n || ext > l.rho - a - n - k {
            self.leases.insert(h.id, l);
            proof {
                assert(self.leases@ =~= old(self).leases@);
            }
            return Err(Error::InvalidArgument);
        }
        if self.next_ticket == u64::MAX {
            self.leases.insert(h.id, l);
            proof {
                assert(self.leases@ =~= old(self).leases@);
            }
            return Err(Error::IdentifierExhausted);
        }
        let z = a + n;
        let zk = z + k;
        let w = zk + ext;
        let b = self.b;
        proof {
            if q > 0 {
                reveal(pend_ok);
                assert(pend_ok(v, v.leases[h.id].pending[q - 1]));
            }
            assert(v.leases[h.id].c <= a);
            lemma_plan_slots(v, log, h.id, a as nat, w as nat);
            lemma_cdiv_le(w as nat, v.b, l.table@.len());
        }
        let ghost lv = v.leases[h.id];
        // Inputs: the input interval, then the drafts.
        let mut input_ids = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(l.toks.as_slice(), a, z));
        input_ids.extend_from_slice(drafts);
        let mut positions: Vec<usize> = Vec::new();
        let mut write_slots: Vec<usize> = Vec::new();
        let mut j = a;
        while j < w
            invariant
                lv == lease_view(l),
                b as nat == v.b,
                b > 0,
                a <= j <= w,
                zk <= w,
                v.p * v.b <= max_slots(),
                positions@.len() == if j <= zk { j - a } else { zk - a },
                forall|q: int| 0 <= q < positions@.len() ==> #[trigger] positions@[q] as int == a + q,
                write_slots@.len() == j - a,
                forall|q: int| 0 <= q < j - a ==> #[trigger] write_slots@[q] as int == slot_of(v.b, lv.table, a + q),
                forall|jj: int|
                    a <= jj < w ==> {
                        &&& 0 <= #[trigger] slot_of(v.b, lv.table, jj) < v.p * v.b
                        &&& (jj / (v.b as int)) < lv.table.len()
                    },
                forall|i: int| 0 <= i < lv.table.len() ==> (#[trigger] lv.table[i] as nat) < v.p,
            decreases w - j,
        {
            if j < zk {
                positions.push(j);
            }
            proof {
                assert(0 <= slot_of(v.b, lv.table, j as int) < v.p * v.b);
                assert((j as int / (v.b as int)) < lv.table.len());
                lemma_slot_of_props(v.b, v.p, lv.table, j as int);
            }
            let pg = l.table[j / b];
            write_slots.push(pg * b + j % b);
            j += 1;
        }
        proof {
            assert(b as nat <= v.p * v.b) by (nonlinear_arith) requires v.p >= 1, b as nat == v.b;
            assert(w as nat <= lv.rho);
        }
        let nb = (w + b - 1) / b;
        let page_table = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(l.table.as_slice(), 0, nb));
        let t = self.next_ticket;
        self.next_ticket = t + 1;
        // The ticket joins the end of the queue (D21).
        l.pending.push(t);
        self.leases.insert(h.id, l);
        let dv = vstd::slice::slice_to_vec(drafts);
        self.pend.insert(t, PendC { lease: h.id, a, z, drafts: dv, propose });
        let ghost v2 = began_d(v, h.id, n as nat, drafts@, propose);
        proof {
            assert(begin_args_ok(v.leases[h.id], pfront(v, v.leases[h.id]), n as nat, drafts@.len(), 0, propose));
            lemma_begin_inv(v, log, h.id, n as nat, drafts@, propose);
        }
        self.g = Ghost(v2);
        let ticket = Ticket { mgr: self.id, id: t };
        let plan = ExecutionPlan {
            ticket,
            handle: h,
            input_ids,
            positions,
            write_slots,
            page_table,
            block_size: b,
        };
        proof {
            assert(self.leases@.dom() =~= v2.leases.dom());
            assert(self.pend@.dom() =~= v2.pend.dom());
            assert forall|h2: u64| #[trigger] self.leases@.contains_key(h2) implies lease_view(self.leases@[h2])
                == v2.leases[h2] && Self::head_ok(v2, self.leases@[h2]) by {
                if h2 != h.id {
                    assert(Self::head_ok(v, self.leases@[h2]));
                } else {
                    assert(Self::head_ok(v, old(self).leases@[h2]));
                }
            }
            assert forall|t2: u64| #[trigger] self.pend@.contains_key(t2) implies pend_view(self.pend@[t2]) == v2.pend[t2] by {
            }
            let lw = v.leases[h.id];
            assert(lw == lv);
            assert(lv.toks == l.toks@);
            assert(a as nat == pfront(v, lw));
            assert(z as nat == pfront(v, lw) + n);
            assert(w as nat == pfront(v, lw) + n + drafts@.len() + ext);
            assert(plan.input_ids@ == lw.toks.subrange(a as int, z as int) + drafts@);
            assert(positions@.len() == zk - a);
            assert(plan.write_slots@.len() == w - a);
            assert forall|q: int| 0 <= q < w - a implies (#[trigger] plan.write_slots@[q] as nat) < v.p * v.b by {
                assert(plan.write_slots@[q] as int == slot_of(v.b, lw.table, a + q));
            }
            assert forall|q1: int, q2: int| 0 <= q1 < w - a && 0 <= q2 < w - a && q1 != q2 implies #[trigger] plan.write_slots@[q1]
                != #[trigger] plan.write_slots@[q2] by {
                assert(plan.write_slots@[q1] as int == slot_of(v.b, lw.table, a + q1));
                assert(plan.write_slots@[q2] as int == slot_of(v.b, lw.table, a + q2));
            }
            assert forall|q: int| 0 <= q < w - a implies write_page_ok(v, h.id, #[trigger] lw.table[(a + q) / (v.b as int)]) by {
                let jj = a + q;
                assert(a <= jj < w);
                assert(0 <= slot_of(v.b, lw.table, jj));
            }
            assert(lease_ok(v, log, h.id));
            lemma_cdiv_props(w as nat, v.b);
            assert(nb as nat == cdiv(w as nat, v.b));
            assert(page_table@ =~= lw.table.subrange(0, nb as int));
            assert(plan_ok_d(v, h.id, n as nat, drafts@, ext as nat, plan));
        }
        Ok((ticket, plan))
    }
}


impl Manager {
    /// `(|Q_h|, p_h)` of a live lease (§3.2).
    pub fn queue_info(&self, h: u64) -> (r: (usize, usize))
        requires
            self.valid(),
            self@.leases.contains_key(h),
        ensures
            r.0 as nat == self@.leases[h].pending.len(),
            r.1 as nat == pfront(self@, self@.leases[h]),
            r.1 as nat <= self@.leases[h].toks.len(),
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
            reveal(lease_ok);
            reveal(pend_ok);
            assert(lease_ok(self@, self.den_log(), h));
        }
        let l = self.leases.get(&h).unwrap();
        let q = l.pending.len();
        if q == 0 {
            (0, l.c)
        } else {
            let last = l.pending[q - 1];
            proof {
                assert(self@.pend.contains_key(last));
                assert(pend_ok(self@, last));
            }
            (q, self.pend.get(&last).unwrap().z)
        }
    }

    /// Ticket `t` is the oldest ticket of its lease's queue (D21).
    pub fn is_head(&self, t: u64) -> (r: bool)
        requires
            self.valid(),
            self@.pend.contains_key(t),
        ensures
            r == (self@.leases[self@.pend[t].lease].pending[0] == t),
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
            reveal(pend_ok);
            reveal(lease_ok);
            assert(pend_ok(self@, t));
            assert(lease_ok(self@, self.den_log(), self@.pend[t].lease));
        }
        let h = self.pend.get(&t).unwrap().lease;
        self.leases.get(&h).unwrap().pending[0] == t
    }
}

// ---------------------------------------------------------------------------------------------
// C4 finish_write
// ---------------------------------------------------------------------------------------------

/// The executor's completion notice for one ticket. Its truth (the planned reads and writes
/// happened with the planned inputs and addresses, producing KV per the executor spec) is the
/// external assumption E1/E2/E5; the manager only checks that it names the ticket being finished.
#[derive(Clone, Copy)]
pub struct Completion {
    pub ticket: Ticket,
}

/// Ghost `V` after completing `[a, z)` of lease `l`.
pub open spec fn vmap_after(v: MgrV, l: LeaseV, a: nat, z: nat) -> spec_fn(int) -> Seq<Token> {
    |s: int|
        if exists|j: int| a <= j < z && #[trigger] slot_of(v.b, l.table, j) == s {
            l.toks.subrange(0, (choose|j: int| a <= j < z && #[trigger] slot_of(v.b, l.table, j) == s) + 1)
        } else {
            (v.vmap)(s)
        }
}

/// Functional postcondition of C4 (§9.0 (c)), stated relationally.
pub open spec fn finish_rel(v: MgrV, v2: MgrV, t: u64) -> bool {
    let r = v.pend[t];
    let h = r.lease;
    let l = v.leases[h];
    let lo = r.a / v.b;
    let hi = r.z / v.b;
    &&& v2.same_config(v)
    &&& v2.leases == v.leases.insert(h, LeaseV { c: r.z, pending: l.pending.drop_first(), ..l })
    &&& v2.pend == v.pend.remove(t)
    &&& v2.refs == v.refs
    &&& v2.own == v.own
    &&& v2.holders == v.holders
    &&& v2.next_handle == v.next_handle
    &&& v2.next_ticket == v.next_ticket
    &&& v2.vmap == vmap_after(v, l, r.a, r.z)
    &&& v2.keys.len() == v.keys.len()
    &&& v2.pdep.len() == v.pdep.len()
    &&& v2.ptoks.len() == v.ptoks.len()
    // New complete blocks are published with K(h, i); nothing else changes.
    &&& fin_published(v, v2, t)
    &&& fin_untouched(v, v2, t)
}

/// `finish_rel`, publication part: blocks `[a/B, z/B)` of the lease are published with `K(h, i)`.
pub open spec fn fin_published(v: MgrV, v2: MgrV, t: u64) -> bool {
    let r = v.pend[t];
    let l = v.leases[r.lease];
    let lo = r.a / v.b;
    let hi = r.z / v.b;
    forall|i: int|
        #![trigger l.table[i]]
        lo <= i < hi ==> v2.keys[l.table[i] as int] == Some(v.key_of(l.toks, i as nat)) && v2.pdep[l.table[i] as int]
            == i && v2.ptoks[l.table[i] as int] == l.toks.subrange(0, (i + 1) * v.b)
}

/// `finish_rel`, frame part: no other page's key or publication record changes.
pub open spec fn fin_untouched(v: MgrV, v2: MgrV, t: u64) -> bool {
    let r = v.pend[t];
    let l = v.leases[r.lease];
    let lo = r.a / v.b;
    let hi = r.z / v.b;
    forall|x: int|
        #![trigger v2.keys[x]]
        0 <= x < v.p && (forall|i: int| lo <= i < hi ==> l.table[i] as int != x) ==> v2.keys[x] == v.keys[x]
            && v2.pdep[x] == v.pdep[x] && v2.ptoks[x] == v.ptoks[x]
}

pub open spec fn finish_result(v: MgrV, v2: MgrV, log2: Log, t: Ticket, c: Completion, r: Result<usize, Error>) -> bool {
    let live = t.mgr == v.id && v.pend.contains_key(t.id) && c.ticket == t && v.leases[v.pend[t.id].lease].pending[0] == t.id;
    &&& !live ==> r is Err && r->Err_0 == Error::InvalidTicket
    &&& live ==> r is Ok
    &&& r matches Ok(z) ==> {
        let pr = v.pend[t.id];
        let l = v.leases[pr.lease];
        &&& live
        &&& z as nat == pr.z
        &&& finish_rel(v, v2, t.id)
        // §9.0 (c): every slot of [a, z) now carries its causal prefix ...
        &&& forall|j: int| pr.a <= j < pr.z ==> (v2.vmap)(#[trigger] slot_of(v.b, l.table, j)) == l.toks.subrange(0, j + 1)
        &&& forall|s: int|
            (forall|j: int| pr.a <= j < pr.z ==> #[trigger] slot_of(v.b, l.table, j) != s) ==> (#[trigger] (v2.vmap)(s))
                == (v.vmap)(s)
        // ... and each newly published block's key denotes exactly (ns, T_h[0:(i+1)B]).
        &&& forall|i: int|
            #![trigger l.table[i]]
            pr.a / v.b <= i < pr.z / v.b ==> v2.keys[l.table[i] as int] == Some(v.key_of(l.toks, i as nat)) && den(
                log2,
                v.b,
                v.key_of(l.toks, i as nat),
            ) == (v.ns, l.toks.subrange(0, (i + 1) * v.b))
    }
}

proof fn lemma_vmap_after(v: MgrV, l: LeaseV, a: nat, z: nat)
    requires
        v.b > 0,
        l.table.no_duplicates(),
        forall|j: int| a <= j < z ==> #[trigger] (j / (v.b as int)) < l.table.len(),
    ensures
        forall|j: int| a <= j < z ==> (vmap_after(v, l, a, z))(#[trigger] slot_of(v.b, l.table, j)) == l.toks.subrange(0, j + 1),
{
    assert forall|j: int| a <= j < z implies (vmap_after(v, l, a, z))(#[trigger] slot_of(v.b, l.table, j))
        == l.toks.subrange(0, j + 1) by {
        let s = slot_of(v.b, l.table, j);
        let j2 = choose|j2: int| a <= j2 < z && #[trigger] slot_of(v.b, l.table, j2) == s;
        lemma_slot_of_inj(v.b, l.table, j, j2);
    }
}

/// A slot of `[a, z)` of lease `l` is on page `table[j/b]`.
proof fn lemma_write_slot_page(v: MgrV, table: Seq<PageId>, j: int, pg: int, off: int)
    requires
        v.b > 0,
        0 <= j,
        (j / (v.b as int)) < table.len(),
        0 <= off < v.b,
        pg >= 0,
        sl(v.b, pg, off) == slot_of(v.b, table, j),
    ensures
        table[j / (v.b as int)] as int == pg,
{
    lemma_sl_page(v.b, table, j, pg, off);
}

/// Facts about a pending ticket's lease used by `finish_write`.
pub proof fn lemma_finish_facts(v: MgrV, log: Log, t: u64)
    requires
        inv(v, log),
        v.pend.contains_key(t),
        v.leases[v.pend[t].lease].pending[0] == t,
    ensures
        v.leases.contains_key(v.pend[t].lease),
        v.pend[t].a == v.leases[v.pend[t].lease].c,
        v.pend[t].a < v.pend[t].z <= v.leases[v.pend[t].lease].toks.len(),
        v.pend[t].a / v.b <= v.pend[t].z / v.b,
        v.pend[t].z / v.b <= v.leases[v.pend[t].lease].table.len(),
        v.leases[v.pend[t].lease].table.no_duplicates(),
        v.leases[v.pend[t].lease].toks.len() <= max_slots(),
        v.leases[v.pend[t].lease].table.len() * v.b >= v.leases[v.pend[t].lease].toks.len(),
        forall|i: int| 0 <= i < v.leases[v.pend[t].lease].table.len() ==> (#[trigger] v.leases[v.pend[t].lease].table[i] as nat) < v.p,
        forall|i: nat|
            v.pend[t].a / v.b <= i < v.pend[t].z / v.b ==> i < v.leases[v.pend[t].lease].table.len() && #[trigger] write_page_ok(
                v,
                v.pend[t].lease,
                v.leases[v.pend[t].lease].table[i as int],
            ),
{
    reveal(pend_ok);
    reveal(lease_ok);
    assert(pend_ok(v, t));
    let r = v.pend[t];
    let h = r.lease;
    let l = v.leases[h];
    assert(lease_ok(v, log, h));
    let b = v.b;
    let m = l.table.len();
    lemma_div_is_ordered_nat(r.a, r.z, b);
    // z/b <= m: (z/b)*b <= z <= L <= m*b.
    lemma_div_bounds(r.z, b);
    if r.z / b > m {
        lemma_mul_mono(m + 1, r.z / b, b);
        lemma_mul_succ(m, b);
    }
    assert(v.p * v.b <= max_slots());
    assert forall|i: nat| r.a / b <= i < r.z / b implies i < m && #[trigger] write_page_ok(v, h, l.table[i as int]) by {
        lemma_block_complete(i, r.a, b);
        lemma_block_complete(i, r.z, b);
        lemma_uncomputed_exclusive(v, log, h, i);
    }
}

pub proof fn lemma_finish_inv(v: MgrV, log: Log, log2: Log, t: u64, v2: MgrV)
    requires
        inv(v, log),
        log.submap_of(log2),
        v.pend.contains_key(t),
        v.leases[v.pend[t].lease].pending[0] == t,
        finish_rel(v, v2, t),
        v.pend[t].z / v.b > 0 ==> chain_logged(
            log2,
            v.ns,
            v.leases[v.pend[t].lease].toks,
            v.b,
            (v.pend[t].z / v.b - 1) as nat,
        ),
    ensures
        inv(v2, log2),
{
    lemma_inv_log_mono(v, log, log2);
    let lg = log2;
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    reveal(pub_ok);
    let r = v.pend[t];
    let h = r.lease;
    let l = v.leases[h];
    let a = r.a;
    let z = r.z;
    let b = v.b;
    let lo = a / b;
    let hi = z / b;
    let m = l.table.len();
    assert(pend_ok(v, t));
    assert(lease_ok(v, lg, h));
    assert(a == l.c && a < z && z <= l.toks.len());
    lemma_cdiv_props(l.toks.len(), b);
    lemma_div_bounds(a, b);
    lemma_div_bounds(z, b);
    // Positions below L map into the table.
    assert forall|j: int| 0 <= j < l.toks.len() implies #[trigger] (j / (b as int)) < m by {
        lemma_div_bounds(j as nat, b);
        if j / (b as int) >= m {
            lemma_mul_mono(m, (j / (b as int)) as nat, b);
        }
    }
    // Published indices are uncomputed blocks of h: exclusive, previously unpublished.
    lemma_finish_facts(v, lg, t);
    assert forall|i: int| lo <= i < hi implies i < m && #[trigger] write_page_ok(v, h, l.table[i]) by {
        assert(write_page_ok(v, h, l.table[(i as nat) as int]));
    }
    // All chain blocks below hi are logged.
    assert forall|i: nat| i < hi implies #[trigger] chain_logged(lg, v.ns, l.toks, b, i) by {
        lemma_chain_logged_le(lg, v.ns, l.toks, b, i, (hi - 1) as nat);
    }
    // Write slots are on write pages.
    lemma_plan_slots(v, lg, h, a, z);
    lemma_vmap_after(v, l, a, z);
    let l2 = v2.leases[h];
    // ---- lease h
    assert forall|j: int| 0 <= j < l2.c implies (v2.vmap)(#[trigger] slot_of(v2.b, l2.table, j)) == l2.toks.subrange(
        0,
        j + 1,
    ) by {
        if j < a {
            assert((v.vmap)(slot_of(b, l.table, j)) == l.toks.subrange(0, j + 1));
            assert forall|j2: int| a <= j2 < z implies slot_of(b, l.table, j2) != slot_of(b, l.table, j) by {
                if slot_of(b, l.table, j2) == slot_of(b, l.table, j) {
                    lemma_slot_of_inj(b, l.table, j, j2);
                }
            }
        }
    }
    assert forall|i: nat| i < l2.table.len() implies #[trigger] blk_ok(v2, lg, l2, i) by {
        assert(blk_ok(v, lg, l, i));
        lemma_block_complete(i, a, b);
        lemma_block_complete(i, z, b);
        if !(lo <= i < hi) {
            assert forall|i2: int| lo <= i2 < hi implies l.table[i2] as int != l.table[i as int] as int by {
                assert(i2 != i as int);
                assert(i2 < m);
                assert(l.table.no_duplicates());
            }
            assert(v2.keys[l.table[i as int] as int] == v.keys[l.table[i as int] as int]);
        }
    }
    assert(lease_ok(v2, lg, h));
    // ---- other leases
    assert forall|h2: u64| #[trigger] v2.leases.contains_key(h2) implies lease_ok(v2, lg, h2) by {
        if h2 != h {
            assert(lease_ok(v, lg, h2));
            let lo2 = v.leases[h2];
            assert forall|i: int| 0 <= i < lo2.table.len() implies v2.keys[#[trigger] lo2.table[i] as int]
                == v.keys[lo2.table[i] as int] by {
                let x = lo2.table[i];
                assert forall|i2: int| lo <= i2 < hi implies l.table[i2] as int != x as int by {
                    assert(write_page_ok(v, h, l.table[i2]));
                    assert(lo2.table.contains(x));
                }
            }
            assert forall|j: int| 0 <= j < lo2.c implies (v2.vmap)(#[trigger] slot_of(v.b, lo2.table, j)) == (v.vmap)(
                slot_of(v.b, lo2.table, j),
            ) by {
                lemma_cdiv_props(lo2.toks.len(), b);
                lemma_div_bounds(j as nat, b);
                let i2 = j / (b as int);
                if i2 >= lo2.table.len() {
                    lemma_mul_mono(lo2.table.len(), i2 as nat, b);
                }
                assert forall|j2: int| a <= j2 < z implies slot_of(b, l.table, j2) != slot_of(b, lo2.table, j) by {
                    if slot_of(b, l.table, j2) == slot_of(b, lo2.table, j) {
                        lemma_write_slot_page(v, l.table, j2, lo2.table[i2] as int, j % (b as int));
                        assert(write_page_ok(v, h, l.table[j2 / (b as int)]));
                        assert(lo2.table.contains(lo2.table[i2]));
                    }
                }
            }
            assert forall|i: int| 0 <= i < lo2.pending.len() implies #[trigger] lo2.pending[i] != t by {
                assert(v.pend.contains_key(lo2.pending[i]));
            }
            lemma_lease_frame(v, v2, lg, lg, h2);
        }
    }
    // ---- pages
    assert forall|x: PageId| (x as nat) < v2.p implies #[trigger] page_ok(v2, lg, x) by {
        assert(page_ok(v, lg, x));
        assert(hold_ok(v, x));
        assert forall|h2: u64| #[trigger] v2.holders[x as int].contains(h2) <==> (v2.leases.contains_key(h2)
            && v2.leases[h2].table.contains(x)) by {
        }
        if exists|i: int| lo <= i < hi && l.table[i] == x {
            let i = choose|i: int| lo <= i < hi && l.table[i] == x;
            assert(write_page_ok(v, h, l.table[i]));
            let tau = l.toks.subrange(0, (i + 1) * b);
            lemma_block_complete(i as nat, z, b);
            assert(tau.subrange(0, (i + 1) * b) =~= l.toks.subrange(0, (i + 1) * b));
            lemma_chain_logged_prefix(lg, v.ns, l.toks, tau, b, i as nat);
            lemma_chain_key_prefix(v.seed(), l.toks, tau, b, i as nat);
            assert forall|off: int| 0 <= off < b implies (v2.vmap)(#[trigger] sl(b, x as int, off)) == tau.subrange(
                0,
                i * b + off + 1,
            ) by {
                lemma_slot_of_block(b, l.table, i, off);
                let j = i * b + off;
                lemma_mul_succ(i as nat, b);
                assert(tau.subrange(0, j + 1) =~= l.toks.subrange(0, j + 1));
                if j < a {
                    assert((v.vmap)(slot_of(b, l.table, j)) == l.toks.subrange(0, j + 1));
                    assert forall|j2: int| a <= j2 < z implies slot_of(b, l.table, j2) != slot_of(b, l.table, j) by {
                        if slot_of(b, l.table, j2) == slot_of(b, l.table, j) {
                            lemma_slot_of_inj(b, l.table, j, j2);
                        }
                    }
                }
            }
            assert(pub_ok(v2, lg, x));
        } else {
            assert(v2.keys[x as int] == v.keys[x as int]);
            if v.keys[x as int] is Some {
                assert(pub_ok(v, lg, x));
                assert forall|off: int| 0 <= off < b implies (v2.vmap)(#[trigger] sl(b, x as int, off)) == (v.vmap)(
                    sl(b, x as int, off),
                ) by {
                    assert forall|j2: int| a <= j2 < z implies slot_of(b, l.table, j2) != sl(b, x as int, off) by {
                        if slot_of(b, l.table, j2) == sl(b, x as int, off) {
                            lemma_write_slot_page(v, l.table, j2, x as int, off);
                            assert(write_page_ok(v, h, l.table[j2 / (b as int)]));
                        }
                    }
                }
                lemma_pub_frame(v, v2, lg, lg, x);
            }
        }
    }
    lemma_last_frame(v, v2);
    // ---- pending: the next ticket of the queue, if any, is now the oldest and starts at c' = z.
    assert forall|t2: u64| #[trigger] v2.pend.contains_key(t2) implies pend_ok(v2, t2) by {
        assert(pend_ok(v, t2));
        if v.pend[t2].lease == h {
            let q = v.leases[h].pending;
            let i = choose|i: int| 0 <= i < q.len() && q[i] == t2;
            assert(i != 0);
            assert(i == 1 && q.len() == 2);
            assert(v2.leases[h].pending[0] == t2);
        } else {
            lemma_pend_frame(v, v2, t2);
        }
    }
}

impl Manager {
    /// C4. `finish_write(ticket, completion)`: consume the ticket once, set `c_h = z`, update the
    /// ghost `V`, publish every newly completed block under its chained key.
    pub fn finish_write(&mut self, t: Ticket, completion: Completion) -> (r: Result<usize, Error>)
        requires
            old(self).valid(),
        ensures
            final(self).valid(),
            old(self).den_log().submap_of(final(self).den_log()),
            r is Err ==> final(self)@ == old(self)@,
            finish_result(old(self)@, final(self)@, final(self).den_log(), t, completion, r),
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        if t.mgr != self.id || completion.ticket.mgr != t.mgr || completion.ticket.id != t.id
            || !self.pend.contains_key(&t.id) || !self.is_head(t.id) {
            return Err(Error::InvalidTicket);
        }
        let ghost v = self@;
        let ghost log0 = self.den_log();
        let pr = self.pend.remove(&t.id).unwrap();
        let hid = pr.lease;
        let a = pr.a;
        let z = pr.z;
        let b = self.b;
        proof {
            reveal(pend_ok);
            reveal(lease_ok);
            assert(pend_ok(v, t.id));
            assert(lease_ok(v, log0, hid));
            assert(self.leases@.contains_key(hid));
            lemma_finish_facts(v, log0, t.id);
        }
        let mut l = self.leases.remove(&hid).unwrap();
        let ghost lv = v.leases[hid];
        let lo = a / b;
        let hi = z / b;
        proof {
            lemma_cdiv_props(lv.toks.len(), v.b);
            lemma_div_bounds(a as nat, v.b);
            lemma_div_bounds(z as nat, v.b);
            assert(Self::head_ok(v, l));
            // Block lo-1 is complete and computed, hence logged.
            if lo > 0 {
                lemma_mul_succ((lo - 1) as nat, v.b);
                if lo > lv.table.len() {
                    lemma_mul_mono(lv.table.len(), lo as nat, v.b);
                }
                assert(blk_ok(v, log0, lv, (lo - 1) as nat));
            }
            assert(l.head == chain_parent(v.seed(), lv.toks, v.b, lo as nat));
        }
        let ghost keys0 = self.keys@;
        let ghost mut pd = v.pdep;
        let ghost mut pt = v.ptoks;
        let mut head = l.head;
        let mut i = lo;
        while i < hi
            invariant
                lv == lease_view(l),
                b as nat == v.b,
                b > 0,
                lo <= i <= hi,
                lo == a / b,
                hi == z / b,
                hi <= lv.table.len(),
                lv.table.no_duplicates(),
                v.pend.contains_key(t.id),
                v.pend[t.id].lease == hid,
                v.pend[t.id].a == a,
                v.pend[t.id].z == z,
                forall|i3: nat| lo <= i3 < hi ==> #[trigger] write_page_ok(v, hid, lv.table[i3 as int]),
                forall|i3: int| 0 <= i3 < lv.table.len() ==> (#[trigger] lv.table[i3] as nat) < v.p,
                a as nat == lv.c,
                a < z <= lv.toks.len(),
                lv.toks.len() <= max_slots(),
                inv(v, log0),
                v.leases.contains_key(hid),
                v.keys == keys0,
                self.keys@.len() == v.p,
                self.index.wf(self.keys@),
                log0.submap_of(self.log@@),
                self.log@@.contains_key(v.seed()) && self.log@@[v.seed()] == seed_input(v.ns),
                head == chain_parent(v.seed(), lv.toks, v.b, i as nat),
                i > 0 ==> chain_logged(self.log@@, v.ns, lv.toks, v.b, (i - 1) as nat),
                pd.len() == v.p,
                pt.len() == v.p,
                forall|i2: int|
                    #![trigger lv.table[i2]]
                    lo <= i2 < i ==> self.keys@[lv.table[i2] as int] == Some(v.key_of(lv.toks, i2 as nat))
                        && pd[lv.table[i2] as int] == i2 && pt[lv.table[i2] as int] == lv.toks.subrange(
                        0,
                        (i2 + 1) * v.b,
                    ),
                forall|x: int|
                    #![trigger self.keys@[x]]
                    0 <= x < v.p && (forall|i2: int| lo <= i2 < i ==> lv.table[i2] as int != x) ==> self.keys@[x]
                        == keys0[x] && pd[x] == v.pdep[x] && pt[x] == v.ptoks[x],
            decreases hi - i,
        {
            proof {
                lemma_block_complete(i as nat, z as nat, v.b);
                lemma_mul_succ(i as nat, v.b);
                assert(write_page_ok(v, hid, lv.table[i as int]));
                assert forall|i2: int| lo <= i2 < i implies lv.table[i2] as int != lv.table[i as int] as int by {
                    assert(i2 != i as int);
                }
            }
            let lo_t = i * b;
            let hi_t = lo_t + b;
            let blk = vstd::slice::slice_subrange(l.toks.as_slice(), lo_t, hi_t);
            let ghost logp = self.log@@;
            let k = hash_node(&head, blk, Tracked(self.log.borrow_mut()));
            let x = l.table[i];
            proof {
                lemma_insert_submap(logp, k, node_input(head, blk@));
                vstd::map_lib::lemma_submap_of_trans(log0, logp, self.log@@);
                assert(blk@ =~= block(lv.toks, v.b, i as nat));
                assert(k == v.key_of(lv.toks, i as nat));
                if i > 0 {
                    lemma_chain_logged_mono(logp, self.log@@, v.ns, lv.toks, v.b, (i - 1) as nat);
                }
                assert(self.log@@.contains_key(v.seed()) && self.log@@[v.seed()] == logp[v.seed()]);
                assert(chain_logged(self.log@@, v.ns, lv.toks, v.b, i as nat));
                assert(lv.table[i as int] == x);
                assert((x as nat) < v.p);
                assert forall|i2: int| lo <= i2 < i implies lv.table[i2] as int != x as int by {
                    assert(i2 != i as int);
                }
                assert(self.keys@[x as int] == keys0[x as int]);
            }
            let ghost kb = self.keys@;
            let ghost pdb = pd;
            let ghost ptb = pt;
            proof {
                assert forall|y: int|
                    0 <= y < v.p && (forall|i2: int| lo <= i2 < i ==> lv.table[i2] as int != y) implies kb[y] == keys0[y]
                    && pdb[y] == v.pdep[y] && pdb.len() == v.p && ptb[y] == v.ptoks[y] by {
                    assert(self.keys@[y] == keys0[y]);
                }
            }
            self.index.add(Ghost(self.keys@), x, &k);
            self.keys.set(x, Some(k));
            proof {
                pd = pd.update(x as int, i as nat);
                pt = pt.update(x as int, lv.toks.subrange(0, ((i + 1) * b) as int));
                assert(self.keys@ == kb.update(x as int, Some(k)));
                assert forall|i2: int| #![trigger lv.table[i2]] lo <= i2 < i + 1 implies self.keys@[lv.table[i2] as int]
                    == Some(v.key_of(lv.toks, i2 as nat)) && pd[lv.table[i2] as int] == i2 && pt[lv.table[i2] as int]
                    == lv.toks.subrange(0, (i2 + 1) * v.b) by {
                    if i2 < i {
                        assert(lv.table[i2] as int != x as int) by {
                            assert(lv.table.no_duplicates());
                        }
                    }
                }
                assert forall|y: int|
                    #![trigger self.keys@[y]]
                    0 <= y < v.p && (forall|i2: int| lo <= i2 < i + 1 ==> lv.table[i2] as int != y) implies self.keys@[y]
                    == keys0[y] && pd[y] == v.pdep[y] && pt[y] == v.ptoks[y] by {
                    assert(lv.table[i as int] as int != y);
                    assert(y != x as int);
                    assert(forall|i2: int| lo <= i2 < i ==> lv.table[i2] as int != y);
                    assert(kb[y] == keys0[y] && pdb[y] == v.pdep[y] && ptb[y] == v.ptoks[y]);
                    assert(self.keys@[y] == kb[y]);
                    assert(pd[y] == pdb[y]);
                    assert(pt[y] == ptb[y]);
                }
            }
            head = k;
            i += 1;
        }
        l.c = z;
        // The oldest ticket leaves the front of the queue (D21).
        let ghost q0 = l.pending@;
        l.pending.remove(0);
        assert(l.pending@ =~= q0.drop_first());
        l.head = head;
        self.leases.insert(hid, l);
        let ghost v2 = MgrV {
            leases: v.leases.insert(hid, LeaseV { c: z as nat, pending: lv.pending.drop_first(), ..lv }),
            pend: v.pend.remove(t.id),
            vmap: vmap_after(v, lv, a as nat, z as nat),
            keys: self.keys@,
            pdep: pd,
            ptoks: pt,
            ..v
        };
        let ghost log2 = self.log@@;
        proof {
            assert(finish_rel(v, v2, t.id));
            lemma_finish_inv(v, log0, log2, t.id, v2);
        }
        self.g = Ghost(v2);
        proof {
            assert(self.leases@.dom() =~= v2.leases.dom());
            assert(self.pend@.dom() =~= v2.pend.dom());
            assert forall|h2: u64| #[trigger] self.leases@.contains_key(h2) implies lease_view(self.leases@[h2])
                == v2.leases[h2] && Self::head_ok(v2, self.leases@[h2]) by {
                if h2 != hid {
                    assert(Self::head_ok(v, self.leases@[h2]));
                }
            }
            assert forall|t2: u64| #[trigger] self.pend@.contains_key(t2) implies pend_view(self.pend@[t2]) == v2.pend[t2] by {
            }
            lemma_free_of(v.p, v.refs, v.own);
            // §9.0 (c)
            reveal(lease_ok);
            assert forall|j: int| a <= j < z implies #[trigger] (j / (v.b as int)) < lv.table.len() by {
                lemma_div_bounds(j as nat, v.b);
                if j / (v.b as int) >= lv.table.len() {
                    lemma_mul_mono(lv.table.len(), (j / (v.b as int)) as nat, v.b);
                }
            }
            lemma_vmap_after(v, lv, a as nat, z as nat);
            assert forall|i2: int| #![trigger lv.table[i2]] lo <= i2 < hi implies den(log2, v.b, v.key_of(lv.toks, i2 as nat))
                == (v.ns, lv.toks.subrange(0, (i2 + 1) * v.b)) by {
                lemma_chain_logged_le(log2, v.ns, lv.toks, v.b, i2 as nat, (hi - 1) as nat);
                lemma_block_complete(i2 as nat, z as nat, v.b);
                lemma_chain_denotes(log2, v.ns, lv.toks, v.b, i2 as nat);
            }
        }
        Ok(z)
    }
}


// ---------------------------------------------------------------------------------------------
// D17: committing accepted drafts
// ---------------------------------------------------------------------------------------------

/// The state after committing the first `n` drafts of pending ticket `t` (D17): they join the
/// input `T_h`, and the ticket's input now ends `n` positions later. The frontier is unchanged;
/// `finish_write` then credits `[a, z + n)` over the extended input.
pub open spec fn committed(v: MgrV, t: u64, n: nat) -> MgrV {
    let r = v.pend[t];
    let h = r.lease;
    let l = v.leases[h];
    MgrV {
        leases: v.leases.insert(h, LeaseV { toks: l.toks + r.drafts.subrange(0, n as int), ..l }),
        pend: v.pend.insert(t, PendV { z: r.z + n, drafts: r.drafts.subrange(n as int, r.drafts.len() as int), ..r }),
        ..v
    }
}

/// `Valid` is preserved by committing accepted drafts.
pub proof fn lemma_commit_inv(v: MgrV, log: Log, t: u64, n: nat)
    requires
        inv(v, log),
        v.pend.contains_key(t),
        v.leases[v.pend[t].lease].pending[0] == t,
        n <= v.pend[t].drafts.len(),
    ensures
        inv(committed(v, t, n), log),
{
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    let v2 = committed(v, t, n);
    let r = v.pend[t];
    let h = r.lease;
    let l = v.leases[h];
    let l2 = v2.leases[h];
    assert(pend_ok(v, t));
    assert(lease_ok(v, log, h));
    if n > 0 {
        assert(r.z == l.toks.len());
        // A second ticket would start at z = L and end past L: with drafts, t is alone.
        if l.pending.len() == 2 {
            assert(pend_ok(v, l.pending[1]));
        }
        assert(l.pending.len() == 1);
    }
    assert(l2.toks.len() == l.toks.len() + n);
    // The input only grows: every prefix of the old input is unchanged.
    assert forall|j: int| 0 <= j <= l.toks.len() implies #[trigger] l2.toks.subrange(0, j) == l.toks.subrange(0, j) by {
        assert(l2.toks.subrange(0, j) =~= l.toks.subrange(0, j));
    }
    assert forall|j: int| 0 <= j < l2.c implies (v2.vmap)(#[trigger] slot_of(v2.b, l2.table, j)) == l2.toks.subrange(
        0,
        j + 1,
    ) by {
        assert(l2.toks.subrange(0, j + 1) == l.toks.subrange(0, j + 1));
    }
    assert forall|i: nat| i < l2.table.len() implies #[trigger] blk_ok(v2, log, l2, i) by {
        assert(blk_ok(v, log, l, i));
        if (i + 1) * v.b <= l.c {
            assert(l2.toks.subrange(0, ((i + 1) * v.b) as int) == l.toks.subrange(0, ((i + 1) * v.b) as int));
            lemma_chain_key_prefix(v.seed(), l.toks, l2.toks, v.b, i);
            lemma_chain_logged_prefix(log, v.ns, l.toks, l2.toks, v.b, i);
        }
    }
    assert(lease_ok(v2, log, h));
    assert forall|h2: u64| #[trigger] v2.leases.contains_key(h2) implies lease_ok(v2, log, h2) by {
        if h2 != h {
            assert(lease_ok(v, log, h2));
            let lo = v.leases[h2];
            assert forall|i: int| 0 <= i < lo.pending.len() implies #[trigger] lo.pending[i] != t by {
                assert(v.pend.contains_key(lo.pending[i]));
            }
            lemma_lease_frame(v, v2, log, log, h2);
        }
    }
    assert forall|x: PageId| (x as nat) < v2.p implies #[trigger] page_ok(v2, log, x) by {
        assert(page_ok(v, log, x));
        assert(hold_ok(v, x));
        assert forall|h2: u64| #[trigger] v2.holders[x as int].contains(h2) <==> (v2.leases.contains_key(h2)
            && v2.leases[h2].table.contains(x)) by {
        }
        if v.keys[x as int] is Some {
            lemma_pub_frame(v, v2, log, log, x);
        }
    }
    assert forall|t2: u64| #[trigger] v2.pend.contains_key(t2) implies pend_ok(v2, t2) by {
        if t2 != t {
            assert(pend_ok(v, t2));
            if v.pend[t2].lease != h {
                lemma_pend_frame(v, v2, t2);
            }
        } else {
            let r2 = v2.pend[t];
            if r2.drafts.len() > 0 {
                assert(r.drafts.len() > 0);
            }
            if r2.z < l2.toks.len() {
                assert(r.z < l.toks.len());
                assert(r.drafts.len() == 0);
            }
        }
    }
    lemma_last_frame(v, v2);
}

impl Manager {
    /// D17: commit the first `n` drafts of pending ticket `t`. Not public: the first half of
    /// `finish_write_n`.
    pub(crate) fn commit_drafts(&mut self, t: u64, n: usize)
        requires
            old(self).valid(),
            old(self)@.pend.contains_key(t),
            old(self)@.leases[old(self)@.pend[t].lease].pending[0] == t,
            n <= old(self)@.pend[t].drafts.len(),
        ensures
            final(self).valid(),
            final(self).den_log() == old(self).den_log(),
            final(self)@ == committed(old(self)@, t, n as nat),
            final(self).id == old(self).id,
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        let ghost v = self@;
        let ghost log = self.den_log();
        let ghost hid0 = v.pend[t].lease;
        proof {
            reveal(pend_ok);
            reveal(lease_ok);
            assert(pend_ok(v, t));
            assert(lease_ok(v, log, hid0));
            assert(Self::head_ok(v, self.leases@[hid0]));
            assert(v.pend[t].z + v.pend[t].drafts.len() <= v.leases[hid0].rho);
        }
        let mut pr = self.pend.remove(&t).unwrap();
        let hid = pr.lease;
        let mut l = self.leases.remove(&hid).unwrap();
        let ghost l0 = l;
        let k = pr.drafts.len();
        l.toks.extend_from_slice(vstd::slice::slice_subrange(pr.drafts.as_slice(), 0, n));
        let rest = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(pr.drafts.as_slice(), n, k));
        pr.drafts = rest;
        pr.z = pr.z + n;
        self.leases.insert(hid, l);
        self.pend.insert(t, pr);
        let ghost v2 = committed(v, t, n as nat);
        proof {
            lemma_commit_inv(v, log, t, n as nat);
        }
        self.g = Ghost(v2);
        proof {
            let lv = v.leases[hid];
            assert(self.leases@.dom() =~= v2.leases.dom());
            assert(self.pend@.dom() =~= v2.pend.dom());
            assert forall|h2: u64| #[trigger] self.leases@.contains_key(h2) implies lease_view(self.leases@[h2])
                == v2.leases[h2] && Self::head_ok(v2, self.leases@[h2]) by {
                if h2 != hid {
                    assert(Self::head_ok(v, self.leases@[h2]));
                } else {
                    let lc = self.leases@[h2];
                    assert(lc.toks@ =~= lv.toks + v.pend[t].drafts.subrange(0, n as int));
                    assert(lease_view(lc) == v2.leases[h2]);
                    let q = lc.c as nat / v.b;
                    if q > 0 {
                        lemma_div_bounds(lc.c as nat, v.b);
                        lemma_mul_succ((q - 1) as nat, v.b);
                        assert(lc.toks@.subrange(0, (q * v.b) as int) =~= lv.toks.subrange(0, (q * v.b) as int));
                        lemma_chain_key_prefix(v.seed(), lv.toks, lc.toks@, v.b, (q - 1) as nat);
                    }
                }
            }
            assert forall|t2: u64| #[trigger] self.pend@.contains_key(t2) implies pend_view(self.pend@[t2]) == v2.pend[t2] by {
                if t2 == t {
                    assert(self.pend@[t].drafts@ =~= v.pend[t].drafts.subrange(n as int, k as int));
                }
            }
        }
    }
}

/// C4 with an acceptance count (D17): commit the first `n` drafts, then complete the ticket.
pub open spec fn finish_n_result(
    v: MgrV,
    v2: MgrV,
    log2: Log,
    t: Ticket,
    c: Completion,
    n: usize,
    r: Result<usize, Error>,
) -> bool {
    let live = t.mgr == v.id && v.pend.contains_key(t.id) && c.ticket == t && v.leases[v.pend[t.id].lease].pending[0] == t.id;
    &&& !live ==> r is Err && r->Err_0 == Error::InvalidTicket
    &&& (live && n > v.pend[t.id].drafts.len()) ==> r is Err && r->Err_0 == Error::InvalidArgument
    &&& (live && n <= v.pend[t.id].drafts.len()) ==> r is Ok
    &&& r is Ok ==> live && n <= v.pend[t.id].drafts.len() && finish_result(committed(v, t.id, n as nat), v2, log2, t, c, r)
}

impl Manager {
    /// C4 with an acceptance count `n` (D17): the first `n` drafts of the ticket join `T_h`, and
    /// `[a, z + n)` is credited and published over the extended input.
    pub fn finish_write_n(&mut self, t: Ticket, completion: Completion, n: usize) -> (r: Result<usize, Error>)
        requires
            old(self).valid(),
        ensures
            final(self).valid(),
            old(self).den_log().submap_of(final(self).den_log()),
            r is Err ==> final(self)@ == old(self)@,
            finish_n_result(old(self)@, final(self)@, final(self).den_log(), t, completion, n, r),
    {
        proof {
            self.lemma_valid();
            self.lemma_rep_dom();
        }
        if t.mgr != self.id || completion.ticket.mgr != t.mgr || completion.ticket.id != t.id
            || !self.pend.contains_key(&t.id) || !self.is_head(t.id) {
            return Err(Error::InvalidTicket);
        }
        if n > self.pend.get(&t.id).unwrap().drafts.len() {
            return Err(Error::InvalidArgument);
        }
        self.commit_drafts(t.id, n);
        self.finish_write(t, completion)
    }
}


/// §9.1.4: two different pending tickets never write the same slot, and no pending write slot
/// lies on a page of another lease (in particular, never on a shared or published page).
pub proof fn lemma_pending_disjoint(v: MgrV, log: Log, t1: u64, t2: u64)
    requires
        inv(v, log),
        v.pend.contains_key(t1),
        v.pend.contains_key(t2),
        t1 != t2,
    ensures
        forall|j1: int, j2: int|
            v.pend[t1].a <= j1 < v.pend[t1].z && v.pend[t2].a <= j2 < v.pend[t2].z ==> #[trigger] slot_of(
                v.b,
                v.leases[v.pend[t1].lease].table,
                j1,
            ) != #[trigger] slot_of(v.b, v.leases[v.pend[t2].lease].table, j2),
{
    reveal(pend_ok);
    reveal(lease_ok);
    assert(pend_ok(v, t1));
    assert(pend_ok(v, t2));
    let h1 = v.pend[t1].lease;
    let h2 = v.pend[t2].lease;
    let l1 = v.leases[h1];
    let l2 = v.leases[h2];
    if h1 == h2 {
        // Two tickets of one queue write consecutive, disjoint intervals [a0, z0), [z0, z1) (I9).
        assert(lease_ok(v, log, h1));
        let q = l1.pending;
        let i1 = choose|i: int| 0 <= i < q.len() && q[i] == t1;
        let i2 = choose|i: int| 0 <= i < q.len() && q[i] == t2;
        assert(q.len() == 2);
        let r0 = v.pend[q[0]];
        let r1 = v.pend[q[1]];
        assert(pend_ok(v, q[0]));
        assert(pend_ok(v, q[1]));
        lemma_plan_slots(v, log, h1, r0.a, r1.z);
        assert forall|j1: int, j2: int|
            v.pend[t1].a <= j1 < v.pend[t1].z && v.pend[t2].a <= j2 < v.pend[t2].z implies #[trigger] slot_of(v.b, l1.table, j1)
            != #[trigger] slot_of(v.b, l2.table, j2) by {
            assert(j1 != j2);
        }
        return;
    }
    lemma_plan_slots(v, log, h1, v.pend[t1].a, v.pend[t1].z);
    lemma_plan_slots(v, log, h2, v.pend[t2].a, v.pend[t2].z);
    assert forall|j1: int, j2: int|
        v.pend[t1].a <= j1 < v.pend[t1].z && v.pend[t2].a <= j2 < v.pend[t2].z implies #[trigger] slot_of(v.b, l1.table, j1)
        != #[trigger] slot_of(v.b, l2.table, j2) by {
        assert(0 <= slot_of(v.b, l1.table, j1));
        assert(0 <= slot_of(v.b, l2.table, j2));
        let x1 = l1.table[j1 / (v.b as int)];
        let x2 = l2.table[j2 / (v.b as int)];
        assert(write_page_ok(v, h1, x1));
        if slot_of(v.b, l1.table, j1) == slot_of(v.b, l2.table, j2) {
            lemma_div_bounds(j2 as nat, v.b);
            lemma_write_slot_page(v, l1.table, j1, x2 as int, j2 % (v.b as int));
            assert(l2.table.contains(x2));
        }
    }
}

} // verus!
