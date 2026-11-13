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
    let l = v.leases[h];
    let t = v.next_ticket;
    MgrV {
        leases: v.leases.insert(h, LeaseV { pending: seq![t], ..l }),
        pend: v.pend.insert(t, PendV { lease: h, a: l.c, z: l.c + n }),
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

pub proof fn lemma_begin_inv(v: MgrV, log: Log, h: u64, n: nat)
    requires
        inv(v, log),
        v.leases.contains_key(h),
        v.leases[h].pending.len() == 0,
        0 < n,
        v.leases[h].c + n <= v.leases[h].toks.len(),
        v.next_ticket < u64::MAX,
    ensures
        inv(began(v, h, n), log),
{
    reveal(lease_ok);
    reveal(page_ok);
    reveal(pend_ok);
    let v2 = began(v, h, n);
    let t = v.next_ticket;
    assert(!v.pend.contains_key(t)) by {
        if v.pend.contains_key(t) {
            assert(pend_ok(v, t));
        }
    }
    assert forall|h2: u64| #[trigger] v2.leases.contains_key(h2) implies lease_ok(v2, log, h2) by {
        assert(lease_ok(v, log, h2));
        let l = v2.leases[h2];
        assert forall|i: nat| i < l.table.len() implies #[trigger] blk_ok(v2, log, l, i) by {
            assert(blk_ok(v, log, v.leases[h2], i));
        }
        if h2 != h && l.pending.len() > 0 {
            let t2 = l.pending[0];
            assert(v.pend.contains_key(t2));
            assert(t2 != t);
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
            assert(v.pend[t2].lease != h) by {
                if v.pend[t2].lease == h {
                    assert(v.leases[h].pending == seq![t2]);
                }
            }
        }
    }
}

/// The plan's write pages are exclusive and unpublished; slots are in range and distinct.
proof fn lemma_plan_slots(v: MgrV, log: Log, h: u64, a: nat, z: nat)
    requires
        inv(v, log),
        v.leases.contains_key(h),
        v.leases[h].c == a,
        a < z <= v.leases[h].toks.len(),
    ensures
        forall|j: int|
            a <= j < z ==> {
                &&& 0 <= #[trigger] slot_of(v.b, v.leases[h].table, j) < v.p * v.b
                &&& (j / (v.b as int)) < v.leases[h].table.len()
                &&& write_page_ok(v, h, v.leases[h].table[j / (v.b as int)])
            },
        forall|j1: int, j2: int|
            a <= j1 < z && a <= j2 < z && j1 != j2 ==> #[trigger] slot_of(v.b, v.leases[h].table, j1) != #[trigger] slot_of(
                v.b,
                v.leases[h].table,
                j2,
            ),
{
    reveal(lease_ok);
    let l = v.leases[h];
    assert(lease_ok(v, log, h));
    lemma_cdiv_props(l.toks.len(), v.b);
    assert forall|j: int| a <= j < z implies {
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
        // (i+1)*b > j >= a = c.
        lemma_mul_succ(i as nat, v.b);
        lemma_uncomputed_exclusive(v, log, h, i as nat);
    }
    assert forall|j1: int, j2: int| a <= j1 < z && a <= j2 < z && j1 != j2 implies #[trigger] slot_of(v.b, l.table, j1)
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
        let mut l = self.leases.remove(&h.id).unwrap();
        if l.pending.len() > 0 {
            self.leases.insert(h.id, l);
            proof {
                assert(self.leases@ =~= old(self).leases@);
            }
            return Err(Error::Busy);
        }
        let a = l.c;
        if n == 0 || n > l.toks.len() - a {
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
        let b = self.b;
        proof {
            lemma_plan_slots(v, log, h.id, a as nat, z as nat);
            lemma_cdiv_props(l.toks@.len(), v.b);
            lemma_cdiv_props(z as nat, v.b);
            lemma_cdiv_mono(z as nat, l.toks@.len(), v.b);
        }
        let ghost lv = v.leases[h.id];
        let mut input_ids: Vec<Token> = Vec::new();
        let mut positions: Vec<usize> = Vec::new();
        let mut write_slots: Vec<usize> = Vec::new();
        let mut j = a;
        while j < z
            invariant
                lv == lease_view(l),
                b as nat == v.b,
                b > 0,
                a <= j <= z,
                z <= l.toks@.len(),
                v.p * v.b <= max_slots(),
                input_ids@ == l.toks@.subrange(a as int, j as int),
                positions@.len() == j - a,
                forall|q: int| 0 <= q < j - a ==> #[trigger] positions@[q] as int == a + q,
                write_slots@.len() == j - a,
                forall|q: int| 0 <= q < j - a ==> #[trigger] write_slots@[q] as int == slot_of(v.b, lv.table, a + q),
                forall|jj: int|
                    a <= jj < z ==> {
                        &&& 0 <= #[trigger] slot_of(v.b, lv.table, jj) < v.p * v.b
                        &&& (jj / (v.b as int)) < lv.table.len()
                    },
                forall|i: int| 0 <= i < lv.table.len() ==> (#[trigger] lv.table[i] as nat) < v.p,
            decreases z - j,
        {
            input_ids.push(l.toks[j]);
            positions.push(j);
            proof {
                assert(0 <= slot_of(v.b, lv.table, j as int) < v.p * v.b);
                assert((j as int / (v.b as int)) < lv.table.len());
                lemma_slot_of_props(v.b, v.p, lv.table, j as int);
            }
            let pg = l.table[j / b];
            write_slots.push(pg * b + j % b);
            proof {
                assert(input_ids@ =~= l.toks@.subrange(a as int, j + 1));
            }
            j += 1;
        }
        proof {
            assert(b as nat <= v.p * v.b) by (nonlinear_arith) requires v.p >= 1, b as nat == v.b;
            lemma_cdiv_le(z as nat, v.b, lv.table.len());
        }
        let nb = (z + b - 1) / b;
        let page_table = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(l.table.as_slice(), 0, nb));
        let t = self.next_ticket;
        self.next_ticket = t + 1;
        let mut q: Vec<u64> = Vec::new();
        q.push(t);
        l.pending = q;
        assert(l.pending@ =~= seq![t]);
        self.leases.insert(h.id, l);
        self.pend.insert(t, PendC { lease: h.id, a, z });
        let ghost v2 = began(v, h.id, n as nat);
        proof {
            lemma_begin_inv(v, log, h.id, n as nat);
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
            let lw = v.leases[h.id];
            assert(plan.input_ids@ == lw.toks.subrange(a as int, z as int));
            assert forall|q: int| 0 <= q < n implies (#[trigger] plan.write_slots@[q] as nat) < v.p * v.b by {
                assert(plan.write_slots@[q] as int == slot_of(v.b, lw.table, a + q));
            }
            assert forall|q1: int, q2: int| 0 <= q1 < n && 0 <= q2 < n && q1 != q2 implies #[trigger] plan.write_slots@[q1]
                != #[trigger] plan.write_slots@[q2] by {
                assert(plan.write_slots@[q1] as int == slot_of(v.b, lw.table, a + q1));
                assert(plan.write_slots@[q2] as int == slot_of(v.b, lw.table, a + q2));
            }
            assert forall|q: int| 0 <= q < n implies write_page_ok(v, h.id, #[trigger] lw.table[(a + q) / (v.b as int)]) by {
                let jj = a + q;
                assert(a <= jj < z);
                assert(0 <= slot_of(v.b, lw.table, jj));
            }
            assert(lease_ok(v, log, h.id));
            assert(nb as nat == cdiv(z as nat, v.b));
            assert(page_table@ =~= lw.table.subrange(0, nb as int));
            assert(plan_ok(v, h.id, n as nat, plan));
        }
        Ok((ticket, plan))
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
    &&& v2.leases == v.leases.insert(h, LeaseV { c: r.z, pending: Seq::empty(), ..l })
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
    &&& forall|i: int|
        #![trigger l.table[i]]
        lo <= i < hi ==> v2.keys[l.table[i] as int] == Some(v.key_of(l.toks, i as nat)) && v2.pdep[l.table[i] as int]
            == i && v2.ptoks[l.table[i] as int] == l.toks.subrange(0, (i + 1) * v.b)
    &&& forall|x: int|
        #![trigger v2.keys[x]]
        0 <= x < v.p && (forall|i: int| lo <= i < hi ==> l.table[i] as int != x) ==> v2.keys[x] == v.keys[x]
            && v2.pdep[x] == v.pdep[x] && v2.ptoks[x] == v.ptoks[x]
}

pub open spec fn finish_result(v: MgrV, v2: MgrV, log2: Log, t: Ticket, c: Completion, r: Result<usize, Error>) -> bool {
    let live = t.mgr == v.id && v.pend.contains_key(t.id) && c.ticket == t;
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
            if lo2.pending.len() > 0 {
                let t2 = lo2.pending[0];
                assert(pend_ok(v, t2));
                assert(t2 != t);
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
    // ---- pending
    assert forall|t2: u64| #[trigger] v2.pend.contains_key(t2) implies pend_ok(v2, t2) by {
        assert(pend_ok(v, t2));
        assert(v.pend[t2].lease != h) by {
            if v.pend[t2].lease == h {
                assert(v.leases[h].pending == seq![t2]);
            }
        }
        lemma_pend_frame(v, v2, t2);
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
            || !self.pend.contains_key(&t.id) {
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
        l.pending = Vec::new();
        assert(l.pending@ =~= Seq::<u64>::empty());
        l.head = head;
        self.leases.insert(hid, l);
        let ghost v2 = MgrV {
            leases: v.leases.insert(hid, LeaseV { c: z as nat, pending: Seq::empty(), ..lv }),
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
    assert(h1 != h2);
    let l1 = v.leases[h1];
    let l2 = v.leases[h2];
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
