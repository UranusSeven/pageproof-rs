//! Public types: errors, handles, tickets, views, plans, and the abstract (ghost) state `MgrV`
//! against which every method contract is stated.
use vstd::prelude::*;
use crate::spec::*;

verus! {

pub type PageId = usize;

/// Declared error results (contract §6). Every error path is strongly failure-atomic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    ConfigError,
    InvalidArgument,
    RequestTooLarge,
    NoCapacity,
    IdentifierExhausted,
    InvalidPhase,
    Busy,
    InvalidHandle,
    InvalidTicket,
}

/// Request lease handle, bound to a manager instance and a never-reused id.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Handle {
    pub mgr: u64,
    pub id: u64,
}

/// Execution ticket, bound to a manager instance and a never-reused id.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ticket {
    pub mgr: u64,
    pub id: u64,
}

/// Immutable snapshot of a page table.
pub struct PageTableView {
    pub pages: Vec<PageId>,
}

/// Immutable execution plan returned by `begin_write` (contract §3.4, C3).
pub struct ExecutionPlan {
    pub ticket: Ticket,
    pub handle: Handle,
    /// `T_h[a:z]`
    pub input_ids: Vec<Token>,
    /// `[a, ..., z-1]`
    pub positions: Vec<usize>,
    /// `slot(h, j)` for `j in [a, z)`
    pub write_slots: Vec<usize>,
    /// Page mapping for the context `[0, z)`: logical blocks `0 .. ceil(z/B)`.
    pub page_table: Vec<PageId>,
    pub block_size: usize,
}

/// Read-only view returned by `inspect` (C6).
pub struct RequestView {
    pub len: usize,
    pub computed: usize,
    pub pages: Vec<PageId>,
    pub pending: Option<Ticket>,
    pub block_size: usize,
}

// ---------------------------------------------------------------------------------------------
// Abstract state (§3.2)
// ---------------------------------------------------------------------------------------------

/// `Req[h]`: input `T_h`, page table `M_h`, frontier `c_h`, and `Q_h`, the ids of its pending
/// tickets in issue order (at most one so far).
pub ghost struct LeaseV {
    pub toks: Seq<Token>,
    pub table: Seq<PageId>,
    pub c: nat,
    pub pending: Seq<u64>,
    /// `ρ_h`: the reach, the number of token positions the page table covers (D18).
    pub rho: nat,
}

/// `Pending[t]`: lease, original frontier `a`, interval end `z`.
pub ghost struct PendV {
    pub lease: u64,
    pub a: nat,
    pub z: nat,
    /// The draft tokens fed after the input (D16); empty unless `z = |T_h|`.
    pub drafts: Seq<Token>,
    /// The drafter classes also write proposal rows (D20).
    pub propose: bool,
}

/// Configuration fixed at create and shared by every paged class (I10).
pub ghost struct PCfg {
    /// `μ`: the reservation margin, positions reserved past the planned input (D18).
    pub mu: nat,
    /// `λ`: the maximum number of drafts per ticket (D16).
    pub lam: nat,
    /// `δ`: the ZOS depth (D21).
    pub delta: nat,
    /// Paged classes `[0, ntarget)` are target classes, the rest drafter classes (D20).
    pub ntarget: nat,
}

/// Concrete `PCfg`.
#[derive(Clone, Copy)]
pub struct PCfgC {
    pub mu: usize,
    pub lam: usize,
    pub delta: usize,
    pub ntarget: usize,
}

impl View for PCfgC {
    type V = PCfg;

    open spec fn view(&self) -> PCfg {
        PCfg { mu: self.mu as nat, lam: self.lam as nat, delta: self.delta as nat, ntarget: self.ntarget as nat }
    }
}

/// The configuration of a v0.2.1 manager: no reservation, no drafts, no ZOS.
pub open spec fn v021_cfg() -> PCfg {
    PCfg { mu: 0, lam: 0, delta: 0, ntarget: 1 }
}

/// The abstract manager state. `F` is derived (`free_set`), `Index` is derived from `keys`
/// (`in_index`), `den` is derived from the E8 log (`spec::den`).
pub ghost struct MgrV {
    pub id: u64,
    pub p: nat,
    pub b: nat,
    pub ns: Seq<u8>,
    /// Configuration shared by every paged class of a coordinator (I10).
    pub cfg: PCfg,
    pub leases: Map<u64, LeaseV>,
    pub pend: Map<u64, PendV>,
    pub refs: Seq<u64>,
    pub keys: Seq<Option<Digest>>,
    pub next_handle: u64,
    pub next_ticket: u64,
    /// Ghost `V`: slot -> causal token prefix of the KV stored there (namespace is fixed, I10).
    pub vmap: spec_fn(int) -> Seq<Token>,
    /// Proof bookkeeping: lease ids referencing each page (makes I2 a per-page fact).
    pub holders: Seq<Set<u64>>,
    /// Proof bookkeeping for published pages: block depth `q-1` and covered prefix `tau`.
    pub pdep: Seq<nat>,
    pub ptoks: Seq<Seq<Token>>,
    /// v0.3: unit is in a slab owned by this class (`U_c`). Unowned units have ref 0, no key, and
    /// are not free (I13).
    pub own: Seq<bool>,
}

impl MgrV {
    pub open spec fn seed(self) -> Digest {
        seed_of(self.ns)
    }

    /// `K(h, i)` for an arbitrary token sequence under this manager's namespace and B.
    pub open spec fn key_of(self, toks: Seq<Token>, i: nat) -> Digest {
        chain_key(self.seed(), toks, self.b, i)
    }

    /// `F = { b in U_c | ref[b] = 0 }` (I3).
    pub open spec fn free_set(self) -> Set<PageId> {
        free_of(self.p, self.refs, self.own)
    }

    pub open spec fn is_free(self, b: PageId) -> bool {
        (b as nat) < self.p && self.refs[b as int] == 0 && self.own[b as int]
    }

    /// `Index[K] != {}`.
    pub open spec fn has_hit(self, k: Digest) -> bool {
        exists|b: PageId| #[trigger] crate::index::in_index(self.keys, k, b)
    }

    /// Some candidate for `K` is referenced.
    pub open spec fn has_active_hit(self, k: Digest) -> bool {
        exists|b: PageId| #[trigger] crate::index::in_index(self.keys, k, b) && self.refs[b as int] > 0
    }

    /// I10: configuration is fixed for the manager's lifetime.
    pub open spec fn same_config(self, o: MgrV) -> bool {
        self.id == o.id && self.p == o.p && self.b == o.b && self.ns == o.ns && self.cfg == o.cfg
    }
}

/// `{ b < p | refs[b] == 0 && own[b] }`.
pub open spec fn free_of(p: nat, refs: Seq<u64>, own: Seq<bool>) -> Set<PageId> {
    Set::<PageId>::range(0, p as usize).filter(|b: PageId| refs[b as int] == 0 && own[b as int])
}

pub proof fn lemma_free_of(p: nat, refs: Seq<u64>, own: Seq<bool>)
    requires
        p <= usize::MAX,
    ensures
        forall|b: PageId| #[trigger] free_of(p, refs, own).contains(b) <==> ((b as nat) < p && refs[b as int] == 0
            && own[b as int]),
{
    vstd::set_lib::range_set_properties::<usize>(0usize, p as usize);
}

/// `r0` with every page of `tbl[0..n]` decremented once.
pub open spec fn dec_seq(r0: Seq<u64>, tbl: Seq<PageId>, n: int) -> Seq<u64> {
    Seq::new(r0.len(), |x: int| if tbl.subrange(0, n).contains(x as PageId) { (r0[x] - 1) as u64 } else { r0[x] })
}

/// `r0` with every page of `tbl[0..n]` incremented once.
pub open spec fn inc_seq(r0: Seq<u64>, tbl: Seq<PageId>, n: int) -> Seq<u64> {
    Seq::new(r0.len(), |x: int| if tbl.subrange(0, n).contains(x as PageId) { (r0[x] + 1) as u64 } else { r0[x] })
}

/// Slot address `pg*B + off` (trigger-friendly wrapper).
pub open spec fn sl(b: nat, pg: int, off: int) -> int {
    pg * b + off
}

/// `slot(h, j)` of §3.3 for a page table and position `j`.
pub open spec fn slot_of(b: nat, table: Seq<PageId>, j: int) -> int {
    sl(b, table[j / (b as int)] as int, j % (b as int))
}

/// `m = ceil(L/B)` stated without division: `(m-1)*B < L <= m*B`, `m >= 1`.
pub open spec fn blocks_for(l: nat, b: nat, m: nat) -> bool {
    m >= 1 && (m - 1) * b < l && l <= m * b
}

/// Number of positions `i < k` whose key has an *active* (referenced) candidate: `u` in C1.
pub open spec fn count_active(v: MgrV, toks: Seq<Token>, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        0
    } else {
        count_active(v, toks, (k - 1) as nat) + if v.has_active_hit(v.key_of(toks, (k - 1) as nat)) {
            1nat
        } else {
            0nat
        }
    }
}

/// The longest run of indexed complete-block keys from 0, capped at `cap`.
pub open spec fn is_kcap(v: MgrV, toks: Seq<Token>, cap: nat, k: nat) -> bool {
    &&& k <= cap
    &&& forall|i: nat| i < k ==> v.has_hit(#[trigger] v.key_of(toks, i))
    &&& k < cap ==> !v.has_hit(v.key_of(toks, k))
}

/// `k*` of C1: the longest run of indexed complete-block keys, capped at `m - 1`.
pub open spec fn is_kstar(v: MgrV, toks: Seq<Token>, m: nat, k: nat) -> bool {
    &&& k + 1 <= m
    &&& forall|i: nat| i < k ==> v.has_hit(#[trigger] v.key_of(toks, i))
    &&& k + 1 < m ==> !v.has_hit(v.key_of(toks, k))
}

} // verus!
