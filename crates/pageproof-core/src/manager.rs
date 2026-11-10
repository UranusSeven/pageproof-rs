//! The concrete `Manager`, its abstraction function `view()`, and the refinement invariant.
use vstd::prelude::*;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use crate::spec::*;
use crate::types::*;
use crate::model::*;
use crate::arith::*;
use crate::e8::*;
use crate::idxset::IdxSet;
use crate::index::KeyIndex;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// Process-wide manager-id allocator; ids are never reused, so handles/tickets from one manager
/// are never accepted by another.
exec static NEXT_MGR: AtomicU64 ensures true { AtomicU64::new(0) }

/// Allocates a fresh manager id; `None` once the id space is exhausted (never wraps). Retries a
/// bounded number of times if another thread races the compare-exchange.
fn fresh_mgr_id() -> (r: Option<u64>) {
    let mut tries: u32 = 0;
    while tries < 1024
        decreases 1024 - tries,
    {
        let cur = NEXT_MGR.load(Ordering::SeqCst);
        if cur == u64::MAX {
            return None;
        }
        match NEXT_MGR.compare_exchange(cur, cur + 1, Ordering::SeqCst, Ordering::SeqCst) {
            Ok(_) => return Some(cur),
            Err(_) => {},
        }
        tries += 1;
    }
    None
}

pub struct LeaseC {
    pub toks: Vec<Token>,
    pub table: Vec<PageId>,
    pub c: usize,
    pub pending: Option<u64>,
    /// Chain head: key of the last published complete block, or `Seed(ns)`.
    pub head: Digest,
}

pub struct PendC {
    pub lease: u64,
    pub a: usize,
    pub z: usize,
}

pub struct Manager {
    pub(crate) id: u64,
    pub(crate) p: usize,
    pub(crate) b: usize,
    pub(crate) ns: Vec<u8>,
    pub(crate) seed: Digest,
    pub(crate) leases: HashMap<u64, LeaseC>,
    pub(crate) pend: HashMap<u64, PendC>,
    pub(crate) refs: Vec<u64>,
    pub(crate) keys: Vec<Option<Digest>>,
    pub(crate) free: IdxSet,
    /// v0.3: concrete ownership mask (`U_c`).
    pub(crate) own: Vec<bool>,
    pub(crate) index: KeyIndex,
    pub(crate) next_handle: u64,
    pub(crate) next_ticket: u64,
    pub(crate) log: Tracked<DenLog>,
    pub(crate) g: Ghost<MgrV>,
}

pub open spec fn lease_view(l: LeaseC) -> LeaseV {
    LeaseV { toks: l.toks@, table: l.table@, c: l.c as nat, pending: l.pending }
}

pub open spec fn pend_view(r: PendC) -> PendV {
    PendV { lease: r.lease, a: r.a as nat, z: r.z as nat }
}

impl Manager {
    /// The abstract state.
    pub open(crate) spec fn view(&self) -> MgrV {
        self.g@
    }

    /// The E8 log (ghost), exposed so that `den` can be stated by clients.
    pub open(crate) spec fn den_log(&self) -> Log {
        self.log@@
    }

    /// Chain heads are the key of the last computed full block (or the seed).
    pub open spec fn head_ok(v: MgrV, l: LeaseC) -> bool {
        let q = l.c as nat / v.b;
        &&& q == 0 ==> l.head == v.seed()
        &&& q > 0 ==> l.head == v.key_of(l.toks@, (q - 1) as nat)
    }

    /// Refinement: concrete fields represent `g`.
    pub open(crate) spec fn rep(&self) -> bool {
        let v = self.g@;
        &&& v.id == self.id
        &&& v.p == self.p as nat
        &&& v.b == self.b as nat
        &&& v.ns == self.ns@
        &&& self.seed == v.seed()
        &&& v.refs == self.refs@
        &&& v.keys == self.keys@
        &&& v.own == self.own@
        &&& v.next_handle == self.next_handle
        &&& v.next_ticket == self.next_ticket
        &&& self.leases@.dom() == v.leases.dom()
        &&& forall|h: u64| #[trigger] self.leases@.contains_key(h) ==> lease_view(self.leases@[h]) == v.leases[h]
        &&& forall|h: u64| #[trigger] self.leases@.contains_key(h) ==> Self::head_ok(v, self.leases@[h])
        &&& self.pend@.dom() == v.pend.dom()
        &&& forall|t: u64| #[trigger] self.pend@.contains_key(t) ==> pend_view(self.pend@[t]) == v.pend[t]
        &&& self.free.wf()
        &&& self.free.universe() == v.p
        &&& self.free@ == v.free_set()
        &&& self.index.wf(v.keys)
    }

    /// `Valid(S)` for the concrete manager: refinement + abstract invariant.
    pub open(crate) spec fn valid(&self) -> bool {
        self.rep() && inv(self.g@, self.log@@)
    }

    /// Unfolds `valid` into its two components.
    pub(crate) proof fn lemma_valid(&self)
        requires
            self.valid(),
        ensures
            self.rep(),
            inv(self@, self.den_log()),
    {
    }

    /// Number of key-index buckets (concrete).
    pub closed spec fn index_buckets(&self) -> nat {
        self.index.num_buckets()
    }

    /// Number of concrete lease / pending records.
    pub closed spec fn num_leases(&self) -> nat {
        self.leases@.dom().len()
    }

    pub closed spec fn num_pending(&self) -> nat {
        self.pend@.dom().len()
    }

    /// I11 (bounded metadata, all O(P)): every runtime container's element count is bounded
    /// by the fixed configuration. `refs`, `keys` and the free set have exactly `P` slots.
    pub proof fn lemma_bounded(&self)
        requires
            self.valid(),
        ensures
            self.index_buckets() <= self@.p,
            self.num_leases() <= self@.p,
            self.num_pending() <= self.num_leases(),
            forall|h: u64| #[trigger] self@.leases.contains_key(h) ==> self@.leases[h].table.len() <= self@.p
                && self@.leases[h].toks.len() <= self@.p * self@.b,
            self@.free_set().len() <= self@.p,
    {
        let v = self@;
        lemma_counts_bounded(v, self.log@@);
        assert(v.p <= v.p * v.b) by (nonlinear_arith) requires v.b >= 1;
        self.index.lemma_bounded(v.keys);
        self.free.lemma_bounds();
        assert(self.leases@.dom() == v.leases.dom());
        assert(self.pend@.dom() == v.pend.dom());
    }

    pub fn block_size(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self@.b,
    {
        self.b
    }

    pub fn num_pages(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self@.p,
    {
        self.p
    }

    /// Runtime observation of the bucket count (bounded by `P`, see `lemma_bounded`).
    pub fn index_bucket_count(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self.index_buckets(),
            r as nat <= self@.p,
    {
        proof {
            self.lemma_bounded();
        }
        self.index.bucket_count()
    }

    pub fn free_count(&self) -> (r: usize)
        requires
            self.valid(),
        ensures
            r as nat == self@.free_set().len(),
    {
        self.free.len()
    }
}

// ---------------------------------------------------------------------------------------------
// C0 create
// ---------------------------------------------------------------------------------------------

/// The abstract initial state (every unit owned: the v0.2.1 configuration).
pub open spec fn initial(id: u64, p: nat, b: nat, ns: Seq<u8>) -> MgrV {
    initial_own(id, p, b, ns, true)
}

/// The abstract initial state with every unit owned (`o`) or unowned (`!o`).
pub open spec fn initial_own(id: u64, p: nat, b: nat, ns: Seq<u8>, o: bool) -> MgrV {
    MgrV {
        id,
        p,
        b,
        ns,
        leases: Map::empty(),
        pend: Map::empty(),
        refs: Seq::new(p, |i: int| 0u64),
        keys: Seq::new(p, |i: int| None),
        next_handle: 0,
        next_ticket: 0,
        vmap: |s: int| Seq::empty(),
        holders: Seq::new(p, |i: int| Set::empty()),
        pdep: Seq::new(p, |i: int| 0nat),
        ptoks: Seq::new(p, |i: int| Seq::empty()),
        own: Seq::new(p, |i: int| o),
    }
}

impl Manager {
    /// C0. `create(P, B, Namespace)`: every page owned (v0.2.1).
    pub fn create(p: usize, b: usize, ns: &[u8]) -> (r: Result<Manager, Error>)
        ensures
            r matches Ok(m) ==> {
                &&& m.valid()
                &&& m@ == initial(m@.id, p as nat, b as nat, ns@)
            },
            r matches Err(e) ==> e == Error::ConfigError || e == Error::IdentifierExhausted,
            (p == 0 || b == 0 || (p as nat) * (b as nat) > max_slots() || ns@.len() > u32::MAX) ==> r is Err,
    {
        Self::create_own(p, b, ns, true)
    }

    /// A paged class over `p` units, owning none of them (v0.3, units arrive with slabs).
    pub fn create_empty(p: usize, b: usize, ns: &[u8]) -> (r: Result<Manager, Error>)
        ensures
            r matches Ok(m) ==> {
                &&& m.valid()
                &&& m@ == initial_own(m@.id, p as nat, b as nat, ns@, false)
            },
            r matches Err(e) ==> e == Error::ConfigError || e == Error::IdentifierExhausted,
            (p == 0 || b == 0 || (p as nat) * (b as nat) > max_slots() || ns@.len() > u32::MAX) ==> r is Err,
    {
        Self::create_own(p, b, ns, false)
    }

    fn create_own(p: usize, b: usize, ns: &[u8], o: bool) -> (r: Result<Manager, Error>)
        ensures
            r matches Ok(m) ==> {
                &&& m.valid()
                &&& m@ == initial_own(m@.id, p as nat, b as nat, ns@, o)
            },
            r matches Err(e) ==> e == Error::ConfigError || e == Error::IdentifierExhausted,
            (p == 0 || b == 0 || (p as nat) * (b as nat) > max_slots() || ns@.len() > u32::MAX) ==> r is Err,
    {
        if p == 0 || b == 0 || ns.len() > u32::MAX as usize {
            return Err(Error::ConfigError);
        }
        proof {
            assert((p as nat) * (b as nat) <= u128::MAX) by (nonlinear_arith)
                requires p as nat <= u64::MAX, b as nat <= u64::MAX;
        }
        if (p as u128) * (b as u128) > MAX_SLOTS as u128 {
            return Err(Error::ConfigError);
        }
        let id = match fresh_mgr_id() {
            Some(id) => id,
            None => return Err(Error::IdentifierExhausted),
        };
        let mut nsv: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < ns.len()
            invariant
                0 <= i <= ns@.len(),
                nsv@ == ns@.subrange(0, i as int),
            decreases ns@.len() - i,
        {
            nsv.push(ns[i]);
            i += 1;
            assert(nsv@ =~= ns@.subrange(0, i as int));
        }
        assert(ns@.subrange(0, ns@.len() as int) =~= ns@);
        let tracked mut log = DenLog::new();
        let seed = hash_seed(ns, Tracked(&mut log));
        let refs: Vec<u64> = vec![0u64; p];
        let keys: Vec<Option<Digest>> = vec![None; p];
        let ghost v = initial_own(id, p as nat, b as nat, ns@, o);
        assert(refs@ =~= v.refs);
        assert(keys@ =~= v.keys);
        let own: Vec<bool> = vec![o; p];
        assert(own@ =~= v.own);
        let free = if o { IdxSet::new_full(p) } else { IdxSet::new_empty(p) };
        let index = KeyIndex::new(Ghost(keys@));
        let m = Manager {
            id,
            p,
            b,
            ns: nsv,
            seed,
            leases: HashMap::new(),
            pend: HashMap::new(),
            refs,
            keys,
            free,
            own,
            index,
            next_handle: 0,
            next_ticket: 0,
            log: Tracked(log),
            g: Ghost(v),
        };
        proof {
            vstd::set_lib::range_set_properties::<usize>(0usize, p);
            assert(m.free@ =~= v.free_set());
            assert(m.leases@.dom() =~= v.leases.dom());
            assert(m.pend@.dom() =~= v.pend.dom());
            reveal(page_ok);
            assert forall|x: PageId| (x as nat) < v.p implies #[trigger] page_ok(v, m.log@@, x) by {
                assert(v.holders[x as int] =~= Set::<u64>::empty());
                assert(hold_ok(v, x));
            }
            reveal(last_ok);
        }
        Ok(m)
    }
}

} // verus!
