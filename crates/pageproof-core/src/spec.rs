//! Specification layer for contract §3.3: canonical encodings (E7), the chained key `K(h,i)`,
//! and the chain lemma relating digest equality to prefix equality under the E8 log.
//!
//! Nothing in this file is trusted: every lemma is proved. The only uninterpreted symbol is
//! `sha256_spec`, whose sole property is supplied by the E8 wrapper in `e8.rs`.
use vstd::prelude::*;

verus! {

pub type Token = u32;

pub type Digest = [u8; 32];

/// The mathematical SHA-256 function. Deliberately uninterpreted: the proof uses no property of
/// it except what the single E8 wrapper (`e8::sha256`) states about recorded inputs.
pub uninterp spec fn sha256_spec(input: Seq<u8>) -> Digest;

// ---------------------------------------------------------------------------------------------
// Canonical encodings (E7)
// ---------------------------------------------------------------------------------------------

/// Scheme version tag, `"mg-block-key-v1"`.
pub open spec fn tag() -> Seq<u8> {
    seq![109u8, 103u8, 45u8, 98u8, 108u8, 111u8, 99u8, 107u8, 45u8, 107u8, 101u8, 121u8, 45u8, 118u8, 49u8]
}

pub open spec fn tag_len() -> nat {
    15
}

/// Little-endian 4-byte encoding of a `u32`.
pub open spec fn le32(x: u32) -> Seq<u8> {
    seq![
        (x & 0xffu32) as u8,
        ((x >> 8u32) & 0xffu32) as u8,
        ((x >> 16u32) & 0xffu32) as u8,
        ((x >> 24u32) & 0xffu32) as u8,
    ]
}

/// `Enc(blk)`: each token as 4-byte little-endian `u32`, fixed-width concatenation.
pub open spec fn enc(s: Seq<Token>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        enc(s.drop_last()) + le32(s.last())
    }
}

/// `Canon(ns) = u32 len || ns_bytes` (v0.2: the namespace is an opaque byte string).
pub open spec fn canon(ns: Seq<u8>) -> Seq<u8> {
    le32(ns.len() as u32) + ns
}

/// Valid namespaces are those whose length is representable in the `u32` length prefix.
pub open spec fn ns_ok(ns: Seq<u8>) -> bool {
    ns.len() <= u32::MAX
}

/// `Tag || 0x00 || Canon(ns)`
pub open spec fn seed_input(ns: Seq<u8>) -> Seq<u8> {
    tag() + seq![0u8] + canon(ns)
}

/// `Tag || 0x01 || parent || Enc(blk)`
pub open spec fn node_input(parent: Digest, blk: Seq<Token>) -> Seq<u8> {
    tag() + seq![1u8] + parent@ + enc(blk)
}

/// `Seed(ns) = H(Tag || 0x00 || Canon(ns))`
pub open spec fn seed_of(ns: Seq<u8>) -> Digest {
    sha256_spec(seed_input(ns))
}

/// Logical block `i` of `toks` with block size `bsz`.
pub open spec fn block(toks: Seq<Token>, bsz: nat, i: nat) -> Seq<Token> {
    toks.subrange((i * bsz) as int, ((i + 1) * bsz) as int)
}

/// `K(h,i)`: the chained key of block `i`. Defined for complete blocks `(i+1)*bsz <= |toks|`.
pub open spec fn chain_key(seed: Digest, toks: Seq<Token>, bsz: nat, i: nat) -> Digest
    decreases i,
{
    sha256_spec(node_input(chain_parent(seed, toks, bsz, i), block(toks, bsz, i)))
}

/// The parent digest used for block `i`: `Seed(ns)` for block 0, else `K(h, i-1)`.
pub open spec fn chain_parent(seed: Digest, toks: Seq<Token>, bsz: nat, i: nat) -> Digest
    decreases i, 0nat,
{
    if i == 0 {
        seed
    } else {
        chain_key(seed, toks, bsz, (i - 1) as nat)
    }
}

/// Every hash on the chain up to and including block `i` has been recorded in the E8 log with its
/// exact canonical input. This is what lets digest equality be read as prefix equality.
pub open spec fn chain_logged(log: Map<Digest, Seq<u8>>, ns: Seq<u8>, toks: Seq<Token>, bsz: nat, i: nat) -> bool
    decreases i,
{
    &&& log.contains_key(chain_key(seed_of(ns), toks, bsz, i))
    &&& log[chain_key(seed_of(ns), toks, bsz, i)] == node_input(
        chain_parent(seed_of(ns), toks, bsz, i),
        block(toks, bsz, i),
    )
    &&& if i == 0 {
        log.contains_key(seed_of(ns)) && log[seed_of(ns)] == seed_input(ns)
    } else {
        chain_logged(log, ns, toks, bsz, (i - 1) as nat)
    }
}

/// `den(K) = (ns, tau)`: `K` is the logged chain key of the full prefix `tau` (|tau| = q*bsz, q>=1).
pub open spec fn denotes(log: Map<Digest, Seq<u8>>, bsz: nat, k: Digest, ns: Seq<u8>, tau: Seq<Token>) -> bool {
    exists|q: nat|
        #![trigger chain_key(seed_of(ns), tau, bsz, q)]
        tau.len() == (q + 1) * bsz && ns_ok(ns) && chain_logged(log, ns, tau, bsz, q) && k == chain_key(
            seed_of(ns),
            tau,
            bsz,
            q,
        )
}

/// The ghost `den` of §3.2 as a function of the E8 log. Well-defined on chain outputs by
/// `lemma_den_unique`; it is never executed.
pub open spec fn den(log: Map<Digest, Seq<u8>>, bsz: nat, k: Digest) -> (Seq<u8>, Seq<Token>) {
    choose|p: (Seq<u8>, Seq<Token>)| denotes(log, bsz, k, p.0, p.1)
}

// ---------------------------------------------------------------------------------------------
// E7 lemmas: encodings are injective / uniquely parseable (no hash involved)
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_le32_inj(x: u32, y: u32)
    requires
        le32(x) == le32(y),
    ensures
        x == y,
{
    assert(le32(x)[0] == le32(y)[0]);
    assert(le32(x)[1] == le32(y)[1]);
    assert(le32(x)[2] == le32(y)[2]);
    assert(le32(x)[3] == le32(y)[3]);
    assert(x == y) by (bit_vector)
        requires
            (x & 0xffu32) as u8 == (y & 0xffu32) as u8,
            ((x >> 8u32) & 0xffu32) as u8 == ((y >> 8u32) & 0xffu32) as u8,
            ((x >> 16u32) & 0xffu32) as u8 == ((y >> 16u32) & 0xffu32) as u8,
            ((x >> 24u32) & 0xffu32) as u8 == ((y >> 24u32) & 0xffu32) as u8,
    ;
}

pub proof fn lemma_enc_len(s: Seq<Token>)
    ensures
        enc(s).len() == 4 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_enc_len(s.drop_last());
    }
}

pub proof fn lemma_enc_inj(a: Seq<Token>, b: Seq<Token>)
    requires
        enc(a) == enc(b),
    ensures
        a == b,
    decreases a.len(),
{
    lemma_enc_len(a);
    lemma_enc_len(b);
    assert(a.len() == b.len());
    if a.len() == 0 {
        assert(a =~= b);
    } else {
        let n = a.len();
        let ea = enc(a.drop_last());
        let eb = enc(b.drop_last());
        lemma_enc_len(a.drop_last());
        lemma_enc_len(b.drop_last());
        assert(enc(a) == ea + le32(a.last()));
        assert(enc(b) == eb + le32(b.last()));
        let cut = (4 * (n - 1)) as int;
        assert(ea =~= enc(a).subrange(0, cut));
        assert(eb =~= enc(b).subrange(0, cut));
        assert(le32(a.last()) =~= enc(a).subrange(cut, enc(a).len() as int));
        assert(le32(b.last()) =~= enc(b).subrange(cut, enc(b).len() as int));
        lemma_enc_inj(a.drop_last(), b.drop_last());
        lemma_le32_inj(a.last(), b.last());
        assert(a =~= a.drop_last().push(a.last()));
        assert(b =~= b.drop_last().push(b.last()));
    }
}

/// `enc` distributes over concatenation (used to show prefix-block decomposition).
pub proof fn lemma_enc_push(s: Seq<Token>, x: Token)
    ensures
        enc(s.push(x)) == enc(s) + le32(x),
{
    assert(s.push(x).drop_last() =~= s);
}

pub proof fn lemma_digest_ext(p: Digest, q: Digest)
    requires
        p@ == q@,
    ensures
        p == q,
{
    assert(forall|i: int| 0 <= i < 32 ==> p@[i] == q@[i]);
    assert(forall|i: int| 0 <= i < 32 ==> #[trigger] p[i] == q[i]);
    assert(p =~= q);
}

pub proof fn lemma_node_input_inj(p: Digest, x: Seq<Token>, q: Digest, y: Seq<Token>)
    requires
        node_input(p, x) == node_input(q, y),
    ensures
        p == q,
        x == y,
{
    let a = node_input(p, x);
    let b = node_input(q, y);
    assert(p@.len() == 32);
    assert(q@.len() == 32);
    assert(p@ =~= a.subrange(16, 48));
    assert(q@ =~= b.subrange(16, 48));
    lemma_digest_ext(p, q);
    assert(enc(x) =~= a.subrange(48, a.len() as int));
    assert(enc(y) =~= b.subrange(48, b.len() as int));
    lemma_enc_inj(x, y);
}

pub proof fn lemma_seed_input_inj(a: Seq<u8>, b: Seq<u8>)
    requires
        seed_input(a) == seed_input(b),
    ensures
        a == b,
{
    let sa = seed_input(a);
    let sb = seed_input(b);
    assert(a =~= sa.subrange(20, sa.len() as int));
    assert(b =~= sb.subrange(20, sb.len() as int));
}

/// Domain separation: a seed input is never a node input (byte 15 is 0x00 vs 0x01).
pub proof fn lemma_seed_ne_node(ns: Seq<u8>, p: Digest, x: Seq<Token>)
    ensures
        seed_input(ns) != node_input(p, x),
{
    assert(seed_input(ns)[15] == 0u8);
    assert(node_input(p, x)[15] == 1u8);
}

// ---------------------------------------------------------------------------------------------
// Chain lemmas
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_block_prefix(toks: Seq<Token>, bsz: nat, i: nat)
    requires
        bsz > 0,
        (i + 1) * bsz <= toks.len(),
    ensures
        toks.subrange(0, ((i + 1) * bsz) as int) =~= toks.subrange(0, (i * bsz) as int) + block(toks, bsz, i),
{
    assert((i + 1) * bsz == i * bsz + bsz) by (nonlinear_arith);
}

/// Chain lemma (§3.3) under E8: equal logged chain keys denote equal (ns, depth, prefix).
pub proof fn lemma_chain_inj(
    log: Map<Digest, Seq<u8>>,
    bsz: nat,
    ns1: Seq<u8>,
    t1: Seq<Token>,
    i1: nat,
    ns2: Seq<u8>,
    t2: Seq<Token>,
    i2: nat,
)
    requires
        bsz > 0,
        (i1 + 1) * bsz <= t1.len(),
        (i2 + 1) * bsz <= t2.len(),
        chain_logged(log, ns1, t1, bsz, i1),
        chain_logged(log, ns2, t2, bsz, i2),
        chain_key(seed_of(ns1), t1, bsz, i1) == chain_key(seed_of(ns2), t2, bsz, i2),
    ensures
        i1 == i2,
        ns1 == ns2,
        t1.subrange(0, ((i1 + 1) * bsz) as int) == t2.subrange(0, ((i2 + 1) * bsz) as int),
    decreases i1,
{
    let k = chain_key(seed_of(ns1), t1, bsz, i1);
    let p1 = chain_parent(seed_of(ns1), t1, bsz, i1);
    let p2 = chain_parent(seed_of(ns2), t2, bsz, i2);
    lemma_node_input_inj(p1, block(t1, bsz, i1), p2, block(t2, bsz, i2));
    assert(block(t1, bsz, i1) == block(t2, bsz, i2));
    assert(p1 == p2);
    if i1 == 0 && i2 == 0 {
        lemma_seed_input_inj(ns1, ns2);
        assert(bsz == 1 * bsz);
        assert(t1.subrange(0, bsz as int) =~= block(t1, bsz, 0));
        assert(t2.subrange(0, bsz as int) =~= block(t2, bsz, 0));
    } else if i1 == 0 {
        // seed_of(ns1) == K(t2, i2-1): the log maps one digest to both a seed and a node input.
        let j = (i2 - 1) as nat;
        assert(log[seed_of(ns1)] == seed_input(ns1));
        lemma_chain_logged_head(log, ns2, t2, bsz, j);
        lemma_seed_ne_node(ns1, chain_parent(seed_of(ns2), t2, bsz, j), block(t2, bsz, j));
    } else if i2 == 0 {
        let j = (i1 - 1) as nat;
        assert(log[seed_of(ns2)] == seed_input(ns2));
        lemma_chain_logged_head(log, ns1, t1, bsz, j);
        lemma_seed_ne_node(ns2, chain_parent(seed_of(ns1), t1, bsz, j), block(t1, bsz, j));
    } else {
        let j1 = (i1 - 1) as nat;
        let j2 = (i2 - 1) as nat;
        assert((j1 + 1) * bsz <= t1.len()) by (nonlinear_arith)
            requires (i1 + 1) * bsz <= t1.len(), j1 + 1 == i1;
        assert((j2 + 1) * bsz <= t2.len()) by (nonlinear_arith)
            requires (i2 + 1) * bsz <= t2.len(), j2 + 1 == i2;
        lemma_chain_inj(log, bsz, ns1, t1, j1, ns2, t2, j2);
        lemma_block_prefix(t1, bsz, i1);
        lemma_block_prefix(t2, bsz, i2);
    }
}

pub proof fn lemma_chain_logged_head(log: Map<Digest, Seq<u8>>, ns: Seq<u8>, toks: Seq<Token>, bsz: nat, i: nat)
    requires
        chain_logged(log, ns, toks, bsz, i),
    ensures
        log.contains_key(chain_key(seed_of(ns), toks, bsz, i)),
        log[chain_key(seed_of(ns), toks, bsz, i)] == node_input(
            chain_parent(seed_of(ns), toks, bsz, i),
            block(toks, bsz, i),
        ),
{
}

/// Logging is monotone: extending the log preserves every logged chain.
pub proof fn lemma_chain_logged_mono(
    log: Map<Digest, Seq<u8>>,
    log2: Map<Digest, Seq<u8>>,
    ns: Seq<u8>,
    toks: Seq<Token>,
    bsz: nat,
    i: nat,
)
    requires
        chain_logged(log, ns, toks, bsz, i),
        log.submap_of(log2),
    ensures
        chain_logged(log2, ns, toks, bsz, i),
    decreases i,
{
    let k = chain_key(seed_of(ns), toks, bsz, i);
    assert(log2.contains_key(k) && log2[k] == log[k]);
    if i > 0 {
        lemma_chain_logged_mono(log, log2, ns, toks, bsz, (i - 1) as nat);
    } else {
        assert(log2.contains_key(seed_of(ns)) && log2[seed_of(ns)] == log[seed_of(ns)]);
    }
}

/// Keys depend only on the prefix they cover.
pub proof fn lemma_chain_key_prefix(seed: Digest, toks: Seq<Token>, other: Seq<Token>, bsz: nat, i: nat)
    requires
        bsz > 0,
        (i + 1) * bsz <= toks.len(),
        (i + 1) * bsz <= other.len(),
        toks.subrange(0, ((i + 1) * bsz) as int) == other.subrange(0, ((i + 1) * bsz) as int),
    ensures
        chain_key(seed, toks, bsz, i) == chain_key(seed, other, bsz, i),
        chain_parent(seed, toks, bsz, i) == chain_parent(seed, other, bsz, i),
        block(toks, bsz, i) == block(other, bsz, i),
    decreases i,
{
    let n = ((i + 1) * bsz) as int;
    assert(i * bsz <= (i + 1) * bsz) by (nonlinear_arith);
    assert(block(toks, bsz, i) =~= toks.subrange(0, n).subrange((i * bsz) as int, n));
    assert(block(other, bsz, i) =~= other.subrange(0, n).subrange((i * bsz) as int, n));
    if i > 0 {
        let j = (i - 1) as nat;
        let m = ((j + 1) * bsz) as int;
        assert((j + 1) * bsz <= (i + 1) * bsz) by (nonlinear_arith)
            requires j + 1 == i;
        assert(toks.subrange(0, m) =~= toks.subrange(0, n).subrange(0, m));
        assert(other.subrange(0, m) =~= other.subrange(0, n).subrange(0, m));
        lemma_chain_key_prefix(seed, toks, other, bsz, j);
    }
}

pub proof fn lemma_chain_logged_prefix(
    log: Map<Digest, Seq<u8>>,
    ns: Seq<u8>,
    toks: Seq<Token>,
    other: Seq<Token>,
    bsz: nat,
    i: nat,
)
    requires
        bsz > 0,
        (i + 1) * bsz <= toks.len(),
        (i + 1) * bsz <= other.len(),
        toks.subrange(0, ((i + 1) * bsz) as int) == other.subrange(0, ((i + 1) * bsz) as int),
        chain_logged(log, ns, toks, bsz, i),
    ensures
        chain_logged(log, ns, other, bsz, i),
    decreases i,
{
    lemma_chain_key_prefix(seed_of(ns), toks, other, bsz, i);
    if i > 0 {
        let j = (i - 1) as nat;
        let n = ((i + 1) * bsz) as int;
        let m = ((j + 1) * bsz) as int;
        assert((j + 1) * bsz <= (i + 1) * bsz) by (nonlinear_arith)
            requires j + 1 == i;
        assert(toks.subrange(0, m) =~= toks.subrange(0, n).subrange(0, m));
        assert(other.subrange(0, m) =~= other.subrange(0, n).subrange(0, m));
        lemma_chain_logged_prefix(log, ns, toks, other, bsz, j);
    }
}

/// `den` is well defined on logged chain outputs: any witness is *the* value of `den`.
pub proof fn lemma_den_unique(log: Map<Digest, Seq<u8>>, bsz: nat, k: Digest, ns: Seq<u8>, tau: Seq<Token>)
    requires
        bsz > 0,
        denotes(log, bsz, k, ns, tau),
    ensures
        den(log, bsz, k) == (ns, tau),
{
    let w = (ns, tau);
    assert(denotes(log, bsz, k, w.0, w.1));
    let p = den(log, bsz, k);
    assert(denotes(log, bsz, k, p.0, p.1));
    let q1 = choose|q: nat|
        #![trigger chain_key(seed_of(ns), tau, bsz, q)]
        tau.len() == (q + 1) * bsz && ns_ok(ns) && chain_logged(log, ns, tau, bsz, q) && k == chain_key(
            seed_of(ns),
            tau,
            bsz,
            q,
        );
    let q2 = choose|q: nat|
        #![trigger chain_key(seed_of(p.0), p.1, bsz, q)]
        p.1.len() == (q + 1) * bsz && ns_ok(p.0) && chain_logged(log, p.0, p.1, bsz, q) && k == chain_key(
            seed_of(p.0),
            p.1,
            bsz,
            q,
        );
    lemma_chain_inj(log, bsz, ns, tau, q1, p.0, p.1, q2);
    assert(tau =~= tau.subrange(0, ((q1 + 1) * bsz) as int));
    assert(p.1 =~= p.1.subrange(0, ((q2 + 1) * bsz) as int));
}

/// A logged chain key of `toks` at block `i` denotes `(ns, toks[0:(i+1)*bsz])`.
pub proof fn lemma_chain_denotes(log: Map<Digest, Seq<u8>>, ns: Seq<u8>, toks: Seq<Token>, bsz: nat, i: nat)
    requires
        bsz > 0,
        ns_ok(ns),
        (i + 1) * bsz <= toks.len(),
        chain_logged(log, ns, toks, bsz, i),
    ensures
        denotes(
            log,
            bsz,
            chain_key(seed_of(ns), toks, bsz, i),
            ns,
            toks.subrange(0, ((i + 1) * bsz) as int),
        ),
        den(log, bsz, chain_key(seed_of(ns), toks, bsz, i)) == (ns, toks.subrange(0, ((i + 1) * bsz) as int)),
{
    let tau = toks.subrange(0, ((i + 1) * bsz) as int);
    assert(tau.subrange(0, ((i + 1) * bsz) as int) =~= toks.subrange(0, ((i + 1) * bsz) as int));
    lemma_chain_logged_prefix(log, ns, toks, tau, bsz, i);
    lemma_chain_key_prefix(seed_of(ns), toks, tau, bsz, i);
    assert(tau.len() == (i + 1) * bsz && ns_ok(ns) && chain_logged(log, ns, tau, bsz, i) && chain_key(
        seed_of(ns),
        toks,
        bsz,
        i,
    ) == chain_key(seed_of(ns), tau, bsz, i));
    lemma_den_unique(log, bsz, chain_key(seed_of(ns), toks, bsz, i), ns, tau);
}

} // verus!
