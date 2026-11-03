//! E8 boundary and canonical byte encoders.
//!
//! `sha256` is the **only** `external_body` function in the verified core. Its specification is
//! exactly the contract's E8 assumption, phrased per manager: the ghost `DenLog` records every
//! input hashed so far, and a fresh hash never collides with a previously recorded input. It does
//! not state that `sha256_spec` is injective (which would be false by pigeonhole).
//!
//! Everything else in this file (the encoders) is verified against `spec.rs` (E7).
use vstd::prelude::*;
use crate::spec::*;

verus! {

/// Ghost record of every SHA-256 input this manager has hashed: digest -> exact input bytes.
pub tracked struct DenLog {
    ghost m: Map<Digest, Seq<u8>>,
}

impl DenLog {
    pub closed spec fn view(self) -> Map<Digest, Seq<u8>> {
        self.m
    }

    pub(crate) proof fn new() -> (tracked l: DenLog)
        ensures
            l@ == Map::<Digest, Seq<u8>>::empty(),
    {
        DenLog { m: Map::empty() }
    }
}

/// TRUSTED (E8). Computes SHA-256 with the `sha2` crate.
///
/// Spec: the result is `sha256_spec(input)`; if this digest was already recorded in the log, it
/// was recorded for this very input (no collision among inputs hashed by this manager); the input
/// is then recorded. Exploiting this to derive `false` requires exhibiting a SHA-256 collision.
#[verifier::external_body]
pub(crate) fn sha256(input: &[u8], Tracked(log): Tracked<&mut DenLog>) -> (d: Digest)
    ensures
        d == sha256_spec(input@),
        old(log)@.contains_key(d) ==> old(log)@[d] == input@,
        final(log)@ == old(log)@.insert(d, input@),
{
    use sha2::Digest as _;
    let out = sha2::Sha256::digest(input);
    let mut d = [0u8; 32];
    d.copy_from_slice(&out);
    d
}

pub fn digest_eq(a: &Digest, b: &Digest) -> (r: bool)
    ensures
        r == (*a == *b),
{
    let mut i: usize = 0;
    while i < 32
        invariant
            0 <= i <= 32,
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases 32 - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    proof {
        lemma_digest_ext(*a, *b);
    }
    true
}

fn push_le32(out: &mut Vec<u8>, x: u32)
    ensures
        final(out)@ == old(out)@ + le32(x),
{
    out.push((x & 0xffu32) as u8);
    out.push(((x >> 8u32) & 0xffu32) as u8);
    out.push(((x >> 16u32) & 0xffu32) as u8);
    out.push(((x >> 24u32) & 0xffu32) as u8);
    assert(final(out)@ =~= old(out)@ + le32(x));
}

fn push_tag(out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + tag(),
{
    // "mg-block-key-v1"
    out.push(109u8);
    out.push(103u8);
    out.push(45u8);
    out.push(98u8);
    out.push(108u8);
    out.push(111u8);
    out.push(99u8);
    out.push(107u8);
    out.push(45u8);
    out.push(107u8);
    out.push(101u8);
    out.push(121u8);
    out.push(45u8);
    out.push(118u8);
    out.push(49u8);
    assert(final(out)@ =~= old(out)@ + tag());
}

fn push_bytes(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost base = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            out@ == base + s@.subrange(0, i as int),
        decreases s@.len() - i,
    {
        out.push(s[i]);
        i += 1;
        assert(out@ =~= base + s@.subrange(0, i as int));
    }
    assert(s@.subrange(0, s@.len() as int) =~= s@);
}

fn push_enc(out: &mut Vec<u8>, s: &[Token])
    ensures
        final(out)@ == old(out)@ + enc(s@),
{
    let ghost base = out@;
    let mut i: usize = 0;
    assert(enc(s@.subrange(0, 0)) =~= Seq::<u8>::empty());
    assert(out@ =~= base + enc(s@.subrange(0, 0)));
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            out@ == base + enc(s@.subrange(0, i as int)),
        decreases s@.len() - i,
    {
        push_le32(out, s[i]);
        proof {
            let pre = s@.subrange(0, i as int);
            assert(s@.subrange(0, i + 1) =~= pre.push(s@[i as int]));
            lemma_enc_push(pre, s@[i as int]);
        }
        i += 1;
        assert(out@ =~= base + enc(s@.subrange(0, i as int)));
    }
    assert(s@.subrange(0, s@.len() as int) =~= s@);
}

/// Canonical seed input `Tag || 0x00 || Canon(ns)`.
pub fn seed_input_bytes(ns: &[u8]) -> (out: Vec<u8>)
    requires
        ns_ok(ns@),
    ensures
        out@ == seed_input(ns@),
{
    let mut out: Vec<u8> = Vec::new();
    push_tag(&mut out);
    out.push(0u8);
    push_le32(&mut out, ns.len() as u32);
    push_bytes(&mut out, ns);
    assert(out@ =~= seed_input(ns@));
    out
}

/// Canonical node input `Tag || 0x01 || parent || Enc(blk)`.
pub fn node_input_bytes(parent: &Digest, blk: &[Token]) -> (out: Vec<u8>)
    ensures
        out@ == node_input(*parent, blk@),
{
    let mut out: Vec<u8> = Vec::new();
    push_tag(&mut out);
    out.push(1u8);
    push_bytes(&mut out, parent.as_slice());
    push_enc(&mut out, blk);
    assert(out@ =~= node_input(*parent, blk@));
    out
}

pub(crate) fn hash_seed(ns: &[u8], Tracked(log): Tracked<&mut DenLog>) -> (d: Digest)
    requires
        ns_ok(ns@),
    ensures
        d == seed_of(ns@),
        old(log)@.contains_key(d) ==> old(log)@[d] == seed_input(ns@),
        final(log)@ == old(log)@.insert(d, seed_input(ns@)),
{
    let bytes = seed_input_bytes(ns);
    sha256(bytes.as_slice(), Tracked(log))
}

pub(crate) fn hash_node(parent: &Digest, blk: &[Token], Tracked(log): Tracked<&mut DenLog>) -> (d: Digest)
    ensures
        d == sha256_spec(node_input(*parent, blk@)),
        old(log)@.contains_key(d) ==> old(log)@[d] == node_input(*parent, blk@),
        final(log)@ == old(log)@.insert(d, node_input(*parent, blk@)),
{
    let bytes = node_input_bytes(parent, blk);
    sha256(bytes.as_slice(), Tracked(log))
}

} // verus!
