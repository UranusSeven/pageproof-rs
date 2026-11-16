//! Randomised runtime tests that contract §9.2 planned for v0.5 and v0.6: ZOS depth 1 against
//! depth 0, and ZOS with speculation against plain decoding. `coord_edge_cases.rs` checks the §7
//! rows one scenario at a time; this file compares whole runs over random request mixes.
//!
//! A run drives the verified `Coordinator` with three simulated parts:
//!
//! - A fake model (`Model`). It is a pure function of the token prefix, so cached KV is reusable.
//!   Every value it computes depends on the whole prefix, so one wrong slot anywhere changes what it
//!   samples.
//! - A device (`Run::execute`). It keeps the KV of every paged class and the state of every state
//!   class in simulated slots. It runs a lease's tickets in issue order (E13(1)), resolves a
//!   continuation's start, input and drafts from its producer's outputs (E13(2)), and reads and
//!   writes only the slots its plan lists (E5). Before each ticket it checks that every slot the
//!   ticket reads holds the KV of the lease's tokens (§9.0 (b)), and that the state slot holds the
//!   state after them (I15, E11).
//! - A scheduler. It admits, plans, processes completions and preempts in a random order, and it
//!   learns a sampled token only from the completion of the ticket that sampled it.
//!
//! After every step the run checks the bounds `computed <= len <= reach` and that no unit a pending
//! ticket may write is in another lease's tables. Every committed token is compared with plain
//! greedy decoding, every release snapshot with the scheduler's copy of `T_h`, and right after each
//! final release a probe attach checks which blocks of the snapshot were published.
//!
//! The arenas are large enough that capacity rarely runs out, except in the configurations named
//! "tight". There, NoCapacity makes a request wait (attach), skips the pipelined step
//! (extend_deferred), or preempts the lease (extend).

use std::collections::{HashMap, VecDeque};

use pageproof_core::coord::Coordinator;
use pageproof_core::coord_attach::LeaseView;
use pageproof_core::coord_ops::{CoordCompletion, CoordPlan, Drafts};
use pageproof_core::types::{Error, Handle, Ticket};

const NS: &[u8] = b"dummy-v0.6";
/// Bytes per slab and token slots per page, for every configuration.
const SLAB: usize = 64;
const B: usize = 4;
/// The fake model samples EOS now and then; ordinary tokens are `2..2 + VOCAB`.
const EOS: u32 = 1;
const VOCAB: u64 = 40;
const EOS_EVERY: u64 = 11;
/// The last token of a probe. attach never reports the last block as cached, so a probe of
/// `T ++ [SENTINEL]` can report every complete block of `T`.
const SENTINEL: u32 = 3;
/// What a simulated slot holds before anything is written to it.
const UNWRITTEN: u64 = 0;
const MAX_TICKS: usize = 200_000;

/// Returns `Err` with the message when the condition fails. Messages start with the check's tag
/// (`[kv]`, `[stream]`, ...).
macro_rules! ensure {
    ($cond:expr, $($fmt:tt)+) => {
        if !$cond {
            return Err(format!($($fmt)+));
        }
    };
}

/// An unexpected coordinator error fails the run.
fn ck<T>(r: Result<T, Error>, what: &str) -> Result<T, String> {
    r.map_err(|e| format!("[coord] {what} returned {e:?}"))
}

// ---------------------------------------------------------------------------------------------
// Hashing and randomness
// ---------------------------------------------------------------------------------------------

/// splitmix64's finaliser over `a ^ rotl(b·φ)`.
fn mix(a: u64, b: u64) -> u64 {
    let mut z = (a ^ b.wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(29)).wrapping_add(0x6A09_E667_F3BC_C909);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(mix(seed, 0x5EED))
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        mix(self.0, 1)
    }

    /// Uniform in `[0, n)`.
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    /// Uniform in `[lo, hi]`.
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + self.below(hi - lo + 1)
    }

    fn chance(&mut self, pct: u32) -> bool {
        self.below(100) < pct as usize
    }
}

// ---------------------------------------------------------------------------------------------
// The fake model
// ---------------------------------------------------------------------------------------------

/// The fake model of a configuration with `nt` target paged classes and `ns` state classes.
/// Position j of a prefix has:
///
/// - the KV `kv_j = mix(mix(att_{j-1}, tok_j), j)`: its token, its position and the hidden state
///   of everything before it, with `att_{-1} = ATT0`;
/// - in paged class c, the slot content `content(kv_j, c)`; a drafter class stores a projection of
///   the target's hidden state at j, as an MTP drafter does (E12);
/// - the attention output `att_j`, which folds what every target class holds at j into `att_{j-1}`;
/// - the recurrent state `st_j = mix(st_{j-1}, kv_j)`, with `st_{-1} = ST0`;
/// - the token sampled after it, a hash of `att_j` (and `st_j` with a state class).
///
/// Drafter classes do not change what the target samples, so a configuration without its drafter
/// classes is the same model.
#[derive(Clone, Copy)]
struct Model {
    nt: usize,
    ns: usize,
}

const ATT0: u64 = 0xA77E_0000_0000_0001;
const ST0: u64 = 0x57A7_E000_0000_0001;

impl Model {
    fn kv(att: u64, tok: u32, pos: usize) -> u64 {
        mix(mix(att, u64::from(tok)), pos as u64)
    }

    fn content(kv: u64, c: usize) -> u64 {
        mix(kv, 0xC1A5_5000 + c as u64)
    }

    fn state_content(st: u64, s: usize) -> u64 {
        mix(st, 0x57A7_E000 + s as u64)
    }

    fn attend(&self, att: u64, kv: u64) -> u64 {
        (0..self.nt).fold(att, |a, c| mix(a, Self::content(kv, c)))
    }

    fn sample(&self, att: u64, st: u64) -> u32 {
        let o = if self.ns > 0 { mix(att, st) } else { mix(att, 0) };
        if o % EOS_EVERY == 0 {
            EOS
        } else {
            2 + ((o >> 20) % VOCAB) as u32
        }
    }
}

/// The model's state after a prefix: what the next position needs.
#[derive(Clone, Copy)]
struct Chain {
    att: u64,
    st: u64,
    pos: usize,
}

impl Chain {
    fn start() -> Chain {
        Chain { att: ATT0, st: ST0, pos: 0 }
    }

    /// Feeds the token at position `pos`; returns its KV and the token the model samples after it.
    fn feed(&mut self, m: &Model, tok: u32) -> (u64, u32) {
        let kv = Model::kv(self.att, tok, self.pos);
        self.att = m.attend(self.att, kv);
        self.st = mix(self.st, kv);
        self.pos += 1;
        (kv, m.sample(self.att, self.st))
    }
}

fn chain_over(m: &Model, toks: &[u32]) -> Chain {
    let mut ch = Chain::start();
    for &t in toks {
        ch.feed(m, t);
    }
    ch
}

/// Plain greedy decoding of `prompt`, up to and including an EOS, or `max_tokens` tokens.
fn plain_decoding(m: &Model, prompt: &[u32], max_tokens: usize) -> Vec<u32> {
    let mut ch = Chain::start();
    let mut next = 0;
    for &t in prompt {
        next = ch.feed(m, t).1;
    }
    let mut out = Vec::new();
    loop {
        out.push(next);
        if next == EOS || out.len() == max_tokens {
            return out;
        }
        next = ch.feed(m, next).1;
    }
}

/// The drafter: `k` drafts that follow the token `first`, which goes at position `ch.pos`. Each is
/// the model's greedy token, replaced by a wrong one with probability `noise` percent. The greedy
/// sampler accepts a draft exactly when it equals the model's token, so clean drafts are always
/// accepted and noisy ones are partly rejected.
fn draft(m: &Model, mut ch: Chain, first: u32, k: usize, noise: u32, rng: &mut Rng) -> Vec<u32> {
    let mut out = Vec::with_capacity(k);
    let mut tok = first;
    for _ in 0..k {
        let next = ch.feed(m, tok).1;
        tok = if rng.chance(noise) { corrupt(next, rng) } else { next };
        out.push(tok);
    }
    out
}

/// An ordinary token other than `t`.
fn corrupt(t: u32, rng: &mut Rng) -> u32 {
    let base = u64::from(t.max(2) - 2);
    2 + ((base + 1 + rng.below(VOCAB as usize - 1) as u64) % VOCAB) as u32
}

// ---------------------------------------------------------------------------------------------
// Request mixes and configurations
// ---------------------------------------------------------------------------------------------

#[derive(Clone)]
struct ReqSpec {
    prompt: Vec<u32>,
    max_tokens: usize,
    /// The drafter's noise for this request, in percent per draft; 0 is a clean drafter.
    noise: u32,
}

/// A random mix: most prompts start with one of three shared prefixes of whole blocks, so attach
/// hits pages that other leases published, some of them active. A token unique to each request
/// follows, so no two requests share a block after the shared prefix, and a probe of one request
/// can only hit its own blocks there.
fn gen_mix(seed: u64, nreq: usize) -> Vec<ReqSpec> {
    let mut rng = Rng::new(seed.wrapping_mul(7919).wrapping_add(17));
    let tok = |rng: &mut Rng| 2 + rng.below(VOCAB as usize) as u32;
    let prefixes: Vec<Vec<u32>> = (0..3)
        .map(|_| {
            let n = B * rng.range(1, 3);
            (0..n).map(|_| tok(&mut rng)).collect()
        })
        .collect();
    (0..nreq)
        .map(|i| {
            let mut prompt = if rng.chance(70) { prefixes[rng.below(3)].clone() } else { Vec::new() };
            prompt.push(1000 + i as u32);
            for _ in 0..rng.below(7) {
                prompt.push(tok(&mut rng));
            }
            let max_tokens = rng.range(1, 18);
            let noise = if rng.chance(40) { 0 } else { rng.range(15, 60) as u32 };
            ReqSpec { prompt, max_tokens, noise }
        })
        .collect()
}

#[derive(Clone)]
struct Cfg {
    name: &'static str,
    nslab: usize,
    /// Unit sizes of the target paged classes, the drafter classes and the state classes.
    pu: Vec<usize>,
    du: Vec<usize>,
    su: Vec<usize>,
    lam: usize,
    delta: usize,
    /// Leases attached at once.
    max_live: usize,
    /// Chance, in percent, that the scheduler plans a lease's next step while its newest step is in
    /// flight, whenever it looks at the lease.
    pipeline: u32,
    nreq: usize,
}

impl Cfg {
    /// A configuration with `δ = 1`.
    fn new(name: &'static str, nslab: usize, pu: &[usize], du: &[usize], su: &[usize], lam: usize) -> Cfg {
        Cfg {
            name,
            nslab,
            pu: pu.to_vec(),
            du: du.to_vec(),
            su: su.to_vec(),
            lam,
            delta: 1,
            max_live: 4,
            pipeline: 70,
            nreq: 12,
        }
    }

    /// D18: `μ = (δ + 1)·λ`, plus `λ` with drafter classes.
    fn mu(&self) -> usize {
        (self.delta + 1) * self.lam + if self.du.is_empty() { 0 } else { self.lam }
    }

    fn model(&self) -> Model {
        Model { nt: self.pu.len(), ns: self.su.len() }
    }

    fn depth(&self, delta: usize) -> Cfg {
        Cfg { delta, ..self.clone() }
    }

    /// Plain decoding of the same model: `λ = 0`, `δ = 0` and no drafter class.
    fn plain(&self) -> Cfg {
        Cfg { lam: 0, delta: 0, du: Vec::new(), ..self.clone() }
    }
}

// ---------------------------------------------------------------------------------------------
// A run
// ---------------------------------------------------------------------------------------------

/// What `inspect` reports about a lease, in a comparable form.
#[derive(Debug, Clone, PartialEq)]
struct View {
    len: usize,
    computed: usize,
    reach: usize,
    planned: usize,
    slack: usize,
    deferred: bool,
    stopped: bool,
    queue: Vec<Ticket>,
    tables: Vec<Vec<usize>>,
    slots: Vec<usize>,
}

/// The fields of a `CoordPlan` that the device and the checks use.
#[derive(Clone)]
struct PlanInfo {
    lo: usize,
    slack: usize,
    l: usize,
    k: usize,
    propose: bool,
    producer: Option<Ticket>,
    input_ids: Vec<u32>,
    write_slots: Vec<Vec<usize>>,
    page_tables: Vec<Vec<usize>>,
    state_slots: Vec<usize>,
    init: bool,
}

impl From<CoordPlan> for PlanInfo {
    fn from(p: CoordPlan) -> PlanInfo {
        PlanInfo {
            lo: p.lo,
            slack: p.slack,
            l: p.num_inputs,
            k: p.num_drafts,
            propose: p.propose,
            producer: p.producer,
            input_ids: p.input_ids,
            write_slots: p.write_slots,
            page_tables: p.page_tables,
            state_slots: p.state_slots,
            init: p.init,
        }
    }
}

/// What the device did for a ticket. The host reads it only when it processes the completion; a
/// continuation reads its producer's on the device.
#[derive(Clone)]
struct DevOut {
    /// The acceptance count the device used, the bonus token it sampled after the accepted drafts,
    /// the drafts it fed, and the drafter's proposal after the bonus (D20).
    n: usize,
    bonus: Option<u32>,
    drafts: Vec<u32>,
    proposals: Vec<u32>,
}

struct Issued {
    t: Ticket,
    plan: PlanInfo,
    /// The input reaches the end of the planned input, so the ticket samples a token.
    samples: bool,
    /// extend_deferred made this ticket the producer of the deferred position (`X_h`, D22).
    heads_x: bool,
    /// An older ticket of the lease completed with stop (D25).
    orphan: bool,
    dev: Option<DevOut>,
}

/// An attached lease: the scheduler's side and the device's side.
struct Live {
    rid: usize,
    h: Handle,
    /// The scheduler's copy of `T_h`.
    host_t: Vec<u32>,
    /// Pending tickets in issue order (indices into `Run::issued`).
    queue: VecDeque<usize>,
    /// A sampled token that is not in `T_h`; the scheduler appends it with extend before planning.
    held: Option<u32>,
    /// The proposal a completion handed to the caller, for the next verify's host-known drafts.
    held_drafts: Vec<u32>,
    stopped: bool,
    /// The device's tokens: `T_h`, then what the device has computed or sampled past it.
    seq: Vec<u32>,
    /// Where the next window starts: the end of the last executed ticket's input and accepted drafts.
    end: usize,
    /// Issued tickets the device has not run yet, and the ones it has run, in issue order.
    dev_pending: VecDeque<usize>,
    dev_done: Vec<usize>,
}

struct Req {
    spec: ReqSpec,
    /// Plain greedy decoding of the prompt.
    expect: Vec<u32>,
    /// The tokens to attach with: the prompt, or after a preemption everything committed so far.
    resume: Vec<u32>,
    /// The tokens committed so far, the request's output.
    out: Vec<u32>,
    finished: bool,
    /// The final token, when the scheduler keeps it and it is not in `T_h`.
    kept: Option<u32>,
    /// The final EOS entered `T_h` through `X_h` (the v0.5 EOS row of §7).
    eos_bound: bool,
    done: Option<ReqOut>,
}

/// A request's result.
#[derive(Clone, Debug)]
struct ReqOut {
    out: Vec<u32>,
    /// What the final release returned.
    snapshot: Vec<u32>,
    kept: Option<u32>,
    eos_bound: bool,
    /// The cached tokens a later attach of `snapshot ++ [SENTINEL]` reported, if that attach fit.
    probe: Option<usize>,
}

/// Defines `Stats`, a set of counters, and `Stats::add`.
macro_rules! stats {
    ($($f:ident),* $(,)?) => {
        #[derive(Default, Debug, Clone, Copy)]
        struct Stats {
            $($f: usize),*
        }

        impl Stats {
            fn add(&mut self, o: &Stats) {
                $(self.$f += o.$f;)*
            }
        }
    };
}

// tickets: every ticket; verifies: tickets with host-known drafts; continuations: tickets whose
// input is a deferred position, of which behind_verify have slack > 0 and deferred_drafts have
// `Deferred(k > 0)`; windows: continuation windows checked against slot_of, of which shifted have
// σ > 0; accepted, rejected: drafts; eos_bound, eos_ignored: the v0.5 EOS row; stops, orphans: D25;
// hits: attaches with cached tokens; kv_checked: slots the device checked before a ticket;
// iso_checked: units of pending tickets checked against other leases' tables; the rest count
// injected protocol checks, capacity errors and probes.
stats!(
    tickets,
    verifies,
    continuations,
    behind_verify,
    deferred_drafts,
    windows,
    shifted,
    accepted,
    rejected,
    eos_bound,
    eos_ignored,
    stops,
    orphans,
    hits,
    kv_checked,
    iso_checked,
    preemptions,
    out_of_order,
    release_busy,
    full_queue,
    stopped_checks,
    attach_nocap,
    deferred_nocap,
    extend_nocap,
    probes,
    probes_skipped,
);

struct RunOut {
    reqs: Vec<ReqOut>,
    stats: Stats,
}

struct Run<'a> {
    cfg: &'a Cfg,
    m: Model,
    co: Coordinator,
    rng: Rng,
    /// The device's memory: per paged class one value per token slot, per state class one per unit.
    kv: Vec<Vec<u64>>,
    st: Vec<Vec<u64>>,
    reqs: Vec<Req>,
    waiting: VecDeque<usize>,
    lives: Vec<Live>,
    issued: Vec<Issued>,
    by_ticket: HashMap<u64, usize>,
    stats: Stats,
}

/// Serves every request of `mix` on a fresh coordinator of `cfg`.
fn run(cfg: &Cfg, mix: &[ReqSpec], seed: u64) -> Result<RunOut, String> {
    let co = ck(Coordinator::create(cfg.nslab, SLAB, &cfg.pu, &cfg.du, &cfg.su, B, cfg.lam, cfg.delta, NS), "create")?;
    let m = cfg.model();
    let kv = cfg.pu.iter().chain(&cfg.du).map(|u| vec![UNWRITTEN; cfg.nslab * (SLAB / u) * B]).collect();
    let st = cfg.su.iter().map(|u| vec![UNWRITTEN; cfg.nslab * (SLAB / u)]).collect();
    let reqs = mix
        .iter()
        .map(|s| Req {
            spec: s.clone(),
            expect: plain_decoding(&m, &s.prompt, s.max_tokens),
            resume: s.prompt.clone(),
            out: Vec::new(),
            finished: false,
            kept: None,
            eos_bound: false,
            done: None,
        })
        .collect();
    let seed = mix_seed(seed, cfg);
    Run {
        cfg,
        m,
        co,
        rng: Rng::new(seed),
        kv,
        st,
        reqs,
        waiting: (0..mix.len()).collect(),
        lives: Vec::new(),
        issued: Vec::new(),
        by_ticket: HashMap::new(),
        stats: Stats::default(),
    }
    .go()
}

/// A scheduler seed that differs between the runs a test compares.
fn mix_seed(seed: u64, cfg: &Cfg) -> u64 {
    mix(mix(seed, cfg.delta as u64), (cfg.lam + 8 * cfg.du.len()) as u64)
}

impl Run<'_> {
    fn go(mut self) -> Result<RunOut, String> {
        for tick in 0..MAX_TICKS {
            if self.reqs.iter().all(|r| r.done.is_some()) {
                let reqs = self.reqs.into_iter().map(|r| r.done.expect("done")).collect();
                return Ok(RunOut { reqs, stats: self.stats });
            }
            self.step().map_err(|e| format!("step {tick}: {e}"))?;
            self.stats.iso_checked += self.check_all(None).map_err(|e| format!("step {tick}: {e}"))?;
        }
        Err(format!("[harness] the run did not finish in {MAX_TICKS} steps"))
    }

    /// One random action of the scheduler or the device.
    fn step(&mut self) -> Result<(), String> {
        let roll = self.rng.below(100);
        if roll < 12 || self.lives.is_empty() {
            return self.admit();
        }
        let li = self.rng.below(self.lives.len());
        match roll {
            12..=46 => self.plan(li),
            47..=66 => self.execute(li),
            67..=96 => self.process(li),
            _ => self.maybe_preempt(li),
        }
    }

    fn view(&self, h: Handle) -> Result<View, String> {
        let v = ck(self.co.inspect(h), "inspect")?;
        Ok(View {
            len: v.len,
            computed: v.computed,
            reach: v.reach,
            planned: v.planned,
            slack: v.slack,
            deferred: v.deferred,
            stopped: v.stopped,
            queue: v.queue,
            tables: v.lease.tables,
            slots: v.lease.slots,
        })
    }

    // ---- the scheduler ----

    fn admit(&mut self) -> Result<(), String> {
        if self.lives.len() >= self.cfg.max_live {
            return Ok(());
        }
        let Some(rid) = self.waiting.pop_front() else { return Ok(()) };
        let t = self.reqs[rid].resume.clone();
        match self.co.attach(&t) {
            Ok((h, cached, _)) => {
                // D3: whole blocks, never the last one; D13: no hits with a state class.
                ensure!(cached % B == 0 && cached < t.len(), "[attach] request {rid}: {cached} of {} tokens cached", t.len());
                ensure!(self.m.ns == 0 || cached == 0, "[attach] request {rid}: a hit with a state class");
                if cached > 0 {
                    self.stats.hits += 1;
                }
                self.lives.push(Live {
                    rid,
                    h,
                    host_t: t.clone(),
                    queue: VecDeque::new(),
                    held: None,
                    held_drafts: Vec::new(),
                    stopped: false,
                    seq: t,
                    end: cached,
                    dev_pending: VecDeque::new(),
                    dev_done: Vec::new(),
                });
            },
            Err(Error::NoCapacity) => {
                ensure!(!self.lives.is_empty(), "[harness] request {rid} does not fit in an idle arena");
                self.waiting.push_front(rid);
                self.stats.attach_nocap += 1;
            },
            Err(e) => return Err(format!("[coord] attach of request {rid} returned {e:?}")),
        }
        Ok(())
    }

    /// Plans the next ticket of a lease, if it has room for one: a chunk of known inputs, a verify
    /// with host-known drafts, or, while its newest step is in flight, a continuation (D21, D24).
    fn plan(&mut self, li: usize) -> Result<(), String> {
        let (h, rid) = (self.lives[li].h, self.lives[li].rid);
        if self.lives[li].stopped {
            return self.check_stopped(li);
        }
        if self.reqs[rid].finished {
            return Ok(());
        }
        let mut v = self.view(h)?;
        if v.queue.is_empty() && v.planned == v.len && !v.deferred {
            // Every input is computed: append the token the last completion sampled (C2, D17).
            let Some(x) = self.lives[li].held.take() else {
                return Err(format!("[harness] request {rid} has nothing to plan"));
            };
            match self.co.extend(h, &[x]) {
                Ok(_) => self.lives[li].host_t.push(x),
                Err(Error::NoCapacity) => {
                    self.lives[li].held = Some(x);
                    self.stats.extend_nocap += 1;
                    return self.preempt(li);
                },
                Err(e) => return Err(format!("[coord] extend of request {rid} returned {e:?}")),
            }
            v = self.view(h)?;
            ensure!(v.reach == v.len + self.cfg.mu(), "[bounds] request {rid}: extend set ρ = {}, not L + μ", v.reach);
        }
        if v.queue.len() > self.cfg.delta {
            // D21: a full queue takes no ticket.
            if self.rng.chance(10) {
                ensure!(
                    matches!(self.co.begin_write(h, 1, Drafts::Known(Vec::new()), false), Err(Error::Busy)),
                    "[protocol] begin_write on a full queue is not Busy"
                );
                ensure!(self.view(h)? == v, "[protocol] begin_write on a full queue changed the lease");
                self.stats.full_queue += 1;
            }
            return Ok(());
        }
        let lhat = v.len + usize::from(v.deferred);
        if v.planned < lhat {
            return if v.deferred { self.issue_continuation(li, &v) } else { self.issue_known(li, &v) };
        }
        // The newest ticket reaches the end of the planned input and is in flight: plan the next
        // step before its token reaches the host (C2b), if the request may need it.
        if self.cfg.delta == 0 || v.queue.is_empty() {
            return Ok(());
        }
        let newest = *self.lives[li].queue.back().expect("a pending ticket");
        if !self.issued[newest].samples {
            return Ok(());
        }
        let inflight = self.lives[li].queue.iter().filter(|&&ix| self.issued[ix].samples).count();
        let req = &self.reqs[rid];
        if req.out.len() + inflight + 1 > req.spec.max_tokens || !self.rng.chance(self.cfg.pipeline) {
            return Ok(());
        }
        match self.co.extend_deferred(h) {
            Ok(_) => {},
            Err(Error::NoCapacity) => {
                // C2b: wait for the newest step, then extend.
                self.stats.deferred_nocap += 1;
                return Ok(());
            },
            Err(e) => return Err(format!("[coord] extend_deferred of request {rid} returned {e:?}")),
        }
        self.issued[newest].heads_x = true;
        let v2 = self.view(h)?;
        ensure!(
            v2.deferred && v2.len == v.len && v2.computed == v.computed && v2.reach == v.len + 1 + self.cfg.mu(),
            "[deferred] request {rid}: extend_deferred left {v2:?}"
        );
        self.issue_continuation(li, &v2)
    }

    /// D25: a stopped lease takes no new work.
    fn check_stopped(&mut self, li: usize) -> Result<(), String> {
        if !self.rng.chance(20) {
            return Ok(());
        }
        let h = self.lives[li].h;
        let before = self.view(h)?;
        ensure!(
            matches!(self.co.begin_write(h, 1, Drafts::Known(Vec::new()), false), Err(Error::InvalidPhase)),
            "[protocol] begin_write on a stopped lease is not InvalidPhase"
        );
        ensure!(matches!(self.co.extend(h, &[2]), Err(Error::InvalidPhase)), "[protocol] extend on a stopped lease is not InvalidPhase");
        ensure!(
            matches!(self.co.extend_deferred(h), Err(Error::InvalidPhase)),
            "[protocol] extend_deferred on a stopped lease is not InvalidPhase"
        );
        ensure!(self.view(h)? == before, "[protocol] a call on a stopped lease changed it");
        self.stats.stopped_checks += 1;
        Ok(())
    }

    /// A ticket with known inputs `[p_h, p_h + n)`: a prefill chunk, a decode step, or a verify with
    /// host-known drafts (which needs an empty queue, D21).
    fn issue_known(&mut self, li: usize, v: &View) -> Result<(), String> {
        let (h, rid) = (self.lives[li].h, self.lives[li].rid);
        let rem = v.len - v.planned;
        let n = if self.rng.chance(50) { rem } else { self.rng.range(1, rem) };
        let reaches = v.planned + n == v.len;
        let mut d = Vec::new();
        if reaches && v.queue.is_empty() && self.cfg.lam > 0 && self.rng.chance(75) {
            let k = self.rng.range(1, self.cfg.lam);
            d = self.host_drafts(li, k);
        }
        let propose = reaches && !self.cfg.du.is_empty() && self.rng.chance(80);
        let (t, plan) = ck(self.co.begin_write(h, n, Drafts::Known(d.clone()), propose), "begin_write")?;
        let lo = v.planned;
        let mut inputs = self.lives[li].host_t[lo..lo + n].to_vec();
        inputs.extend_from_slice(&d);
        ensure!(
            plan.lo == lo && plan.slack == 0 && plan.num_inputs == n && plan.num_drafts == d.len() && plan.producer.is_none(),
            "[plan] request {rid}: lo {} slack {} ℓ {} k {} for a chunk of {n} at {lo} with {} drafts",
            plan.lo,
            plan.slack,
            plan.num_inputs,
            plan.num_drafts,
            d.len()
        );
        ensure!(plan.input_ids == inputs, "[plan] request {rid}: input_ids {:?}, not T_h[lo..lo + n] ++ D = {inputs:?}", plan.input_ids);
        ensure!(
            plan.positions == (lo..lo + inputs.len()).collect::<Vec<_>>() && plan.init == (lo == 0) && plan.state_slots == v.slots,
            "[plan] request {rid}: positions, init or state slots"
        );
        for (c, ws) in plan.write_slots.iter().enumerate() {
            let extra = if c >= self.m.nt && propose { self.cfg.lam } else { 0 };
            ensure!(ws.len() == inputs.len() + extra, "[plan] request {rid}: {} slots listed for class {c}", ws.len());
        }
        if !d.is_empty() {
            self.stats.verifies += 1;
        }
        self.lives[li].held_drafts.clear();
        self.record(li, t, plan, reaches)
    }

    /// A continuation of the newest pending ticket: its input is the deferred position, its start
    /// is bounded by `lo = p_h` and the slack `s_h`, and its drafts, if any, are the ones the
    /// producer's proposal forward samples on the device (D24).
    fn issue_continuation(&mut self, li: usize, v: &View) -> Result<(), String> {
        let (h, rid) = (self.lives[li].h, self.lives[li].rid);
        let newest = *self.lives[li].queue.back().expect("a producer");
        let (prod_t, prod_propose) = (self.issued[newest].t, self.issued[newest].plan.propose);
        let lam = self.cfg.lam;
        let k = if lam > 0 && prod_propose && self.rng.chance(85) { self.rng.range(1, lam) } else { 0 };
        let drafts = if k > 0 || self.rng.chance(30) { Drafts::Deferred(k) } else { Drafts::Known(Vec::new()) };
        let propose = !self.cfg.du.is_empty() && self.rng.chance(80);
        let (t, plan) = ck(self.co.begin_write(h, 1, drafts, propose), "begin_write of a continuation")?;
        let lo = v.planned;
        ensure!(
            plan.producer == Some(prod_t) && plan.lo == lo && plan.slack == v.slack && plan.num_inputs == 1 && plan.num_drafts == k,
            "[plan] request {rid}: continuation with producer {:?}, lo {}, slack {}, ℓ {}, k {}",
            plan.producer,
            plan.lo,
            plan.slack,
            plan.num_inputs,
            plan.num_drafts
        );
        ensure!(
            plan.input_ids == vec![0; 1 + k] && plan.positions == (lo..lo + 1 + k).collect::<Vec<_>>() && !plan.init,
            "[plan] request {rid}: a continuation's placeholders and lowest-outcome positions"
        );
        for (c, ws) in plan.write_slots.iter().enumerate() {
            let extra = if c >= self.m.nt && propose { lam } else { 0 };
            ensure!(
                ws.len() == v.slack + 1 + k + extra,
                "[plan] request {rid}: {} slots listed for class {c}, not s + 1 + k = {}",
                ws.len(),
                v.slack + 1 + k + extra
            );
        }
        self.stats.continuations += 1;
        if v.slack > 0 {
            self.stats.behind_verify += 1;
        }
        if k > 0 {
            self.stats.deferred_drafts += 1;
        }
        self.record(li, t, plan, true)
    }

    /// Host-known drafts for a verify at the end of `T_h`: the proposal the last completion handed
    /// to the caller, or else drafts from an external proposer (the same drafter, on the host).
    fn host_drafts(&mut self, li: usize, k: usize) -> Vec<u32> {
        let lv = &self.lives[li];
        if lv.held_drafts.len() >= k {
            return lv.held_drafts[..k].to_vec();
        }
        let noise = self.reqs[lv.rid].spec.noise;
        let (last, prefix) = lv.host_t.split_last().expect("a non-empty lease");
        let ch = chain_over(&self.m, prefix);
        draft(&self.m, ch, *last, k, noise, &mut self.rng)
    }

    /// Checks a new plan's listed slots and queues the ticket for the device.
    fn record(&mut self, li: usize, t: Ticket, plan: CoordPlan, samples: bool) -> Result<(), String> {
        let h = self.lives[li].h;
        ensure!(plan.ticket == t && plan.handle == h && plan.block_size == B, "[plan] ticket, handle or B");
        let p = PlanInfo::from(plan);
        for (c, ws) in p.write_slots.iter().enumerate() {
            let mut distinct = ws.clone();
            distinct.sort_unstable();
            distinct.dedup();
            ensure!(distinct.len() == ws.len(), "[plan] the listed slots of class {c} are not distinct");
            for (i, &s) in ws.iter().enumerate() {
                let pos = p.lo + i;
                ensure!(s == ck(self.co.slot_of(c, h, pos), "slot_of")?, "[plan] listed slot of class {c} at {pos} is not slot_of");
                ensure!(
                    p.page_tables[c].get(pos / B).map(|g| g * B + pos % B) == Some(s),
                    "[plan] the page mapping of class {c} disagrees with the listed slot at {pos}"
                );
            }
        }
        let ix = self.issued.len();
        self.by_ticket.insert(t.id, ix);
        self.issued.push(Issued { t, plan: p, samples, heads_x: false, orphan: false, dev: None });
        self.lives[li].queue.push_back(ix);
        self.lives[li].dev_pending.push_back(ix);
        self.stats.tickets += 1;
        Ok(())
    }

    // ---- the device ----

    /// Runs the oldest ticket of a lease that the device has not run yet.
    fn execute(&mut self, li: usize) -> Result<(), String> {
        let Some(ix) = self.lives[li].dev_pending.pop_front() else { return Ok(()) };
        let (m, lam) = (self.m, self.cfg.lam);
        let (h, rid, a) = (self.lives[li].h, self.lives[li].rid, self.lives[li].end);
        let p = self.issued[ix].plan.clone();
        let samples = self.issued[ix].samples;
        let noise = self.reqs[rid].spec.noise;
        let (l, k) = (p.l, p.k);
        // D24: the window starts where the previous ticket's input and accepted drafts end.
        ensure!(
            a >= p.lo && a - p.lo <= p.slack,
            "[window] request {rid}, ticket {ix}: the window starts at {a}, outside [lo, lo + s] = [{}, {}]",
            p.lo,
            p.lo + p.slack
        );
        let sigma = a - p.lo;
        let z = a + l;
        // E13(2): a continuation's input is its producer's bonus token, its drafts the producer's proposal.
        let producer = p.producer.map(|t| self.by_ticket[&t.id]);
        let (inputs, drafts) = match producer {
            Some(pi) => {
                ensure!(
                    self.lives[li].dev_done.last() == Some(&pi),
                    "[window] request {rid}, ticket {ix}: the producer is not the lease's last ticket"
                );
                let po = self.issued[pi].dev.as_ref().expect("the producer has run");
                let bonus = po.bonus.expect("a producer samples");
                ensure!(po.proposals.len() >= k, "[harness] the producer proposed {} drafts, fewer than {k}", po.proposals.len());
                (vec![bonus], po.proposals[..k].to_vec())
            },
            None => (p.input_ids[..l].to_vec(), p.input_ids[l..].to_vec()),
        };
        let seq_len = self.lives[li].seq.len();
        ensure!(
            seq_len >= z && self.lives[li].seq[a..z] == inputs[..],
            "[input] request {rid}, ticket {ix}: inputs {inputs:?} are not the lease's tokens at [{a}, {z})"
        );
        ensure!(!samples || seq_len == z, "[harness] a sampling ticket does not end at the lease's last token");
        // D24, C3: the window lies inside the listed slots, at the slots slot_of names.
        for (c, ws) in p.write_slots.iter().enumerate() {
            let width = l + k + if c >= m.nt && p.propose { lam } else { 0 };
            ensure!(sigma + width <= ws.len(), "[window] request {rid}, ticket {ix}: the window of class {c} overruns the listed slots");
            for (i, &s) in ws[sigma..sigma + width].iter().enumerate() {
                ensure!(
                    s == ck(self.co.slot_of(c, h, a + i), "slot_of")?,
                    "[window] request {rid}, ticket {ix}: listed slot {} of class {c} is not slot_of({})",
                    sigma + i,
                    a + i
                );
            }
        }
        if producer.is_some() {
            self.stats.windows += 1;
            if sigma > 0 {
                self.stats.shifted += 1;
            }
        }
        // §9.0 (b): every slot of [0, a) holds the KV of the lease's tokens, in every paged class.
        let mut ch = Chain::start();
        for pos in 0..a {
            let tok = self.lives[li].seq[pos];
            let kv = Model::kv(ch.att, tok, pos);
            for (c, table) in p.page_tables.iter().enumerate() {
                let s = table[pos / B] * B + pos % B;
                ensure!(
                    self.kv[c][s] == Model::content(kv, c),
                    "[kv] request {rid}, ticket {ix}: class {c} holds stale KV at position {pos} (slot {s})"
                );
            }
            ch.feed(&m, tok);
        }
        self.stats.kv_checked += a * p.page_tables.len();
        // I15, E11: the state slot holds the state after [0, a), or the plan starts from the initial state.
        if p.init {
            ensure!(a == 0, "[state] request {rid}, ticket {ix}: init at position {a}");
        } else {
            for (s, &g) in p.state_slots.iter().enumerate() {
                ensure!(
                    self.st[s][g] == Model::state_content(ch.st, s),
                    "[state] request {rid}, ticket {ix}: state class {s} does not hold the state after {a} tokens"
                );
            }
        }
        // The forward over the window writes target and drafter KV at every position (D20).
        let mut cur = ch;
        let mut after = Vec::with_capacity(l + k);
        let mut outs = Vec::with_capacity(k + 1);
        for (i, &tok) in inputs.iter().chain(&drafts).enumerate() {
            let (kv, next) = cur.feed(&m, tok);
            for (c, ws) in p.write_slots.iter().enumerate() {
                self.kv[c][ws[sigma + i]] = Model::content(kv, c);
            }
            after.push(cur);
            if i + 1 >= l {
                outs.push(next);
            }
        }
        // The greedy sampler accepts the leading drafts that equal the model's tokens.
        let mut n = 0;
        while n < k && drafts[n] == outs[n] {
            n += 1;
        }
        let bonus = samples.then(|| outs[n]);
        if k > 0 {
            self.stats.accepted += n;
            self.stats.rejected += k - n;
            ensure!(noise > 0 || n == k, "[accept] request {rid}, ticket {ix}: clean drafts rejected after {n} of {k}");
        }
        // E11: the state after the input and the accepted drafts, in the same slot.
        for (s, &g) in p.state_slots.iter().enumerate() {
            self.st[s][g] = Model::state_content(after[l + n - 1].st, s);
        }
        // D20: the proposal forward writes λ rows from the bonus position and samples λ drafts.
        let mut proposals = Vec::new();
        if p.propose {
            let bonus = bonus.expect("a ticket with propose samples");
            proposals = draft(&m, after[l + n - 1], bonus, lam, noise, &mut self.rng);
            let first = sigma + l + n;
            for (j, &d) in proposals.iter().enumerate() {
                for (c, ws) in p.write_slots.iter().enumerate().skip(m.nt) {
                    self.kv[c][ws[first + j]] = mix(0x9809_05A1 + j as u64, u64::from(d));
                }
            }
        }
        // The lease's tokens as the coordinator will commit them.
        let lv = &mut self.lives[li];
        if let Some(x) = bonus {
            lv.seq.truncate(z);
            lv.seq.extend_from_slice(&drafts[..n]);
            lv.seq.push(x);
            lv.end = z + n;
        } else {
            lv.end = z;
        }
        lv.dev_done.push(ix);
        self.issued[ix].dev = Some(DevOut { n, bonus, drafts, proposals });
        Ok(())
    }

    // ---- completions ----

    /// Processes the completion of the oldest ticket of a lease, once the device has run it.
    fn process(&mut self, li: usize) -> Result<(), String> {
        let Some(&head) = self.lives[li].queue.front() else { return Ok(()) };
        while self.issued[head].dev.is_none() {
            self.execute(li)?;
        }
        let (h, rid) = (self.lives[li].h, self.lives[li].rid);
        // C4: only the oldest ticket of a lease completes; a younger one is InvalidTicket.
        if self.lives[li].queue.len() > 1 && self.rng.chance(50) {
            let t2 = self.issued[self.lives[li].queue[1]].t;
            let before = self.view(h)?;
            let r = self.co.finish_write(t2, CoordCompletion { ticket: t2, accepted: 0, token: Some(5), drafts: Vec::new(), stop: false });
            ensure!(r == Err(Error::InvalidTicket), "[protocol] out-of-order finish_write returned {r:?}");
            ensure!(self.view(h)? == before, "[protocol] an out-of-order finish_write changed the lease");
            self.stats.out_of_order += 1;
        }
        // C5: release is Busy while any ticket is pending.
        if self.rng.chance(30) {
            let before = self.view(h)?;
            let r = self.co.release(h);
            ensure!(matches!(r, Err(Error::Busy)), "[protocol] release with a pending ticket returned {:?}", r.map(|s| s.len()));
            ensure!(self.view(h)? == before, "[protocol] a Busy release changed the lease");
            self.stats.release_busy += 1;
        }
        let before = self.view(h)?;
        let (t, samples, heads_x, orphan) = {
            let it = &self.issued[head];
            (it.t, it.samples, it.heads_x, it.orphan)
        };
        let (l, k, continuation) = {
            let p = &self.issued[head].plan;
            (p.l, p.k, p.producer.is_some())
        };
        let dv = self.issued[head].dev.clone().expect("the device has run it");
        if orphan {
            // D25: an orphan accepts any completion and changes nothing but the queue.
            let c = if self.rng.chance(50) {
                CoordCompletion { ticket: t, accepted: dv.n, token: dv.bonus, drafts: dv.drafts.clone(), stop: false }
            } else {
                CoordCompletion { ticket: t, accepted: 7, token: Some(9), drafts: vec![1, 2, 3], stop: self.rng.chance(50) }
            };
            let r = ck(self.co.finish_write(t, c), "finish_write of an orphan")?;
            let after = self.view(h)?;
            ensure!(
                r == before.computed
                    && after.len == before.len
                    && after.computed == before.computed
                    && after.tables == before.tables
                    && after.queue[..] == before.queue[1..],
                "[orphan] request {rid}: finish_write of an orphan changed the lease"
            );
            self.lives[li].queue.pop_front();
            self.stats.orphans += 1;
        } else if !samples {
            let r = ck(self.co.finish_write(t, CoordCompletion { ticket: t, accepted: 0, token: None, drafts: Vec::new(), stop: false }), "finish_write")?;
            ensure!(r == before.computed + l, "[frontier] request {rid}: finish_write returned c = {r}, not {}", before.computed + l);
            self.lives[li].queue.pop_front();
        } else if self.reqs[rid].finished {
            // §7 (v0.5): the step after an EOS ignores its token and sets c_h = L_h.
            ensure!(!heads_x && k == 0, "[harness] a step after the EOS heads X_h or has drafts");
            let c = CoordCompletion { ticket: t, accepted: 0, token: dv.bonus, drafts: Vec::new(), stop: false };
            let r = ck(self.co.finish_write(t, c), "finish_write after the EOS")?;
            let after = self.view(h)?;
            ensure!(
                r == before.len && after.len == before.len && after.computed == after.len,
                "[eos] request {rid}: the step after the EOS returned c = {r} with L = {}, now L = {}",
                before.len,
                after.len
            );
            self.lives[li].queue.pop_front();
            self.stats.eos_ignored += 1;
        } else {
            // The device's acceptance count and bonus token. The host applies the stop rules (EOS,
            // max_tokens) that the device does not (D25).
            let n_dev = dv.n;
            let bonus = dv.bonus.expect("a sampling ticket");
            let mut cand = dv.drafts[..n_dev].to_vec();
            cand.push(bonus);
            let mut take = 0;
            let mut fin = false;
            {
                let req = &mut self.reqs[rid];
                for &x in &cand {
                    let i = req.out.len();
                    ensure!(
                        req.expect.get(i) == Some(&x),
                        "[stream] request {rid}: token {i} is {x}, plain decoding has {:?}",
                        req.expect.get(i)
                    );
                    req.out.push(x);
                    take += 1;
                    if x == EOS || req.out.len() == req.spec.max_tokens {
                        fin = true;
                        break;
                    }
                }
            }
            // λ = 0 finishes an EOS the v0.5 way, without stop; speculation reports it with stop
            // (D23), cut inside the accepted drafts or at the bonus token.
            let v05 = self.cfg.lam == 0;
            let (acc, token, stop) = if take <= n_dev { (take, None, true) } else { (n_dev, Some(bonus), fin && !v05) };
            let drafts = if continuation && k > 0 { dv.drafts[..acc].to_vec() } else { Vec::new() };
            let r = ck(self.co.finish_write(t, CoordCompletion { ticket: t, accepted: acc, token, drafts, stop }), "finish_write")?;
            ensure!(
                r == before.computed + l + acc,
                "[frontier] request {rid}: finish_write returned c = {r}, not z + n = {}",
                before.computed + l + acc
            );
            let lv = &mut self.lives[li];
            lv.queue.pop_front();
            lv.host_t.extend_from_slice(&cand[..acc]);
            if heads_x && token.is_some() {
                lv.host_t.push(bonus);
            }
            if fin {
                let req = &mut self.reqs[rid];
                req.finished = true;
                req.kept = if take > n_dev && !heads_x { Some(bonus) } else { None };
                if v05 && heads_x {
                    // Pipelining stops before max_tokens, so only an EOS ends a request here.
                    ensure!(bonus == EOS, "[harness] request {rid} ended at a producer without an EOS");
                    req.eos_bound = true;
                    self.stats.eos_bound += 1;
                }
                if stop {
                    lv.stopped = true;
                    for &ix in &lv.queue {
                        self.issued[ix].orphan = true;
                    }
                    self.stats.stops += 1;
                }
            } else if !heads_x {
                ensure!(lv.queue.is_empty(), "[harness] a ticket behind a producer that does not head X_h");
                lv.held = Some(bonus);
                lv.held_drafts = dv.proposals;
            }
        }
        let after = self.view(h)?;
        ensure!(!after.deferred, "[deferred] request {rid}: X_h is not empty after its head completed");
        let lv = &self.lives[li];
        if (self.reqs[rid].finished || lv.stopped) && lv.queue.is_empty() {
            return self.finalize(li);
        }
        Ok(())
    }

    /// Releases a finished lease, checks its snapshot, and probes which of its blocks are published.
    fn finalize(&mut self, li: usize) -> Result<(), String> {
        let before = self.view(self.lives[li].h)?;
        let lv = self.lives.remove(li);
        let rid = lv.rid;
        let snap = ck(self.co.release(lv.h), "release")?;
        ensure!(snap == lv.host_t, "[snapshot] request {rid}: release returned {snap:?}, the scheduler holds {:?}", lv.host_t);
        let req = &self.reqs[rid];
        let mut full = snap.clone();
        full.extend(req.kept);
        let mut want = req.spec.prompt.clone();
        want.extend_from_slice(&req.out);
        ensure!(full == want, "[stream] request {rid}: snapshot {snap:?} and kept token {:?} are not prompt ++ output", req.kept);
        if req.eos_bound {
            ensure!(
                snap.last() == Some(&EOS) && before.computed == before.len,
                "[eos] request {rid}: the bound EOS is not the last computed token"
            );
        }
        // I5b: every block below c_h is published, keyed over the real tokens; with unique
        // prompts nothing past it is (D13: nothing at all with a state class).
        let mut probe_t = snap.clone();
        probe_t.push(SENTINEL);
        let probe = match self.co.attach(&probe_t) {
            Ok((hp, cached, lease)) => {
                self.stats.iso_checked += self.check_all(Some(&lease))?;
                ck(self.co.release(hp), "release of a probe")?;
                let expect = if self.m.ns > 0 { 0 } else { before.computed / B * B };
                ensure!(
                    cached == expect,
                    "[publish] request {rid}: a later attach reports {cached} cached tokens, not {expect} (c_h = {})",
                    before.computed
                );
                self.stats.probes += 1;
                Some(cached)
            },
            Err(Error::NoCapacity) => {
                self.stats.probes_skipped += 1;
                None
            },
            Err(e) => return Err(format!("[coord] the probe attach of request {rid} returned {e:?}")),
        };
        let req = &mut self.reqs[rid];
        req.done = Some(ReqOut { out: req.out.clone(), snapshot: snap, kept: req.kept, eos_bound: req.eos_bound, probe });
        Ok(())
    }

    fn maybe_preempt(&mut self, li: usize) -> Result<(), String> {
        let lv = &self.lives[li];
        if !lv.queue.is_empty() || lv.stopped || self.reqs[lv.rid].finished || !self.rng.chance(40) {
            return Ok(());
        }
        self.preempt(li)
    }

    /// Releases a lease with an empty queue and queues its request to attach again with everything
    /// committed so far (C1, C5).
    fn preempt(&mut self, li: usize) -> Result<(), String> {
        let lv = self.lives.remove(li);
        let snap = ck(self.co.release(lv.h), "release of a preempted lease")?;
        ensure!(snap == lv.host_t, "[snapshot] request {}: release returned {snap:?}, the scheduler holds {:?}", lv.rid, lv.host_t);
        let mut resume = snap;
        resume.extend(lv.held);
        self.reqs[lv.rid].resume = resume;
        self.waiting.push_back(lv.rid);
        self.stats.preemptions += 1;
        Ok(())
    }

    // ---- invariants checked after every step ----

    /// Bounds and the scheduler's mirror for every lease, and I9's isolation of pending tickets:
    /// every unit a pending ticket may write (a listed slot at or past `c_h`) is in its own lease's
    /// table and in no other table, the probe's included. Returns how many such units it checked.
    fn check_all(&self, probe: Option<&LeaseView>) -> Result<usize, String> {
        let (mu, delta, lam) = (self.cfg.mu(), self.cfg.delta, self.cfg.lam);
        let mut views = Vec::with_capacity(self.lives.len());
        let mut holders: HashMap<(usize, usize), Vec<usize>> = HashMap::new();
        let mut slots: HashMap<(usize, usize), usize> = HashMap::new();
        for (li, lv) in self.lives.iter().enumerate() {
            let rid = lv.rid;
            let v = self.view(lv.h)?;
            let lhat = v.len + usize::from(v.deferred);
            ensure!(
                v.computed <= v.len && lhat <= v.reach,
                "[bounds] request {rid}: computed {}, len {}, L̂ {lhat}, reach {}",
                v.computed,
                v.len,
                v.reach
            );
            ensure!(v.queue.len() <= delta + 1, "[bounds] request {rid}: {} tickets pending", v.queue.len());
            if !v.stopped {
                // I16 and §3.2: ρ ≤ L̂ + μ, p_h = c_h + Σ ℓ ≤ L̂ and s_h = Σ k over the queue.
                let (sum_l, sum_k) = lv.queue.iter().fold((0, 0), |(l, k), &ix| (l + self.issued[ix].plan.l, k + self.issued[ix].plan.k));
                ensure!(v.reach <= lhat + mu, "[bounds] request {rid}: reach {} past L̂ + μ = {}", v.reach, lhat + mu);
                ensure!(
                    v.planned == v.computed + sum_l && v.planned <= lhat && v.slack == sum_k && sum_k <= (delta + 1) * lam,
                    "[bounds] request {rid}: p_h {} and s_h {} with c_h {}, Σ ℓ = {sum_l} and Σ k = {sum_k}",
                    v.planned,
                    v.slack,
                    v.computed
                );
            }
            ensure!(v.len == lv.host_t.len() && v.stopped == lv.stopped, "[mirror] request {rid}: L = {}, stopped = {}", v.len, v.stopped);
            ensure!(lv.seq.starts_with(&lv.host_t), "[mirror] request {rid}: T_h is not a prefix of the device's tokens");
            let queue: Vec<Ticket> = lv.queue.iter().map(|&ix| self.issued[ix].t).collect();
            ensure!(v.queue == queue, "[mirror] request {rid}: the queue is {:?}, the scheduler holds {queue:?}", v.queue);
            for (c, table) in v.tables.iter().enumerate() {
                ensure!(table.len() == v.reach.div_ceil(B), "[bounds] request {rid}: class {c} has {} pages for reach {}", table.len(), v.reach);
                for &g in table {
                    holders.entry((c, g)).or_default().push(li);
                }
            }
            for (s, &g) in v.slots.iter().enumerate() {
                ensure!(slots.insert((s, g), li).is_none(), "[iso] state slot {g} of class {s} is held twice");
            }
            views.push(v);
        }
        if let Some(lease) = probe {
            for (c, table) in lease.tables.iter().enumerate() {
                for &g in table {
                    holders.entry((c, g)).or_default().push(usize::MAX);
                }
            }
            for (s, &g) in lease.slots.iter().enumerate() {
                ensure!(slots.insert((s, g), usize::MAX).is_none(), "[iso] the probe holds state slot {g} of class {s}");
            }
        }
        let mut checked = 0;
        for (lv, v) in self.lives.iter().zip(&views) {
            for &ix in &lv.queue {
                let p = &self.issued[ix].plan;
                ensure!(p.state_slots == v.slots, "[iso] request {}: a pending plan names other state slots", lv.rid);
                for (c, ws) in p.write_slots.iter().enumerate() {
                    for (i, &s) in ws.iter().enumerate() {
                        let pos = p.lo + i;
                        if pos < v.computed {
                            continue;
                        }
                        let g = s / B;
                        ensure!(
                            v.tables[c].get(pos / B) == Some(&g),
                            "[iso] request {}: ticket {ix} lists slot {s} at {pos}, off the lease's page",
                            lv.rid
                        );
                        let hs = &holders[&(c, g)];
                        ensure!(
                            hs.len() == 1,
                            "[iso] request {}: unit {g} of class {c}, which pending ticket {ix} may write at {pos}, is in {} tables",
                            lv.rid,
                            hs.len()
                        );
                        checked += 1;
                    }
                }
            }
        }
        Ok(checked)
    }
}

// ---------------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------------

const SEEDS: u64 = 6;

/// §9.2, ZOS depth 1 against depth 0: each mix runs with `δ = 1`, pipelining with extend_deferred
/// and continuations, and with `δ = 0`.
///
/// - Token streams are identical, and so are release snapshots, except that `δ = 1` may bind a
///   final EOS through `X_h`: then its snapshot has the EOS appended (the EOS row of §7).
/// - Published blocks are identical, compared by what an attach right after each release reports
///   as cached, except the block that such an EOS completes, which only `δ = 1` publishes.
/// - Every run checks after every step that no unit a pending ticket may write is in another
///   lease's tables; injects out-of-order completions (InvalidTicket) and releases while tickets
///   are pending (Busy); and checks the EOS row: `finish_write(n)` appends the EOS, and
///   `finish_write(n + 1)` ignores its token and sets `c_h = L_h`.
#[test]
fn zos_depth_one_matches_depth_zero() {
    let configs = [
        Cfg::new("paged", 48, &[16], &[], &[], 0),
        Cfg::new("two paged classes", 48, &[16, 32], &[], &[], 0),
        Cfg::new("paged and state", 48, &[16], &[], &[8], 0),
        Cfg { max_live: 6, ..Cfg::new("tight", 5, &[16], &[], &[], 0) },
    ];
    let (mut one_total, mut zero_total) = (Stats::default(), Stats::default());
    let mut eos_blocks = 0;
    for cfg in &configs {
        for seed in 0..SEEDS {
            let mix = gen_mix(seed, cfg.nreq);
            let one = run(&cfg.depth(1), &mix, seed).unwrap_or_else(|e| panic!("{}, seed {seed}, δ = 1: {e}", cfg.name));
            let zero = run(&cfg.depth(0), &mix, seed).unwrap_or_else(|e| panic!("{}, seed {seed}, δ = 0: {e}", cfg.name));
            for (i, (r1, r0)) in one.reqs.iter().zip(&zero.reqs).enumerate() {
                let at = format!("{}, seed {seed}, request {i}", cfg.name);
                assert_eq!(r1.out, r0.out, "{at}: the token streams differ");
                if r1.eos_bound {
                    assert_eq!(r1.snapshot.split_last(), Some((&EOS, &r0.snapshot[..])), "{at}: δ = 1 bound the EOS, δ = 0 did not");
                } else {
                    assert_eq!(r1.snapshot, r0.snapshot, "{at}: the release snapshots differ");
                }
                if let (Some(p1), Some(p0)) = (r1.probe, r0.probe) {
                    let eos_block = r1.eos_bound && cfg.su.is_empty() && r1.snapshot.len() % B == 0;
                    eos_blocks += usize::from(eos_block);
                    assert_eq!(p1, p0 + if eos_block { B } else { 0 }, "{at}: the published blocks differ");
                }
            }
            one_total.add(&one.stats);
            zero_total.add(&zero.stats);
        }
    }
    eprintln!("δ = 1: {one_total:?}\nδ = 0: {zero_total:?}");
    let s = one_total;
    assert!(s.continuations > 0 && s.out_of_order > 0 && s.release_busy > 0 && s.full_queue > 0, "δ = 1 never pipelined: {s:?}");
    assert!(s.eos_bound > 0 && s.eos_ignored == s.eos_bound && eos_blocks > 0, "the EOS row was not exercised: {s:?}");
    assert!(s.hits > 0 && s.preemptions > 0 && s.probes > 0, "no hits, preemptions or probes: {s:?}");
    assert!(s.kv_checked > 0 && s.iso_checked > 0, "the KV and isolation checks saw nothing: {s:?}");
    assert!(s.attach_nocap > 0 && s.deferred_nocap > 0 && s.extend_nocap > 0, "the tight arena never ran out: {s:?}");
    assert_eq!(zero_total.continuations, 0);
}

/// §9.2, ZOS with speculation: speculative decoding with `λ > 0`, mostly with a drafter class and
/// `δ = 1`, against plain decoding (`λ = 0`, `δ = 0`) of the same model, with clean and noisy
/// drafters.
///
/// - The committed tokens equal plain decoding, and so does every release snapshot followed by
///   the token the scheduler kept.
/// - Every continuation's window, `write_slots[c][σ : σ + num_inputs + num_drafts]` plus `λ`
///   proposal rows in a drafter class with propose, lies inside its listed slots, and each slot is
///   what slot_of names for its position.
/// - After every step, inspect shows `computed <= len <= reach` (and the rest of I16's bounds).
///
/// The device takes a continuation's start, input and drafts only from its producer's outputs (the
/// device rows), and checks the KV and the state slot before every ticket.
#[test]
fn zos_with_speculation_matches_plain_decoding() {
    let configs = [
        Cfg::new("drafter, λ = 2", 48, &[16], &[16], &[], 2),
        Cfg::new("drafter and state, λ = 3", 64, &[16], &[32], &[8], 3),
        Cfg::new("host drafts without a drafter, λ = 2", 48, &[16], &[], &[], 2),
        Cfg::new("drafter, δ = 0", 48, &[16], &[16], &[], 2).depth(0),
        Cfg { max_live: 5, ..Cfg::new("tight drafter", 9, &[16], &[16], &[], 2) },
    ];
    let mut total = Stats::default();
    for cfg in &configs {
        for seed in 0..SEEDS {
            let mix = gen_mix(100 + seed, cfg.nreq);
            let spec = run(cfg, &mix, seed).unwrap_or_else(|e| panic!("{}, seed {seed}: {e}", cfg.name));
            let plain = run(&cfg.plain(), &mix, seed).unwrap_or_else(|e| panic!("{}, seed {seed}, plain: {e}", cfg.name));
            for (i, (rs, rp)) in spec.reqs.iter().zip(&plain.reqs).enumerate() {
                let at = format!("{}, seed {seed}, request {i}", cfg.name);
                assert_eq!(rs.out, rp.out, "{at}: the committed tokens differ from plain decoding");
                let full = |r: &ReqOut| r.snapshot.iter().copied().chain(r.kept).collect::<Vec<u32>>();
                assert_eq!(full(rs), full(rp), "{at}: the snapshots differ from plain decoding");
            }
            total.add(&spec.stats);
        }
    }
    eprintln!("speculation: {total:?}");
    let s = total;
    assert!(s.verifies > 0 && s.accepted > 0 && s.rejected > 0, "no verify accepted and rejected drafts: {s:?}");
    assert!(
        s.behind_verify > 0 && s.deferred_drafts > 0 && s.windows > 0 && s.shifted > 0,
        "no continuation behind a verify with a shifted window: {s:?}"
    );
    assert!(s.stops > 0 && s.orphans > 0 && s.stopped_checks > 0, "stop and orphans were not exercised: {s:?}");
    assert!(s.out_of_order > 0 && s.release_busy > 0 && s.hits > 0 && s.preemptions > 0, "{s:?}");
    assert!(s.kv_checked > 0 && s.iso_checked > 0, "the KV and isolation checks saw nothing: {s:?}");
    assert!(s.deferred_nocap > 0 && s.extend_nocap > 0, "the tight arena never ran out: {s:?}");
}
