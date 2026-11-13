"""End-to-end demo of the verified block manager through the Python facade.

Simulates a tiny scheduler: two requests sharing a prompt prefix, chunked prefill, decode via
extend, preemption via release + re-attach, and the error paths from contract §7.
"""
import pageproof as pp

B = 4
mgr = pp.BlockManager(8, B, b"dummy-v0.2")
print(f"manager: P={mgr.num_pages} B={mgr.block_size} free={mgr.free_pages}")


def run(h, n):
    plan = mgr.begin_write(h, n)
    # A real executor would run the model on plan.input_ids at plan.positions and write KV to
    # plan.write_slots. Here we only check the plan is self-consistent.
    assert len(plan.write_slots) == n == len(plan.positions)
    for j, s in zip(plan.positions, plan.write_slots):
        assert s == plan.page_table[j // B] * B + j % B
    return mgr.finish_write(plan.ticket)


prompt = list(range(100, 110))  # 10 tokens: blocks [0..4) [4..8) and tail [8..10)

h1, cached, pages = mgr.attach(prompt)
print(f"req1 attach: cached={cached} pages={pages}")
run(h1, 6)  # chunked prefill
run(h1, 4)
print(f"req1 prefilled: {mgr.inspect(h1)}")

h2, cached, pages2 = mgr.attach(prompt)
print(f"req2 attach (shares prefix): cached={cached} pages={pages2}")
assert cached == 8 and pages2[:2] == pages[:2]
run(h2, 2)

# Decode one token for req1.
mgr.extend(h1, [7])
run(h1, 1)
print(f"req1 after decode: {mgr.inspect(h1)}")

# In-flight protection.
mgr.extend(h2, [8, 9])
plan = mgr.begin_write(h2, 2)
for bad in (lambda: mgr.release(h2), lambda: mgr.extend(h2, [1])):
    try:
        bad()
    except pp.BlockManagerError as e:
        print(f"in-flight op rejected: {e}")
mgr.finish_write(plan.ticket)
try:
    mgr.finish_write(plan.ticket)
except pp.BlockManagerError as e:
    print(f"duplicate completion rejected: {e}")

# Preemption: release, then re-attach with the snapshot.
snap = mgr.release(h1)
h1b, cached, _ = mgr.attach(snap)
print(f"req1 re-attached after preemption: cached={cached} (computed prefix reused)")
try:
    mgr.inspect(h1)
except pp.BlockManagerError as e:
    print(f"stale handle rejected: {e}")

for h in (h1b, h2):
    mgr.release(h)
assert mgr.free_pages == mgr.num_pages
print(f"all released: free={mgr.free_pages}")
print("pageproof demo: ok")

# ---------------------------------------------------------------------------------------------
# v0.3: a slab arena shared by two paged classes and one recurrent-state class.
# ---------------------------------------------------------------------------------------------
# Unit sizes (bytes): paged class 0 = 16, paged class 1 = 64, state = 64; slab = lcm = 64 B.
co = pp.Coordinator(6, 64, [16, 64], [64], B, b"dummy-v0.3")
print(f"coordinator arena: {co.arena()}")


def run_c(h, n):
    plan = co.begin_write(h, n)
    assert len(plan.write_slots) == 2 and all(len(w) == n for w in plan.write_slots)
    for c, (ws, pt) in enumerate(zip(plan.write_slots, plan.page_tables)):
        for j, s in zip(plan.positions, ws):
            assert s == pt[j // B] * B + j % B, (c, j, s)
    return plan, co.finish_write(plan.ticket)


ha, cached, la = co.attach(list(range(200, 208)))
assert cached == 0, "a state class disables prefix hits (D13)"
plan, _ = run_c(ha, 8)
assert plan.init and plan.state_slots == la["slots"]
print(f"hybrid lease attached and prefilled: {co.inspect(ha)}")

co.extend(ha, [1])
plan, _ = run_c(ha, 1)
assert not plan.init, "decode reads the live state slot"
co.release(ha)
print(f"after release (slabs kept, reclaimable): {co.arena()}")

# A burst of short leases forces reclaim of idle keyed slabs into the class that needs them.
hs = []
while True:
    try:
        h, _, _ = co.attach([len(hs)] * 4)
    except pp.BlockManagerError as e:
        print(f"arena full after {len(hs)} leases: {e}; arena={co.arena()}")
        break
    run_c(h, 4)
    hs.append(h)
assert len(hs) >= 2
for h in hs:
    co.release(h)
print("pageproof coordinator demo: ok")

# ---------------------------------------------------------------------------------------------
# v0.6: speculative decoding with one drafter class, and zero-overhead scheduling (δ = 1).
# The §7 walk-through: B = 4, λ = 2, μ = 3λ = 6.
# ---------------------------------------------------------------------------------------------
sd = pp.Coordinator(8, 64, [16], [], B, b"dummy-v0.6", drafter_units=[16], max_drafts=2, zos_depth=1)


def window(plan, c, sigma):
    """The slots a device runs for `plan` in class `c` when the older tickets accepted `sigma`
    drafts: the window starts at index sigma of the listed slots (D24, E13)."""
    width = plan.num_inputs + plan.num_drafts
    assert sigma <= plan.slack
    return plan.write_slots[c][sigma:sigma + width]


def lease_l7():
    """A lease with L = 7 and c_h = 6. A repeat attach hits the published block 0 (cached = 4)."""
    h, cached, _ = sd.attach(list(range(300, 307)))
    p = sd.begin_write(h, 6 - cached)
    sd.finish_write(p.ticket)
    assert sd.inspect(h)["computed"] == 6
    return h


# A verify step with host drafts and proposal rows, then the next step planned behind it.
h = lease_l7()
v = sd.begin_write(h, 1, [11, 12], propose=True)
assert (len(v.write_slots[0]), len(v.write_slots[1])) == (3, 5)
sd.extend_deferred(h)
info = sd.inspect(h)
assert (info["len"], info["deferred"], info["reach"]) == (7, True, 14)
c2 = sd.begin_write(h, 1, propose=True, deferred_drafts=2)
assert (c2.lo, c2.slack, c2.num_inputs, c2.num_drafts) == (7, 2, 1, 2)
assert c2.producer == v.ticket and c2.input_ids == [0, 0, 0]
for n1 in range(3):
    # Whatever the producer accepts, the continuation's window is inside its listed slots.
    for i, s in enumerate(window(c2, 0, n1)):
        assert s == sd.slot_of(0, h, 7 + n1 + i)
print(f"verify + continuation planned: {len(sd.inspect(h)['queue'])} tickets, slack={sd.inspect(h)['slack']}")
# The producer accepts one draft and samples 21; the continuation accepts both of its drafts.
assert sd.finish_write(v.ticket, accepted=1, token=21) == 8
assert sd.inspect(h)["computed"] == 8
sd.finish_write(c2.ticket, accepted=2, drafts=[31, 32])
snap = sd.release(h)
assert snap[7:] == [11, 21, 31, 32]
print(f"spec decode with ZOS: committed {snap[7:]}")

# EOS at the first draft: stop orphans the continuation and ends the lease.
h = lease_l7()
v = sd.begin_write(h, 1, [11, 12], propose=True)
sd.extend_deferred(h)
c2 = sd.begin_write(h, 1, propose=True, deferred_drafts=2)
sd.finish_write(v.ticket, accepted=1, stop=True)
info = sd.inspect(h)
assert info["stopped"] and info["queue"] == [c2.ticket]
for what, bad in (("begin_write", lambda: sd.begin_write(h, 1)), ("extend", lambda: sd.extend(h, [1])),
                  ("release while an orphan is pending", lambda: sd.release(h))):
    try:
        bad()
    except pp.BlockManagerError as e:
        print(f"stopped lease, {what}: {e}")
sd.finish_write(c2.ticket, accepted=7, token=99)  # an orphan accepts any completion
assert sd.release(h)[7:] == [11]
print("pageproof v0.6 demo: ok")
