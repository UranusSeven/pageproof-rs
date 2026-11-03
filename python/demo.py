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
