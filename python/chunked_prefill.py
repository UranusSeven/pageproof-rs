"""Chunked prefill with the pageproof coordinator.

A small scheduler loop. Each step has a budget of BUDGET tokens. Requests that are decoding take one
token each; what is left goes to prefill chunks of at most CHUNK tokens, oldest request first. A
waiting request is attached when it first gets budget, so it picks up every block published by
then. Each chunk is one ticket:

    plan = co.begin_write(h, n)           # plan positions [c, c + n) of lease h
    ...                                   # the executor runs the chunk
    c = co.finish_write(plan.ticket)      # advance the computed frontier, publish full blocks

`attach` allocates pages for the whole prompt (D2); chunks only advance the computed frontier.
A full block is published when a chunk completes it, so a request with the same prefix that is
attached during another request's prefill reuses exactly the blocks finished so far.

The executor is a stand-in for the model. Device memory maps each KV slot to the token prefix
whose KV it holds, so the executor can check that every position a step reads holds this
request's own prefix, whichever request computed it.

Run `scripts/build.sh` first, then `python3 chunked_prefill.py` from this directory.
"""
import pageproof as pp

B = 4  # tokens per KV block
BUDGET = 10  # tokens per scheduler step
CHUNK = 6  # prefill tokens per request per step

# One paged class: 8 slabs of 4 pages. No recurrent-state class, so prefix hits are on (D13).
co = pp.Coordinator(num_slabs=8, slab_bytes=64, paged_units=[16], state_units=[], block_size=B,
                    namespace=b"chunked-prefill-example")
kv = {}  # device KV memory: slot -> the token prefix whose KV the slot holds


def slot(page_table, j):
    return page_table[j // B] * B + j % B


def execute(plan, tokens):
    """Run one ticket on the stand-in model. `tokens` is the lease's input. Returns the token
    sampled after the ticket's last position; the scheduler keeps it only if that position ends
    the input."""
    pt, a, n = plan.page_tables[0], plan.lo, plan.num_inputs
    assert plan.positions == list(range(a, a + n))
    assert plan.input_ids == tokens[a:a + n]
    # Attention reads positions [0, a). Each must hold the KV of this request's own prefix.
    for j in range(a):
        assert kv[slot(pt, j)] == tuple(tokens[:j + 1]), f"position {j} holds the wrong KV"
    # Write this chunk's KV to the planned slots.
    for j, s in zip(plan.positions, plan.write_slots[0]):
        assert s == slot(pt, j)
        kv[s] = tuple(tokens[:j + 1])
    return 1000 + sum(tokens[:a + n]) % 1000


class Request:
    def __init__(self, name, prompt, max_new, arrival):
        self.name, self.prompt, self.max_new, self.arrival = name, prompt, max_new, arrival
        self.out = []  # sampled tokens
        self.h = None  # the lease, once attached
        self.done = 0  # the lease's computed frontier
        self.cached = None  # tokens reused at attach
        self.pages = None  # page table at attach

    def tokens(self):
        return self.prompt + self.out


SYSTEM = list(range(100, 118))  # an 18-token system prompt shared by r1 and r2
requests = [
    Request("r0", [7, 8, 9, 10, 11], max_new=6, arrival=0),
    Request("r1", SYSTEM + [200, 201, 202, 203, 204, 205], max_new=4, arrival=0),
    Request("r2", SYSTEM + [300, 301, 302, 303, 304], max_new=3, arrival=2),
]
waiting, running = [], []

for step in range(100):
    waiting += [r for r in requests if r.arrival == step]
    budget, batch = BUDGET, []
    # Decodes first: the newest sampled token is the input of this step.
    for r in running:
        if r.out:
            co.extend(r.h, [r.out[-1]])
            batch.append((r, co.begin_write(r.h, 1), f"{r.name} decode at {r.done}"))
            budget -= 1
    # Then prefill chunks: running requests first, then waiting ones, oldest first.
    for r in running + waiting:
        if r.out or budget == 0:
            continue
        if r.h is None:
            others = ", ".join(f"{q.name} has computed {q.done}" for q in running)
            r.h, r.cached, lease = co.attach(r.prompt)
            r.done, r.pages = r.cached, lease["tables"][0]
            assert len(r.pages) == -(-len(r.prompt) // B), "the whole prompt is allocated"
            print(f"{r.name} attached: {r.cached} of {len(r.prompt)} tokens cached "
                  f"({others or 'nothing running'})")
            waiting.remove(r)
            running.append(r)
        n = min(CHUNK, budget, len(r.prompt) - r.done)
        batch.append((r, co.begin_write(r.h, n), f"{r.name} prefill [{r.done}, {r.done + n})"))
        budget -= n
    if not batch:
        break
    print(f"step {step}: " + ", ".join(label for _, _, label in batch))
    # The executor runs the whole batch; completions arrive in issue order.
    for r, plan, _ in batch:
        x = execute(plan, r.tokens())
        r.done = co.finish_write(plan.ticket)
        assert r.done == plan.lo + plan.num_inputs
        if r.done == len(r.tokens()):  # the ticket reached the end of the input: sample
            r.out.append(x)
    for r in [r for r in running if len(r.out) == r.max_new]:
        assert co.release(r.h) == r.prompt + r.out[:-1]  # the last token was never fed back
        running.remove(r)
        print(f"{r.name} finished: {r.out}")

assert not waiting and not running
# r2 was attached while r1 was mid-prefill. r1 had computed [0, 11), so 2 full blocks were
# published; r1's chunk [11, 17) was still in flight. r2 shares those 2 pages and computes the
# rest of the system prompt itself.
r1, r2 = requests[1], requests[2]
assert r2.cached == 2 * B
assert r2.pages[:2] == r1.pages[:2]
print("chunked prefill: ok")

# ---------------------------------------------------------------------------------------------
# A hybrid model with a recurrent-state class. Every chunk reads and updates the lease's one
# state slot in place. Only the first chunk starts from the initial state (plan.init, E10), and
# prefix hits are off (D13).
# ---------------------------------------------------------------------------------------------
hy = pp.Coordinator(4, 64, [16], [64], B, b"chunked-prefill-hybrid")
prompt = list(range(300, 314))  # 14 tokens
h, cached, lease = hy.attach(prompt)
assert cached == 0
inits = []
while (c := hy.inspect(h)["computed"]) < len(prompt):
    p = hy.begin_write(h, min(CHUNK, len(prompt) - c))
    assert p.state_slots == lease["slots"]
    inits.append(p.init)
    hy.finish_write(p.ticket)
assert inits == [True, False, False]
hy.release(h)
print(f"hybrid: plan.init per chunk = {inits}")

# ---------------------------------------------------------------------------------------------
# With zos_depth=1, the next chunk can be planned while the previous one is still on the device.
# It starts where the previous chunk ends, and completions must arrive in issue order (D21).
# ---------------------------------------------------------------------------------------------
zo = pp.Coordinator(4, 64, [16], [], B, b"chunked-prefill-zos", zos_depth=1)
h, _, _ = zo.attach(list(range(400, 412)))  # 12 tokens
p1 = zo.begin_write(h, 6)  # positions [0, 6)
p2 = zo.begin_write(h, 6)  # positions [6, 12), planned before p1 completes
assert (p1.lo, p2.lo) == (0, 6)
try:
    zo.finish_write(p2.ticket)
    raise AssertionError("an out-of-order completion was accepted")
except pp.BlockManagerError as e:
    print(f"zos: completing chunk 2 before chunk 1: {e}")
assert zo.finish_write(p1.ticket) == 6
assert zo.finish_write(p2.ticket) == 12
zo.release(h)
print("pipelined chunks: ok")
