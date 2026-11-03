# Block Manager 功能契约草案 v0.2

状态：供 review 的规格草案，尚未实现或证明。
日期：2026-11-02（v0.1：2026-11-01）。
参照代码：nano-vLLM `bb823b3e06983d71485a8e1f23715ebd87d98ef8` 的 `block_manager.py`、`sequence.py`、`scheduler.py`；`shell/offload.py` 的 `prefix_keys`（链式 key 的既有实现）。

v0.2 相对 v0.1 的变更：key 改为链式 256-bit 摘要，同时是身份和索引键，碰撞以显式概率假设进入可信基础（D4、§3.3、§9）；补完整性不变量 I5b、`den` ghost 和 `Canon`/`Enc` 的具体编码（§3.3）；新增 `Index`/`Pending` 的表示与导出不变量（§3.4）；明确单线程、写入必成功、非目标与主定理/外部假设（§5、§1.1、§9.0）；C1 补 `IdentifierExhausted`，页表视图为快照；`Pending` 去掉冗余的 `table_ver`。

## 1. 目标与职责

目标是编写一份可执行、可做静态程序证明的 block manager。证明应覆盖实际方法体及其调用，而不只检查运行轨迹或验证一个独立模型。

本模块负责：物理 KV 页分配、请求页表、整块前缀复用（键为链式摘要）、容量增长、已计算前沿、执行期间的页保护、缓存发布和引用释放。

以下语义由其他模块负责：选择本轮调度哪些请求、prefill/decode 优先级、token budget、EOS 与 max_tokens、模型上下文上限、模型数值正确性、GPU kernel 与通信实现。block manager 不修改这些业务状态。

模块保证自己输出的页表和 slot 计划符合本契约；外部执行器必须按计划执行。正确性保证以固定 KV 命名空间、有效外部完成事件和正确执行器为边界。

每个 manager 对自己的物理池拥有管理权；外部代码不能绕过它改写已完成 KV 或复用其页。多个 manager 需要各自独立的物理池；跨 manager 共用同一池的协议不在本稿内。

### 1.1 v0.2 明确非目标与写入假设

以下能力不在本稿的状态机内，调用方必须另行处理，不能把它们当作已证明的性质：

- 投机解码的部分提交与被拒 draft 的截断：`finish_write` 只把前沿推进到 ticket 的 `z`，`extend` 只追加；被拒 draft 的 token 无法从 `T_h` 移除。现有 shell 的 `spec_decode`（`docs/spec/shell.md` §1.9）需要额外的原语。
- offload/store 的外部 KV 导入（adopt）：推进 `c_h` 的唯一途径是执行器对 ticket 的完成事件。`restore_prefix` 的路径需要额外的原语。
- 多线程并发调用：见 §5 的单线程假设 E3。

本版**假设写入必成功**（E4）：每个签发的 ticket 最终成功完成，没有失败完成、静默丢弃或进程终止；因此不提供 abort/回滚路径，也不承诺 GPU 故障下的进展（见 C4）。

在补齐这些原语之前，适配器不得声称完整覆盖现有 scheduler 的全部特性（尤其是 `spec_decode` 与 `store`）。

## 2. 本版拟采用的设计决定

| 编号 | 草案默认决定 | 理由或代价 |
|---|---|---|
| D1 | 每个 manager 固定 `P`、`B` 和 KV 命名空间；不使用全局可变 block size | 多进程或多个实例不会依赖同一个隐式全局值 |
| D2 | attach 时为当前全部输入 token 预留页 | 延续上游的提前分配方式；chunked prefill 只推进计算前沿 |
| D3 | 只复用连续的、已完成的整块前缀，attach 时保留最后一个逻辑块重新计算 | 延续上游生成首个输出所需的计算约定；即使输入长度恰好整除 B，也排除最后一块 |
| D4 | 缓存命中依据链式 256-bit 摘要身份；摘要同时是索引键 | key 是 `H(parent, block)` 链，每块 O(1)；身份精确性以“SHA-256 抗碰撞”为显式概率假设（E8），不使用 64-bit 实用哈希，也不做逐候选精确比较 |
| D5 | 完整前缀可读共享；写入页必须独占；本版不提供 COW | 把共享与写入的边界写进规格 |
| D6 | 核心接口采用原子 `attach` / `extend`，容量检查与修改一起完成 | 避免依赖可能过时的 can_allocate/can_append 结果 |
| D7 | 用 `begin_write` / `finish_write` 显式表示在途工作；在途请求不能 extend 或 release | 通过元数据协议保护页；实际 GPU 完成真实性仍由执行器承担 |
| D8 | 保留所有尚未被实际重用的已发布缓存条目；查找完整、命中前缀最长 | 提供明确的缓存功能承诺；比上游单值 hash 索引更强，可实现为多候选索引 |
| D9 | 空闲页选择、缓存淘汰顺序和相同 key 的页选择不作固定要求；有已被引用的命中候选时优先用它 | 保留优化空间，并确保资源充分时不会无故失败 |

D1—D9 是拟定语义，不是对上游已满足这些条件的声明。尤其 D4、D6—D8 需要调整实现和接口；本稿不承诺对旧 API 逐函数兼容。

## 3. 抽象状态

### 3.1 固定配置

- `P >= 1`：物理页数，`PageId = {0,...,P-1}`。
- `B >= 1`：每个物理页的 token 槽数。
- `Namespace`：决定缓存可复用性的配置身份，一个不透明字节串。最终字段表应覆盖模型与权重版本、适配器、位置编码/scaling、attention 语义（含滑窗）、B、KV 数据类型与布局，并建议与 `Engine.store_identity()` 对齐。v0.2 先用 dummy（实现可传固定字符串，如 `"dummy-v0.2"`）；完整性仍是调用方的义务（E6），字段表留到 v0.3。
- `Token`：合法 token ID 的类型；序列有限，索引从 0 开始。

抽象规格采用数学整数。具体实现必须证明页号、长度、计数和地址的机器整数运算不溢出；构造时拒绝无法表示的配置。CUDA 当前要求的 B 倍数、int32 slot 上限等由对应实现/适配器另加明确约束，不能隐含忽略。

### 3.2 可变状态

| 符号 | 含义 |
|---|---|
| `Req[h]` | 已 attach 的请求租约，含不可原地修改的输入序列 `T_h`、页表 `M_h`、计算前沿 `c_h`、可选的 pending ticket |
| `F` | 当前没有请求引用的物理页集合；包含仍保有可复用数据的空闲缓存页 |
| `ref[b]` | 物理页 b 被多少个活动租约引用 |
| `key[b]` | 页 b 的可复用缓存身份（链式 256-bit 摘要），或 None |
| `Index[K]` | 已发布 key 为 K 的全部物理页候选 |
| `Pending[t]` | 一次已提交但尚未完成的计算，包括租约、原始前沿 `a`、区间终点 `z` 和执行计划 `plan` |
| `V` | 证明使用的 ghost KV 来源标记；记录槽所对应的 Namespace 与完整因果 token 前缀 |
| `den` | 证明使用的 ghost：摘要到 `(Namespace, 完整因果前缀)` 的偏函数；链式 key 的语义由它给出 |

`den` 的定义域恰为链输出 `{Seed(ns)} ∪ {K(h,i)}`；理想模型下单射，具体实例由 E8 保证。它不进入可执行状态。

请求 handle 和执行 ticket 使用互不混淆的类型，并绑定 manager 与相应代次。已失效 handle/ticket 不能在后续对象上重新生效。若具体实现的计数空间耗尽，应安全拒绝新操作，不能回绕复用。

本稿中的请求代表 block manager 的租约，不等同于 scheduler 的 WAITING/RUNNING/FINISHED 状态。scheduler 仍管理其业务请求；释放租约不等于删除用户请求或输出。

### 3.3 语义约定

令 `L_h = |T_h|`，`m_h = ceil(L_h/B)`。

页表 `M_h[i]` 表示第 i 个逻辑块对应的物理页。token 位置 j 的槽地址为：

\[
slot(h,j)=M_h[\lfloor j/B\rfloor]\cdot B+(j\bmod B).
\]

`c_h` 是已完成计算的连续前缀长度：位置 `[0,c_h)` 有有效 KV，`[c_h,L_h)` 尚未全部完成。容量已经预留，不意味着 KV 已经有效。

逻辑块 i 的 cache key 是链式 256-bit 摘要。令 `H` 为 256-bit 抗碰撞哈希（实现用 SHA-256），`Tag` 为方案版本（如 `"mg-block-key-v1"`），`Canon` 为 Namespace 的规范编码，`Enc` 为 B 个 token 的定宽编码：

\[
\begin{aligned}
Seed(ns) &= H(Tag \,\|\, 0x00 \,\|\, Canon(ns))\\
K(h,0) &= H(Tag \,\|\, 0x01 \,\|\, Seed(ns) \,\|\, Enc(T_h[0:B]))\\
K(h,i) &= H(Tag \,\|\, 0x01 \,\|\, K(h,i-1) \,\|\, Enc(T_h[iB:(i+1)B]))
\end{aligned}
\]

**编码（E7）。** `Canon(ns)` 把 namespace 字节串编码为 `u32 len || ns_bytes`（v0.2 的 namespace 是不透明字节串；字段化后按固定顺序、每字段 `u32 tag || u32 len || bytes`）。`Enc(blk)` 把 B 个 token 各写成 4 字节小端 uint32，定宽拼接，恰好 `4B` 字节。父摘要固定 32 字节，`Tag` 与 `0x00`/`0x01` 做域分隔，因此 `Tag || 0x01 || parent || Enc(blk)` 的切分唯一。这条唯一性不依赖哈希（E7）；哈希只负责 E8。反例：变长 token 直接拼接、用分隔符连接字符串、JSON 键序不定，都会让两个不同前缀编码成同一个字节串，碰撞概率是 1，不是 `2^-256`。

`K(h,i)` 只对完整块 `(i+1)B <= L_h` 定义；不完整的尾块没有 key，也永远不发布。key 的语义是完整因果前缀 `(Namespace, T_h[0:(i+1)B])`，由 ghost `den` 给出；链式构造只是它的 O(1) 表示。前序不同必须改变所有后续 key：链式构造保证这一点，而“仅当前块 token”“仅 token hash”或“长度相同”都不充分。

在理想哈希模型（`H` 单射）下，链式引理成立：

\[
K(h,i)=K(h',i') \iff ns=ns' \land i=i' \land T_h[0:(i+1)B]=T_h'[0:(i+1)B].
\]

具体实例（SHA-256）中该等价式以概率 `>= 1 - \epsilon` 成立，`\epsilon <= Q^2/2^{257} + Q/2^{256}`，`Q` 为部署期内 key 的生成与比较次数（E8）。`den` 在链输出上单射（理想模型），具体实例同样由 E8 保证；于是 `den(K(h,i)) = (Namespace, T_h[0:(i+1)B])` 就是 key 的语义。

key 的生命周期等于页的生命周期：摘要存在页上，`Index` 条目随 key 的撤销而移除；没有 intern 表、祖先链或 GC。释放但未被重用的页保留 key（C5），因此总元数据是 O(P) 个摘要。链头（最后一个已发布完整块的 key，或 `Seed(ns)`）可以让 `finish_write` 增量计算新块的 key；它是实现细节。

### 3.4 Index 与 Pending 的表示

**Index。** `Index : Map<Key, Set<PageId>>`，`Index[K] = {b | key[b] = K}`（I8）。它是 `key` 的反关系，只覆盖已发布页；`F` 中既有已发布（仍可从 Index 查到）也有未发布的页，二者靠 `key[b]` 区分。同一个 key 可以对应多个物理页；`attach` 在每个命中位置优先选 `ref>0` 的候选，否则选一个 `ref=0` 的候选重新激活。条目随 `key` 撤销而移除（C1/C2、I7）；`release` 不删条目（C5）。总条目数 ≤ P。

**Pending。** `Pending : Map<TicketId, PendingRec>`，`dom(Pending)` 与 `Req[·].pending` 双向对应（I9）：

```
PendingRec = {
  lease : Handle,          // h
  a     : Nat,             // 发起时的 c_h
  z     : Nat,             // a + n
  plan  : ExecutionPlan,   // begin_write 返回的不可变计划
}
```

`plan` 至少含 `ticket`、`h`、`input_ids = T_h[a:z]`、`positions = [a..z-1]`、`write_slots = [slot(h,j) | j in [a,z)]`、`[0,z)` 的页映射和 `B`。由于单线程（E3）且 pending 期间禁止 `extend`/`release`（I9），`T_h`、`M_h` 和页表内容在 ticket 存活期间不变；因此不需要额外的版本号。导出不变量：

```
Req[h].pending = Some t  ⇔  t ∈ dom(Pending) ∧ Pending[t].lease = h
t ∈ dom(Pending)  ⇒  c_h = Pending[t].a  ∧  T_h、M_h 自 ticket 签发后未变
```

`finish_write` 只接受 `t ∈ dom(Pending)` 且绑定匹配的 ticket；原子地删除条目、清 `Req[h].pending`、令 `c_h = z`、更新 ghost `V`、发布新完整块并更新 `Index`。完成事件只消费一次。

## 4. 全局不变量 Valid(S)

以下性质在构造完成以及每个公开方法返回时均成立。

**I1 页域与页表。** 所有页号都在 `[0,P)` 内。每个活动租约的页表内部无重复；`1 <= L_h <= P*B` 且 `|M_h| = ceil(L_h/B)`。

**I2 引用精确。**

\[
ref[b]=|\{h\in dom(Req): b\in set(M_h)\}|.
\]

不允许负引用计数、遗漏引用或额外引用。引用计数表示请求租约引用；pending 的保护通过“租约不能释放”实现，不额外虚增这一个计数。

**I3 空闲精确。** `b in F <=> ref[b]=0`。有引用的页绝不被重新分配为可写页。空闲只表示可回收，不能解释为数据不存在或已清零。

**I4 有效前沿。** `0 <= c_h <= L_h`。对每个 `j<c_h`，`V[slot(h,j)]` 都与 `Namespace, T_h[0:j+1]` 对应。此处是 KV 来源性质；浮点数值正确性是执行器的外部规格。

**I5 已发布缓存真实。** `key[b] != None` 时，存在 `q >= 1` 与长度 `qB` 的前缀 `τ`，使 `den(key[b]) = (ns, τ)`，且页 b 承载 `τ` 的最后一个完整块的有效 KV。一个 key 标识一个确定的逻辑块位置与上下文。

对任何引用已发布页 b 的活动租约 h，若 `M_h[i]=b`，还必须有 `key[b]=K(h,i)` 且 `c_h >= (i+1)B`。这项约束也适用于 ref=1 的页，保证已发布页不会被同一个请求重新当作未计算尾部写入。

**I5b 完整即发布。** 对每个活动租约 h 与 `i < |M_h|`，若 `(i+1)B <= c_h`，则 `key[M_h[i]] = K(h,i)`。I5 只给出“已发布 ⇒ 正确”；I5b 给出反向，使 D8 的“查找完整”成为状态性质，而不是要靠重放历史才能得到的结论。

**I6 共享只读。** 若 `ref[b]>1`，则 b 有已发布 key；对每个引用者 h，该 key 等于 b 在 h 中对应的 `K(h,i)`，并且 `c_h >= (i+1)B`。因此任何引用者都不会把 b 当作未计算尾部写入。

**I7 发布后不可覆盖。** key 非空的页不允许在原地被任何写计划覆盖。只有 `ref[b]=0`、选中为新页且已撤销 key/index 后，才可开始新一轮写入。

**I8 索引双向一致。** `Index[K] = {b | key[b]=K}`，忽略空集合的物理存储形式。失效页不被查到；未淘汰的已发布候选可被找到。在 E8 下，摘要相等视为前缀相等；`Index[K]` 的候选无需再做逐 token 比较。

**I9 在途保护。** 每个活动租约最多一个 pending ticket；请求的 pending 字段与 Pending 表双向对应。ticket 绑定真实租约、输入快照和 `[a,z)` 区间，其中 `a=c_h`、`0<n=z-a<=L_h-c_h`；所需页在完成前保持引用。所有 pending 写计划均在合法槽范围内，写页独占且未发布，不同 ticket 的写槽不重叠。ticket 存活期间 `T_h`、`M_h` 不变，且 `c_h = a`（导出不变量，见 §3.4）。

**I10 不可变配置。** P、B 和 Namespace 在 manager 生命周期内不变；执行计划的地址均由该实例的 B 计算。

## 5. 通用方法约定

实际实现应封装内部状态：外部代码只能通过已验证的方法更新它。不能把 `Valid(S)` 当成一个任意外部 Python 调用者永远自觉遵守的条件。

每个方法都必须满足：

1. 入口状态 Valid 时，正常返回状态也 Valid。
2. 所有有限合法输入上方法终止；无越界、计数溢出或未规定的状态修改。
3. 声明的错误结果具备强失败原子性：`S'=S`，包括页表、前沿、引用计数、索引、pending 和 ID 分配状态。
4. 未涉及租约的输入、页表、前沿和 pending 保持不变；被多个租约引用的已有 KV 不得改变。
5. 外部可观察输出满足各方法的功能后置条件，而不只是“状态仍合法”。

这些失败原子性要求针对规定的输入/容量/阶段错误。进程终止、运行库 OOM、硬件故障不在本版状态机承诺中。

本稿假定方法在单线程中顺序调用（或由调用方串行化），不声明多线程线性化（E3）。链式 key 的计算是纯函数，不修改状态；`Index` 的修改只随成功的方法发生，因此 §5 第 3 条的强失败原子性覆盖页表、引用、`Index` 和 ID 分配状态，不新增 key-store 状态。

## 6. API 契约

### C0. create(P,B,Namespace) -> Result<Manager>

**成功：** 页全集固定；F 为全部物理页；Req、Pending 和 Index 为空；每页 ref=0、key=None；Valid 成立。

**失败：** 配置非正或机器表示不安全时，返回明确 ConfigError，不产生可用 manager。

### C1. attach(T) -> Result<(Handle, cached_tokens, PageTableView)>

用途：首次处理请求，或请求被抢占释放后，按保留的完整输入重新取得资源。

**有效输入：** T 是非空的合法 token 序列，`L<=P*B`；其 Namespace 为本 manager 固定配置。超长返回 RequestTooLarge，非法或空序列返回 InvalidArgument。

**前缀与容量的精确定义：** 令 `m=ceil(L/B)`。从调用前状态计算：

\[
k^*=\max\{k\in[0,m-1]\mid\forall i<k,\ Index[K(h,i)]\ne\varnothing\}.
\]

`K(h,i)` 由 §3.3 的链从 `Seed(ns)` 递增计算；尾块没有 key，因此上界 `m-1` 与“最后一块重算”一致。

令 u 为这 k* 个前缀位置中，至少有一个候选的 `ref>0` 的位置数。所需从空闲集合取出的最少页数是：

\[
d=m-u.
\]

**成功充要条件：** 对有效输入且 handle 空间未耗尽，`|F|>=d` 时必须成功；`|F|<d` 时必须返回 NoCapacity。不能因为某个较差候选选择而在有可行计划时返回 NoCapacity。handle 空间耗尽时返回 `IdentifierExhausted`（与 C3 一致），状态不变。

**成功后置条件：**

- 返回新鲜有效 handle h，`T_h=T`，`|M_h|=m`，`c_h=k^*B`，无 pending。
- 对 `i<k*`，页表项选自调用前对应 Index；若有已引用候选，则选择已引用候选，否则重新激活一个空闲缓存候选。
- 对 `i>=k*`，分配互不相同的空闲页；这些页不能覆盖本次选中的缓存命中页。
- 所有旧引用计数按新增页表项精确加一。新取出的页从 F 移除。
- 新分配为可写页的旧 key 被撤销，对应 Index 项正确移除。命中页的 key 与 KV 不变。
- 其他活动租约内容和有效 KV 不变。返回的 PageTableView 是不可修改的快照；后续 extend 不改变已返回的视图。

该容量公式区分“复用活跃页”和“复用空闲缓存页”：前者节省一个空闲页名额，后者仍消耗一个名额。找到缓存不等于不需要物理容量。

attach 不隐式抢占其他请求，不淘汰有引用的页，不推进 GPU 计算。固定哪一页被淘汰不属于本契约。

### C2. extend(h, suffix) -> Result<PageTableView>

用途：把后续需要计算的 token 追加到租约，并原子地预留其容量。

**调用阶段：** h 有效、无 pending，且 `c_h=L_h`；即当前输入已经算完。未完成输入时返回 InvalidPhase，在途时返回 Busy。suffix 非空且 token 合法；不允许修改已有前缀。

令旧长度 L、旧页数 m，`L'=L+|suffix|`，`m'=ceil(L'/B)`，`d=m'-m`。

**成功充要条件：** 对有效阶段且 `L'<=P*B`，当且仅当 `|F|>=d` 时成功。`L'>P*B` 返回 RequestTooLarge。空间不足返回 NoCapacity，旧输入和页表都保持不变。

**成功后置条件：**

- `T'_h=T_h ++ suffix`，`c'_h=c_h`，旧输入前缀未变。
- 旧页表保持为新页表的前缀；新增恰好 d 个不同的空闲页，各 ref=1、key=None。
- 已有 KV、已发布 key 及其他请求不变；新占用页原有缓存身份被正确撤销。
- 不查找新增后缀的其他 prefix cache，不复制共享页。若旧尾块仍有未使用槽，该尾块必为独占且未发布，后续写入可使用这些槽。

若最终采样 token 不需要再参与一次模型输入，scheduler 可以直接记录输出并 release，无须 extend。若 extend 失败，调用者需保留外部 token 并选择等待/抢占等策略；本模块不丢弃或重采样它。

### C3. begin_write(h,n) -> Result<(Ticket, ExecutionPlan)>

用途：为一次 chunk 或一次 decode 生成不可变执行计划，标记资源在途。

**有效调用：** h 有效，无 pending，`0<n<=L_h-c_h`。无剩余输入或越界 n 返回 InvalidArgument；已有 pending 返回 Busy。

若具体实现的新鲜 ticket 表示空间耗尽，返回 IdentifierExhausted 且状态不变；不能回绕并接受旧 ticket。

令 `a=c_h`，`z=a+n`。

**成功后置条件：**

- 返回新鲜 ticket，绑定 h、输入快照、区间 `[a,z)`。
- `input_ids=T_h[a:z]`，`positions=[a,...,z-1]`。
- 每个位置 j 的写槽严格等于 `slot(h,j)`；共 n 个槽，互异且在 `[0,P*B)` 内，写页均为独占且无已发布 key。
- 计划明确列出所需上下文 `[0,z)` 的页映射；旧前缀 `[0,a)` 已有效，新区间的读依赖由执行器的因果计算语义满足。
- manager 记录 pending；页表、ref、F、key、Index 和 c 不变；不能把“已提交”计作“已完成”。

计划是数据与元数据承诺，不证明 GPU 已执行。CPU adapter 不得自行用另一个 B 重算地址或更改计划。

### C4. finish_write(ticket, completion) -> Result<ComputedFrontier>

用途：在一次计算真实完成后，推进有效前沿，发布新完整块。

**协议条件：** ticket 是本 manager 当前有效的 pending ticket。未知、过期、重复使用或属于其他 manager 的 ticket 返回 InvalidTicket，不修改状态。

**外部前提 Completed(ticket)：** completion 来自执行器，确认该 ticket 对应的读写已完成，执行使用了计划中的输入/地址，且新 KV 满足执行器规格。如何从 CUDA/NCCL 得到这一事实不由本模块证明；不能把一个调用者随意提供的 bool 当成已证明的物理完成。

**成功后置条件：**

- 对绑定租约 h，`c'_h=z`，pending 被消耗一次；输入与页表不变。
- ghost V 中 `[a,z)` 的来源与 ticket 的固定前缀一致；其他已有效槽不变。
- 对所有满足 `a<(i+1)B<=z` 的新完成整块 i，发布 `K(h,i)` 并更新 Index；不能发布部分块。`K(h,i)` 从链头（最后一个已发布完整块的 key，或 `Seed(ns)`）顺序计算；链头可以用 `floor(c_h/B)-1` 处的 key 维护，但它是实现细节。
- 已有只读缓存页、ref、F 及其他请求状态不变。不同物理页具有相同 key 时，索引保留全部候选。

本版假设写入必成功（E4），因此没有“失败完成”分支，也不提供 abort；`finish_write` 只处理成功完成。若执行器无法保证这一点，必须先停止相关执行并证明安全，属于后续扩展。

### C5. release(h) -> Result<TokenSnapshot>

用途：完成请求或抢占时，释放租约的全部引用。

**有效调用：** h 有效且无 pending。存在 pending 返回 Busy；失效 handle 返回 InvalidHandle，重复 release 不能产生第二次减引用。

**成功后置条件：**

- 返回租约持有的完整输入快照，方便调用者保留请求逻辑状态；不删改用户的输出序列。
- 从 Req 删除 h，使 h 永久失效。
- 对原页表中的每个 b 恰好减一次 ref。减为 0 的页进入 F；仍有其他引用的页不进入 F。
- 已发布 key、Index 与 KV 保留，以供后续复用；未完成的部分块仍不可作为缓存命中。
- 其他活动租约的输入、页表、有效前沿及 pending 不变。释放本身不清零 KV、不驱逐活跃页，也不决定 scheduler 状态。

释放完成后的同一个业务请求，可以拿返回的 T 再次 attach，获得新 handle；这是抢占恢复路径。

### C6. inspect(h) -> Result<RequestView>（只读辅助接口）

返回输入长度、已计算前沿、页表不可变视图、pending 状态及本实例 B。无副作用。

提供可选的 `slot_of(h,j)` 时，只保证对 `0<=j<L_h` 返回正确的已分配地址；只有 `j<c_h` 才能同时宣称该槽的 KV 已有效。非法 handle/索引返回明确错误。

v0.2 不要求提供 can_allocate/can_append。若以后增加 preview，它只能是只读建议或绑定状态版本的计划；不能无条件保证后续状态变化后仍可执行。

## 7. 必须 review 的边界案例

| 场景 | 预期行为 |
|---|---|
| 空输入 | attach 返回 InvalidArgument，状态不变 |
| 单块输入；或输入恰好 B 个 token | attach 的 k*=0；最后一块仍需要计算 |
| 输入恰好 2B，前两个块均已有缓存 | 最多复用第一块，不能把全部输入标成已算完 |
| prefix hit 指向活跃页 | 加引用，可减少所需空闲页；禁止改写该页 |
| prefix hit 指向 ref=0 的缓存页 | 重新激活并占用一个空闲页名额 |
| 相同当前块 token，但前序上下文不同 | 链式 key 不同，不得复用 |
| 尾块未满（L 不是 B 的倍数） | 该块没有 key，不进 Index；即使 token 相同也不命中 |
| 尾块被 extend 补齐后再 finish | 此时才发布；之前不发布部分块 |
| 两个请求先后 attach 同一 T | 第二个复用已发布页并加引用；两者都从 k*B 开始计算 |
| 相同 key 有多个候选 | 有活跃候选优先用活跃候选，避免可服务请求被错误拒绝 |
| 只有一个空闲页，需要两个新页 | NoCapacity，不能先分配一页再留下半完成状态 |
| L=B，已计算完，追加一个 token | 新增一页；新 token 的逻辑 offset 为 0 |
| L=B-1，已计算完，追加一个 token | 无须新增页；旧尾块仍独占，后续只写新槽 |
| 在途 ticket 尚未完成 | release/extend 返回 Busy，旧页不能被回收 |
| 同一个 completion 到达两次 | 第二次 InvalidTicket，不重复推进前沿或发布 |
| 被抢占后旧 handle 或旧 ticket 到达 | 拒绝，不作用于新租约 |
| B=512，执行位置 j=256，M[0]=0 | slot 必须为 256，不能依赖 Sequence 默认 B=256 |

## 8. 与上游方法的对应及有意变更

| 上游接口 | 草案接口 | 变更 |
|---|---|---|
| BlockManager 构造 | create | 固定实例配置，验证表示范围 |
| can_allocate + allocate | attach | 一次原子操作；不依赖外部传入 num_cached_blocks |
| Sequence.append_token + can_append + may_append | extend | 输入快照与容量原子增长；需要 scheduler adapter 配合 |
| seq.num_scheduled_tokens 与 runner 准备 | begin_write | 生成实例一致的地址计划，并记录在途保护 |
| hash_blocks + 更新 num_cached_tokens | finish_write | 统一在完成后提交前沿和缓存发布 |
| deallocate | release | 禁止在途释放；失效 handle 防止双重释放 |
| compute_hash | 缓存身份 | 链式 256-bit 摘要，既是身份也是索引键；以抗碰撞假设进入 E8（§9） |

这是面向可证明实现的新接口，不能未经适配直接替换原对象。特别是 `Sequence` 中不能再存在可随意独立修改的权威页表/缓存前沿；若需要镜像，只能从核心导出，并证明 adapter 使用一致的版本。

## 9. 后续实现必须交付的证明

### 9.0 主定理与外部假设

**主定理。** 对任意合法 trace 的每一步，若执行器按 `begin_write` 返回的计划执行，则：

(a) 计划中的写槽恰为 `slot(h,j)`（`j in [a,z)`），在 `[0,P*B)` 内互异；
(b) `[0,a)` 的每个槽在 ghost `V` 中对应 `(Namespace, T_h[0:j+1])`；
(c) `finish_write` 后 `[a,z)` 的每个槽更新为对应前缀，且每个新发布块 i 满足 `den(key[M_h[i]]) = (Namespace, T_h[0:(i+1)B])`；
(d) `Valid(S)` 保持，各方法的 frame 条件成立，错误路径满足 §5 第 3 条的强失败原子性。

**外部假设。** 以下不证明，但必须列出，并在已验证的调用链上检查；其中 E8 是本版唯一的密码学假设。

| 编号 | 假设 | 不成立时的后果 |
|---|---|---|
| E1 | 完成事件真实：执行器确认读写完成，且使用了计划的输入与地址 | 前沿推进到未写或写错的 KV |
| E2 | KV 只依赖前缀：数值与批次组成、切块方式无关（在容差内） | 共享页的 ghost `V` 不再成立 |
| E3 | 单线程顺序调用（或调用方串行化） | 不变量在并发下失效 |
| E4 | 写入必成功：每个签发的 ticket 最终成功完成；没有失败完成、静默丢弃或进程终止 | pending 永不清空，页被永久占用 |
| E5 | 执行器使用计划中的 slot 与实例的 B，不重算地址 | 写错页或槽 |
| E6 | Namespace 完整：最终字段表覆盖权重、dtype、B、KV 格式/布局、rope/scaling、attention 语义、adapter；v0.2 用 dummy 字节串，完整性由调用方负责 | 不同语义共享 key，静默错误复用 |
| E7 | `Canon`/`Enc` 按 §3.3 的规范编码：定宽 uint32 token、长度前缀字段、固定字段序、域分隔 | 结构性碰撞（概率 1），E8 兜不住 |
| E8 | SHA-256 抗碰撞；部署期内 `Q` 次 key 生成/比较的碰撞概率 `<= Q^2/2^257 + Q/2^256` | 跨请求错误复用 KV（多租户下是数据泄露） |

### 9.1 证明义务

1. **初始化正确：** create 成功后 Valid。
2. **逐方法保持：** 对每个真实方法体证明 Valid 保持及 C0—C6 的功能、错误和 frame 条件。
3. **分配充分性：** attach 的 k*、u、d 计算符合定义；正确选择候选时，容量充分必成功。
4. **地址与隔离：** slot 范围、同请求无别名、跨 pending 写入不冲突、共享页不被写。
5. **缓存可靠性：** 链式 key 的规范实现（`Canon`/`Enc`/`Tag`/域分隔）与 Index 双向一致；发布条件正确；回收撤销身份先于新用途写入；在理想哈希模型下证明链式引理（§3.3），把 E8 作为具体实例的唯一密码学假设。
6. **协议正确：** handle/ticket 失效、完成单次消费、在途页不被回收；证明执行器接口的前提在已验证调用链上成立，或列为显式外部假设（E1、E2、E5）。
7. **终止与表示：** 所有循环终止；机器整数、数组和集合操作安全；验证器 UNKNOWN 或超时不是通过。
8. **部署连接：** 运行经验证的实现或其受信编译输出，不将手工重写的另一版本视为自动继承证明；摘要实现与 `Canon`/`Enc` 的规范性必须与证明中的定义逐字节一致。

### 9.2 可信基础

1. E8（SHA-256 抗碰撞及 ε 界）；
2. E6（Namespace 完整性）与 E7（规范编码）：设计义务，不是概率假设；
3. 受信编译输出（§9.1 第 8 条）；
4. E1/E2/E5（执行器接口）；E3/E4 是部署假设（单线程、写入必成功），不进入方法体证明。

证明辅助引理、循环不变量和数据结构可以由 agent 设计，但不得用新 assume、公理、跳过函数体或削弱前后条件来冒充完成证明。E1—E8 是显式列出的外部假设，不能作为新增 assume 的入口。

建议分三步实现和证明：先做无共享的分配/增长/释放；再加入链式摘要前缀缓存和共享；最后接入 ticket/完成协议和 Python runner adapter。每步保持同一套外部功能目标，不能把被暂缓的性质算作已证明。

## 10. 已定与待确认

v0.2 已定：

- key 是链式 256-bit 摘要：`Seed(ns)` 起链，逐块追加该块 token；摘要同时是身份和索引键。尾块没有 key。身份精确性以 E8 的显式概率假设为前提（§3.3、D4）。
- 不变量保留 ghost `den`，使“key 描述哪个前缀”可以陈述；具体层每页只存 32 字节摘要，无 intern 表、无 GC（§3.2、I5）。
- `Canon`/`Enc` 采用 §3.3 的规范编码；`Tag` 为方案版本；摘要 256-bit、不截断。
- 单线程（E3）、写入必成功（E4）；spec-decode、offload、多线程为非目标（§1.1）。
- Namespace 先用 dummy 字节串（E6），字段表留到 v0.3。
- `Pending` 不存 `table_ver`；用 §3.4 的导出不变量代替。
- 继续 D2/D3：attach 为全部输入预留、最后一块重算；D6/D7 的原子接口和显式在途保护不变。

仍待确认（v0.3 或实现前必须定）：

- Namespace 的真实字段表（E6）以及与 `Engine.store_identity()` 的对齐。
- 是否与 `shell/offload.py` 的 `prefix_keys` 共用身份：共用需对齐 Tag、namespace 字段和 `grain == B`；不共用就明确写成两套。
- 投机解码/offload 的原语（`truncate`/`commit`、`adopt`）：v0.3 是否补。
- 验证工具链与仓库名（文档外）。

另一条明确边界是：本稿证明的是资源/来源/地址与协议。GPU 是否真正按照计划完成，以及数值 KV 的正确性，需要执行器的独立契约。该边界不能通过给 ghost V 赋值而被视为已经证明。
