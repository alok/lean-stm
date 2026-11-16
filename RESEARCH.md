# PL Research Synthesis, Prover-Guided Autoresearch & Empirical Benchmarks

This document records the Programming Languages (PL) literature synthesis, prover-guided protocol discoveries, and 16-core Apple M4 Max benchmark results for `lean-stm`.

---

## 1. PL Literature Survey: Modern Approaches to STM (2005–2026)

| Lineage | Key Mechanism | Strengths | Weaknesses | Role in `lean-stm` |
| :--- | :--- | :--- | :--- | :--- |
| **Composable Haskell STM** (*Harris, Marlow, Peyton Jones, Herlihy, PPoPP 2005*) | `STM` monad, `retry` blocking on read-set, left-biased `orElse` (`<|>`) | Compositional concurrency without lock-order deadlocks; type-level `IO` isolation | Original GHC runtime used coarse/per-TVar locking without MVCC or snapshot extension | Core surface API (`STM/Core.lean`), nested savepoints, `TQueue`, split-counter `TBQueue`, `TChan` |
| **TL2** (*Dice, Shalev, Shavit, DISC 2006*) + **LSA** (*Riegel, Felber, Fetzer, DISC 2006*) | Global version clock + per-object versioned write locks + Lazy Snapshot Extension | Disjoint-access parallel commits; 0-lock/0-clock read-only fast path; LSA eliminates spurious aborts | Central clock `fetch_add` contention at high core counts; long readers can starve under heavy writes | Default `Protocol.tl2Lsa` + Post-Lock `GV4` CAS Clock + mechanized simulation proof (`STM/Verify/TL2.lean`) |
| **Fraser EBR** (*Fraser, PhD 2004*) + **Perceus RC** (*Reinking et al., PLDI 2021; Ullrich & de Moura*) | 3-epoch deferred reclamation paired with Lean's `lean_mark_mt` atomic refcounting | Eliminates `IO.Ref.get`'s `exchange(nullptr)` double-RMW read bottleneck; zero cache-line writes on scalar reads | Requires careful thread-exit orphan draining | Native C++20 `EbrThreadGuard` in `c/lean_stm.cpp` |
| **NOrec** (*Dalessandro, Spear, Scott, PPoPP 2010*) | Single global sequence lock + value-based snapshot validation | Zero per-object lock/version metadata; automatic value-based snapshot extension | Serializes disjoint write commits on one global seqlock at high core counts | Selectable `Protocol.norec` + ABA-free Perceus pointer validation + mechanized proof (`STM/Verify/NOrec.lean`) |
| **JVSTM / Multi-Version STM** (*Fernandes & Cachopo, PPoPP 2011; Perelman et al., PODC 2010*) | Bounded per-cell version history rings read at pinned `rv` | Wait-free read-only transactions **never abort**, even under 100% write storms | Naive lock-ignoring lookup causes fractured reads! | Inline 8-slot version ring (`atomicallyReadOnly` + adaptive fallback) + mechanized Lock-Before-Clock proof (`STM/Verify/MVCC.lean`) |
| **OCaml 5 `kcas`** (*Karvonen & Sivaramakrishnan, 2023–2024*) | Obstruction-free read-only compares + scheduler-friendly awaiters (`retry`) | Zero busy-waiting; clean separation of optimistic fast path and parking slow path | Full $k$-CAS descriptors add indirection on write-heavy paths compared to 128B TL2 cells | Dekker-synchronized `seq_cst` WaitQueues (`has_waiters` fast flag avoids mutex on uncontended commits) |
| **STO — Software Transactional Objects** (*Herman et al., EuroSys 2016*) & **CCSTM** (*Bronson et al., PPoPP 2010*) | Data-structure-aware sharding & predicate tracking | Eliminates whole-container false conflicts while retaining multi-key serializability | Requires container-level engineering | 64-stripe `TMap` (`STM/Data/TMap.lean`) & split-counter `TBQueue` (`STM/Data/TBQueue.lean`) |
| **Opacity & TMS2 Verification** (*Guerraoui & Kapalka, PPoPP 2008; Doherty et al., 2009/2013; Lesani et al., POPL*) | Intermediate `TMS2` specification automaton + forward simulation | Guarantees even *live/aborted* transactions never observe inconsistent state | Historically required thousands of lines of manual Isabelle/Rocq scripts | Zero-`sorry` Lean 4 proofs (`Opacity.lean`, `TMS2.lean`, `TL2.lean`, `NOrec.lean`, `MVCC.lean`) + 1-line `stm_verify` tactic |

---

## 2. Prover-Guided Autoresearch Discoveries

Using Lean 4's kernel alongside live multi-core stress testing produced **four concrete algorithmic & specification discoveries**:

### Discovery 1: Lean 4 `IO.Ref.get` Double-`exchange(nullptr)` Read Serialization
Inspecting `~/lean4/src/runtime/io.cpp:1450–1468` revealed that multi-threaded `IO.Ref.get` executes `val_addr->exchange(nullptr)`, increments `m_rc`, and executes `val_addr->exchange(val)`. Two threads concurrently *reading* a shared `IO.Ref` dirty the cache line twice per read and spin-wait on `nullptr`. Replacing this with **Fraser 3-Epoch EBR + `lean_mark_mt`** + 128-byte Apple-Silicon-aligned `TVarCell`s turns `TVar` reads into pure `memory_order_acquire` loads with zero shared cache-line writes.

### Discovery 2: Cross-Protocol Fractured Snapshots & The Lock-Before-Clock MVCC Theorem
When testing `atomicallyReadOnly` (8-slot inline MVCC ring) concurrently against 8 bank-transfer writer threads (`total = 8000`):
- `Protocol.tl2Lsa` and `Protocol.tl2Gv1` maintained `total == 8000` across 100% of mid-flight audits.
- `Protocol.norec` initially failed mid-flight with **`expected 8000, got 7984`** (`8000 - 16`, a single half-applied transfer of `16`!).
- **Root Cause & Formalization ([`STM/Verify/MVCC.lean`](STM/Verify/MVCC.lean))**:
  - We proved `naive_mvcc_violates_opacity`: if a writer increments `g_tl2_clock` to `wv` without already holding per-cell lock bits on its *entire* write-set, an MVCC reader at `rv = wv` observes `acc0` post-transfer (`984`) and `acc1` unlocked pre-transfer (`1000`), violating `ConsistentWithSnapshot`.
  - We proved `lock_before_clock_mvcc_sound`: enforcing $t_{\text{lock}}(W, x) < t_{\text{clk}}(W) < t_{\text{publish}}(W, x)$ across *all* protocols (`commit_tl2` and `commit_norec`) guarantees $t_{\text{publish}}(W, x) < t_{\text{obs}}(R, x)$ whenever $wv \le rv$ and $R$ observes $x$ unlocked at $t_{\text{obs}} > t_{\text{snap}}$. Adding `fetch_or(1ULL)` prior to `g_tl2_clock.fetch_add(1)` in `commit_norec` eliminated fractured snapshots completely.

### Discovery 3: Safe Post-Lock `GV4` CAS Clock Elision vs Naive Clock Reuse
In naive `GV4`, reusing a concurrent writer's clock bump *before* holding all write locks allows a writer to stamp a cell with `wv <= reader.rv` *after* the reader already read an older version of that cell. By moving the `CAS(c, c + 1)` **strictly after** sorted write-lock acquisition (`commit_tl2` Step C2) and proving `TL2State.gv4_post_lock_strictly_advances` (`old_ver <= c < c'`), colliding writers safely share `wv = c'` while preserving Lock-Before-Clock opacity.

### Discovery 4: Automated Invariant Debugging via `stm_verify`
While verifying the 3-philosopher atomic fork-acquisition model in [`STM/Verify/Examples.lean`](STM/Verify/Examples.lean), `stm_verify` (`simp [stm_simp]` + path `split` + `omega`/`grind`) immediately rejected an under-specified invariant that omitted physical fork-ownership coupling (`eating_i = 2 → f_i = 0 ∧ f_{i+1} = 0`), surfacing the exact unreachable state where a philosopher was marked eating while an adjacent fork remained `1` on the table.

---

### Discovery 5: Rejected Hypothesis (`EXP-05`) — Why Always-On Post-Lock `GV4` Beats ARMv9 LSE `ldaddal`
On Apple M4 Max (ARMv9.2 LSE), `fetch_add(1)` compiles to a single pipelined cache-controller instruction (`ldaddal`), whereas `GV4` requires `load` + `CAS` (`ldar` + `casal`). In `EXP-05`, we tested using `fetch_add` when `attempt == 0` and reserving `GV4` CAS elision for `attempt > 0`.
- **Result (`DISCARDED`)**: Unconditional `fetch_add` on `attempt == 0` inflated `g_tl2_clock` 5–10× faster, invalidating `tx.rv` snapshots on other cores and regressing 8-thread Contended Bank throughput by **-31%** (`4.84 → 3.35 Mops/s`), Split-Counter `TBQueue` by **-31%** (`0.90 → 0.62 Mops/s`), and 16-thread Read-Dominated throughput by **-17%** (`27.58 → 23.00 Mops/s`).
- Always-on Post-Lock `GV4` CAS elides **78.6% of global clock increments** at 16 threads (`314,347` elisions across `400,000` commits), keeping global clock advancement gentle so concurrent readers validate locally without aborting!

---

## 3. Empirical Multi-Core Benchmarks (Apple M4 Max, 16 Cores)

*(Measured via `lake exe stm-bench`, compiled with `-O3 -std=c++20` on Lean 4.35.0 `arm64-apple-darwin24.6.0`, Apple M4 Max 12P+4E cores. Machine-readable experiment log in [`autoresearch/experiments.jsonl`](autoresearch/experiments.jsonl).)*

### Summary Speedups
- **16-Thread Read-Dominated (`95% Read / 5% Write`)**: `TL2-LSA+GV4` (`27.58 Mops/s`) is **4.24× faster** than raw `IO.Ref` (`6.50 Mops/s`, bottlenecked by `exchange(nullptr)`) and **2.25× faster** than `Std.Mutex` (`12.24 Mops/s`).
- **16-Thread Disjoint Shards (`100% Write`)**: `TL2` (`20.92 Mops/s`) is **10.78× faster** than `NOrec` (`1.94 Mops/s`) and **3.04× faster** than pure-Lean `Mutex` STM (`6.89 Mops/s`).
- **Long 32-`TVar` Audit Under 8-Writer Storm**: `MVCC-ReadOnly` (`54.38 ms`, 0 reader aborts) is **48.4× faster** than `TL2-GV1` (`2,634.67 ms`) and **185.1× faster** than `NOrec` (`10,066.68 ms`), while `TL2-LSA` with automatic MVCC fallback (`114.65 ms`) achieves a **23.0× speedup** with zero code changes!
- **Bounded Queue (`4P × 4C`)**: Verified Split-Counter `TBQueue` (`0.90 Mops/s`) is **2.00× faster** than single-counter `NaiveTBQueue` (`0.45 Mops/s`).
- **Transactional HashMap (`50% R / 50% W`, 8 Threads)**: 64-Stripe `TMap` (`6.02 Mops/s`, `10.07%` abort) is **96.6× faster** than a monolithic `TVar (HashMap)` (`0.06 Mops/s`, `60.50%` abort).

### Full Benchmark Table

| Workload | Engine / Protocol | Threads | Ops | Time (ms) | Throughput (Mops/s) | Abort % | LSA Ext | MVCC Snaps | GV4 Elide |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Read-Dominated (95R/5W) | `IO.Ref` (raw) | 1 | 40,000 | 0.21 | **193.00** | 0.00% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `Std.Mutex` (coarse) | 1 | 40,000 | 1.25 | **32.04** | 0.00% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `STM (TL2-LSA+GV4)` | 1 | 40,000 | 1.41 | **28.36** | 0.00% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `IO.Ref` (raw) | 4 | 160,000 | 2.12 | **75.41** | 0.00% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `Std.Mutex` (coarse) | 4 | 160,000 | 17.78 | **9.00** | 0.00% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `STM (NOrec)` | 4 | 160,000 | 3.87 | **41.38** | 0.00% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `STM (TL2-GV1)` | 4 | 160,000 | 10.85 | **14.74** | 1.51% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `STM (TL2-LSA+GV4)` | 4 | 160,000 | 5.52 | **29.01** | 0.54% | 105 | 96 | 275 |
| Read-Dominated (95R/5W) | `IO.Ref` (raw) | 16 | 640,000 | 98.39 | **6.50** | 0.00% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `Std.Mutex` (coarse) | 16 | 640,000 | 52.27 | **12.24** | 0.00% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `STM (NOrec)` | 16 | 640,000 | 31.72 | **20.18** | 0.10% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `STM (TL2-GV1)` | 16 | 640,000 | 30.99 | **20.65** | 2.89% | 0 | 0 | 0 |
| Read-Dominated (95R/5W) | `STM (TL2-LSA+GV4)` | 16 | 640,000 | 23.20 | **27.58** | 2.60% | 2,403 | 2,884 | 2,467 |
| Disjoint Writes (100W) | `PureRef` (Lean Mtx) | 16 | 400,000 | 58.05 | **6.89** | 0.00% | 0 | 0 | 0 |
| Disjoint Writes (100W) | `STM (NOrec)` | 16 | 400,000 | 206.00 | **1.94** | 0.00% | 0 | 0 | 0 |
| Disjoint Writes (100W) | `STM (TL2-GV1)` | 16 | 400,000 | 19.12 | **20.92** | 0.00% | 0 | 0 | 0 |
| Disjoint Writes (100W) | `STM (TL2-LSA+GV4)` | 16 | 400,000 | 22.90 | **17.47** | 0.00% | 0 | 0 | 314,347 |
| Contended Bank (2-TVar) | `STM (NOrec)` | 8 | 120,000 | 55.92 | **2.15** | 39.20% | 0 | 0 | 0 |
| Contended Bank (2-TVar) | `STM (TL2-GV1)` | 8 | 120,000 | 36.31 | **3.30** | 34.19% | 0 | 0 | 0 |
| Contended Bank (2-TVar) | `STM (TL2-LSA+GV4)` | 8 | 120,000 | 24.78 | **4.84** | 28.60% | 5,766 | 0 | 14,235 |
| 32-TVar Audit + 8 Writers | `STM (NOrec)` | 9 | 5,000 | 10,066.68 | **0.00** | 25.04% | 0 | 0 | 0 |
| 32-TVar Audit + 8 Writers | `STM (TL2-GV1)` | 9 | 5,000 | 2,634.67 | **0.00** | 22.42% | 724,231 | 0 | 1,260,338 |
| 32-TVar Audit + 8 Writers | `STM (TL2-LSA Adapt)` | 9 | 5,000 | 114.65 | **0.04** | 17.55% | 37,791 | 4,845 | 55,490 |
| 32-TVar Audit + 8 Writers | `STM (MVCC-ReadOnly)` | 9 | 5,000 | 54.38 | **0.09** | 16.20% | 15,229 | 5,000 | 26,594 |
| Bounded Queue (4P×4C) | `NaiveTBQueue` (1-ctr) | 8 | 120,000 | 264.54 | **0.45** | 80.34% | 16,330 | 0 | 0 |
| Bounded Queue (4P×4C) | `TBQueue` (Split-ctr) | 8 | 120,000 | 132.62 | **0.90** | 59.65% | 8,818 | 0 | 1,354 |
| Transactional Map (50R/50W) | Monolithic `TVar` Map | 8 | 120,000 | 1,924.74 | **0.06** | 60.50% | 1 | 2 | 0 |
| Transactional Map (50R/50W) | Striped `TMap` (64×) | 8 | 120,000 | 19.92 | **6.02** | 10.07% | 48 | 1,736 | 9,102 |
