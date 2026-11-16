# `lean-stm` — High-Performance, Formally Verified Software Transactional Memory for Lean 4

[![CI](https://github.com/alok/lean-stm/actions/workflows/ci.yml/badge.svg)](https://github.com/alok/lean-stm/actions/workflows/ci.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://lean-lang.org)
[![Zero Sorrys](https://img.shields.io/badge/Proofs-Zero%20sorry-brightgreen)](STM/Verify/)

**`lean-stm`** brings composable Haskell-style Software Transactional Memory (`STM`, `TVar`, `retry`, `orElse` / `<|>`) to **Lean 4**, backed by a multi-protocol **C++20 atomic runtime** tailored to Lean 4's Perceus reference-counting allocator and a **zero-`sorry` mechanized verification suite** proving **Opacity**, **TMS2**, **Deadlock Freedom**, **TL2-LSA**, **NOrec**, and **Lock-Before-Clock Hybrid MVCC**, plus a push-button **`stm_verify`** auto-verification tactic.

Zero external Lake dependencies — clones and compiles from scratch in ~4 seconds.

---

## Highlights

- **Multi-Protocol C++20 Engine (`c/lean_stm.cpp`)**:
  - **`Protocol.tl2Lsa` (Default)**: Transactional Locking II (*Dice, Shalev, Shavit*) enhanced with **Lazy Snapshot Extension (`LSA`, Riegel et al.)**, **Safe Post-Lock `GV4` CAS Clock Elision**, **Polka randomized exponential backoff**, **128-byte Apple-Silicon-aligned `TVar` cells**, and **Adaptive MVCC fallback**.
  - **`atomicallyReadOnly` (`Protocol.mvccReadOnly`)**: Wait-free read-only snapshots over an inline 8-version ring per `TVar` governed by our **Lock-Before-Clock Invariant** — 0% reader aborts even while 8 dedicated writer threads hammer the exact same `TVar`s.
  - **`Protocol.norec`**: Dalessandro-Spear-Scott `NOrec` global-seqlock engine exploiting Perceus reference counts for **ABA-free pointer value validation**.
  - **Fraser 3-Epoch Reclamation (EBR) + `lean_mark_mt`**: Eliminates Lean 4 `IO.Ref.get`'s `exchange(nullptr)` double-RMW read contention (`src/runtime/io.cpp:1458`), turning `TVar` reads into pure `acquire` loads with zero shared cache-line writes.
- **Full Composable Concurrency Algebra (`STM` & `STM.Data`)**:
  - `TVar`, `STM.retry` (Dekker-synchronized `seq_cst` WaitQueues — zero spinloops, zero lost wakeups), `STM.orElse` (`<|>` nested write-log savepoints retaining failed branch read-sets), `STM.check`, and transactional exception rollback (`try` / `catch`).
  - Ready-to-use transactional containers: `TMVar`, `TQueue`, **Split-Counter `TBQueue`** (disjoint producer/consumer capacity `TVar`s), multicast `TChan` (`dup` / `clone`), `TSem`, and **64-Stripe `TMap`** (*STO*-inspired disjoint sharding with cross-key atomic transactions).
- **Mechanized Meta-Theory & Auto-Verifier (`STM.Verify`, Zero `sorry`s)**:
  - [`Semantics.lean`](STM/Verify/Semantics.lean): Executable rollback & read-set semantics + Monad, `Alternative` (`orElse_assoc`, `orElse_retry_left/right`), read-after-write, write-after-write, idempotence, and disjoint commutativity laws.
  - [`DeadlockFree.lean`](STM/Verify/DeadlockFree.lean): Proof that strict ascending `TVarId` lock acquisition guarantees an acyclic `WaitsFor` graph.
  - [`Opacity.lean`](STM/Verify/Opacity.lean) & [`TMS2.lean`](STM/Verify/TMS2.lean): Guerraoui-Kapalka Opacity & Doherty et al. `TMS2` specification automaton (`reachable_opaque`).
  - [`TL2.lean`](STM/Verify/TL2.lean) & [`NOrec.lean`](STM/Verify/NOrec.lean): Concrete forward-simulation opacity proofs for `TL2 + LSA + GV4` (`tl2_reachable_opaque`) and `NOrec` (`norec_reachable_opaque`).
  - [`MVCC.lean`](STM/Verify/MVCC.lean): Mechanized counterexample proving naive lock-ignoring MVCC violates opacity (`naive_mvcc_violates_opacity`) + mechanized soundness proof of Lock-Before-Clock MVCC (`lock_before_clock_mvcc_sound`).
  - [`Auto.lean`](STM/Verify/Auto.lean) & [`Examples.lean`](STM/Verify/Examples.lean): Transactional Hoare logic, concurrent schedule lifting, and 1-line **`by stm_verify`** proofs (`grind` + `omega`) for failover bank transfers, split-counter `TBQueue`, `TSem`, and Dining Philosophers.

---

## Quickstart

Add `lean-stm` to your `lakefile.lean`:

```lean
require «lean-stm» from git "https://github.com/alok/lean-stm" @ "main"
```

### Composable Transactions with `retry` and `<|>` (`orElse`)

```lean
import STM
open STM

def payWithFailover (checking savings merchant : TVar Nat) (amt : Nat) : STM Bool := do
  -- Try checking first; if insufficient, `check` triggers `retry`, rolling back any writes
  -- in the left branch and automatically falling back to `savings`!
  (do
    let bal ← checking.read
    check (bal >= amt)
    checking.write (bal - amt)
    merchant.modify (· + amt)
    return false)
  <|>
  (do
    let bal ← savings.read
    check (bal >= amt)
    savings.write (bal - amt)
    merchant.modify (· + amt)
    return true)

def exampleRun : IO Unit := do
  let checking ← TVar.newIO 40
  let savings  ← TVar.newIO 500
  let merchant ← TVar.newIO 0

  let usedSavings ← atomically (payWithFailover checking savings merchant 100)
  -- Wait-free consistent multi-variable read snapshot:
  let total ← atomicallyReadOnly do
    return (← checking.read) + (← savings.read) + (← merchant.read)
  IO.println s!"usedSavings={usedSavings}, total={total}" -- true, 540
```

### Auto-Verifying Transactional Invariants with `stm_verify`

```lean
import STM

open STM.Verify STM.Verify.Examples

-- Discharged automatically in 1 line via @[stm_simp] symbolic evaluation + path splitting + omega/grind:
example (total amt : Nat) :
    Preserves (fun b => totalFunds b = total) (payWithFailover amt) := by
  stm_verify
```

---

## Build, Test & Benchmark

```bash
lake build                 # Compile C++20 runtime, STM library, and all zero-sorry proofs
lake exe stm-test          # Run multi-core conservation, retry/orElse wakeup & EBR stress tests
lake exe stm-bench         # Run 6-workload multi-core benchmark suite (1–16 threads)
```

---

## Key Benchmark Takeaways (16-Core Apple M4 Max)

| Workload (Apple M4 Max, 16 Cores) | Baseline | `lean-stm` (`TL2-LSA+GV4` / `MVCC`) | Speedup |
| :--- | :--- | :--- | ---: |
| **Read-Dominated (`95% R / 5% W`, 16T)** | Raw `IO.Ref`: `6.50 Mops/s` (`exchange` spin) | **`27.58 Mops/s`** (Fraser EBR + 0-lock reads) | **4.24×** |
| **Disjoint Writes (`100% W`, 16T)** | `NOrec`: `1.94 Mops/s` / `Mutex`: `6.89 Mops/s` | **`20.92 Mops/s`** (`TL2` 128B cells) | **10.78×** |
| **Contended Bank (`2-TVar`, 8T)** | `NOrec`: `2.15 Mops/s` / `TL2-GV1`: `3.30 Mops/s` | **`4.84 Mops/s`** (`LSA` + Post-Lock `GV4`) | **2.25×** |
| **32-`TVar` Audit + 8 Concurrent Writers** | `NOrec`: `10,067 ms` / `TL2-GV1`: `2,635 ms` | **`54.38 ms`** (`atomicallyReadOnly` MVCC) | **48.4× – 185×** |
| **Bounded Queue (`4P × 4C`)** | Single-counter `NaiveTBQueue`: `0.45 Mops/s` | **`0.90 Mops/s`** (Verified Split `TBQueue`) | **2.00×** |
| **Transactional Map (`50R/50W`, 8T)** | Monolithic `TVar (HashMap)`: `0.06 Mops/s` | **`6.02 Mops/s`** (64-Stripe `TMap`) | **96.6×** |

See [**`RESEARCH.md`**](RESEARCH.md) for the full benchmark tables, PL literature comparison, and prover-guided autoresearch log, and [**`GUIDE.md`**](GUIDE.md) for a deep from-scratch engineering & verification walkthrough.

---

## License

Apache-2.0. Copyright (c) 2026 Alok Singh.
