/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Sync.Mutex
import STM

open STM

private structure BenchRow where
  workload   : String
  engine     : String
  threads    : Nat
  totalOps   : Nat
  elapsedMs  : Float
  mopsPerSec : Float
  abortPct   : Float
  lsaExt     : UInt64
  mvccSnaps  : UInt64
  gv4Elide   : UInt64

private def fmtFloat2 (x : Float) : String :=
  let scaled := (x * 100.0 + 0.5).toUInt64
  let whole  := scaled / 100
  let frac   := scaled % 100
  let fracStr := if frac < 10 then s!"0{frac}" else s!"{frac}"
  s!"{whole}.{fracStr}"

private def padRight (s : String) (w : Nat) : String :=
  if s.length >= w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

private def printHeader : IO Unit := do
  IO.println "| Workload | Engine / Protocol | Threads | Ops | Time (ms) | Throughput (Mops/s) | Abort % | LSA Ext | MVCC Snaps | GV4 Elide |"
  IO.println "| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"

private def printRow (r : BenchRow) : IO Unit := do
  IO.println s!"| {padRight r.workload 26} | {padRight r.engine 19} | {r.threads} | {r.totalOps} | {fmtFloat2 r.elapsedMs} | **{fmtFloat2 r.mopsPerSec}** | {fmtFloat2 r.abortPct}% | {r.lsaExt} | {r.mvccSnaps} | {r.gv4Elide} |"

private def runTimed (workload engine : String) (threads totalOps : Nat) (act : IO Unit) : IO BenchRow := do
  STM.resetStats
  let t0 ← IO.monoNanosNow
  act
  let t1 ← IO.monoNanosNow
  let st ← STM.getStats
  let ns := Float.ofNat (t1 - t0)
  let ms := ns / 1000000.0
  let mops := if ns == 0.0 then 0.0 else (Float.ofNat totalOps * 1000.0) / ns
  let row : BenchRow := {
    workload   := workload
    engine     := engine
    threads    := threads
    totalOps   := totalOps
    elapsedMs  := ms
    mopsPerSec := mops
    abortPct   := st.abortRatePct
    lsaExt     := st.lsaExtensions
    mvccSnaps  := st.mvccSnapshots
    gv4Elide   := st.gv4Elisions
  }
  printRow row
  return row

/-! ## Workload 1: Read-Dominated Shared Config (95% Read / 5% Write, 16 Vars) -/

def benchReadDominated : IO Unit := do
  let numVars := 16
  let opsPerThread := 40000
  for nThreads in [1, 4, 8, 16] do
    let totalOps := nThreads * opsPerThread

    -- 1a. Raw `IO.Ref` baseline (demonstrates `exchange(nullptr)` read contention in Lean 4's runtime!)
    let mut ioRefs : Array (IO.Ref Nat) := #[]
    for i in [0:numVars] do
      ioRefs := ioRefs.push (← IO.mkRef i)
    let _ ← runTimed "Read-Dominated (95R/5W)" "IO.Ref (raw)" nThreads totalOps do
      let mut tasks := #[]
      for tid in [0:nThreads] do
        let refs := ioRefs
        let t ← IO.asTask (prio := .dedicated) do
          let mut sum := 0
          for step in [0:opsPerThread] do
            let idx := (tid * 5 + step) % numVars
            if h : idx < refs.size then
              if step % 20 == 0 then
                refs[idx].modify (· + 1)
              else
                sum := sum + (← refs[idx].get)
          if sum == 999999999 then IO.println ""
        tasks := tasks.push t
      for t in tasks do IO.ofExcept t.get

    -- 1b. Coarse `Std.Mutex` baseline
    let mut initArr : Array Nat := #[]
    for i in [0:numVars] do initArr := initArr.push i
    let mtx ← Std.Mutex.new initArr
    let _ ← runTimed "Read-Dominated (95R/5W)" "Std.Mutex (coarse)" nThreads totalOps do
      let mut tasks := #[]
      for tid in [0:nThreads] do
        let t ← IO.asTask (prio := .dedicated) do
          let mut sum := 0
          for step in [0:opsPerThread] do
            let idx := (tid * 5 + step) % numVars
            if step % 20 == 0 then
              mtx.atomically do
                modify fun a => a.modify idx (· + 1)
            else
              let v ← mtx.atomically do
                let a ← get
                return a.getD idx 0
              sum := sum + v
          if sum == 999999999 then IO.println ""
        tasks := tasks.push t
      for t in tasks do IO.ofExcept t.get

    -- 1c. STM protocols: NOrec, TL2-GV1, TL2-LSA+GV4
    for (name, proto) in [("STM (NOrec)", Protocol.norec), ("STM (TL2-GV1)", Protocol.tl2Gv1), ("STM (TL2-LSA+GV4)", Protocol.tl2Lsa)] do
      let mut tvars : Array (TVar Nat) := #[]
      for i in [0:numVars] do
        tvars := tvars.push (← TVar.newIO i)
      let _ ← runTimed "Read-Dominated (95R/5W)" name nThreads totalOps do
        let mut tasks := #[]
        for tid in [0:nThreads] do
          let tvs := tvars
          let t ← IO.asTask (prio := .dedicated) do
            let mut sum := 0
            for step in [0:opsPerThread] do
              let idx := (tid * 5 + step) % numVars
              if h : idx < tvs.size then
                let tv := tvs[idx]
                if step % 20 == 0 then
                  atomicallyWith proto (tv.modify (· + 1))
                else
                  let v ← atomicallyWith proto tv.read
                  sum := sum + v
            if sum == 999999999 then IO.println ""
          tasks := tasks.push t
        for t in tasks do IO.ofExcept t.get

/-! ## Workload 2: Disjoint-Access Parallel Writes (100% Write across 64 Shards) -/

def benchDisjointWrites : IO Unit := do
  let numShards := 64
  let opsPerThread := 25000
  for nThreads in [1, 4, 8, 16] do
    let totalOps := nThreads * opsPerThread

    -- Pure-Lean Coarse STM (`STM.PureRef`)
    let mut pvars : Array (PureRef.PTVar Nat) := #[]
    for _ in [0:numShards] do
      pvars := pvars.push (← PureRef.PureSTM.newTVarIO 0)
    let _ ← runTimed "Disjoint Writes (100W)" "PureRef (Lean Mtx)" nThreads totalOps do
      let mut tasks := #[]
      for tid in [0:nThreads] do
        let pvs := pvars
        let t ← IO.asTask (prio := .dedicated) do
          let shard := (tid * 4) % numShards
          if h : shard < pvs.size then
            let pv := pvs[shard]
            for _ in [0:opsPerThread] do
              PureRef.PureSTM.atomically do
                let x ← PureRef.PureSTM.read pv
                PureRef.PureSTM.write pv (x + 1)
        tasks := tasks.push t
      for t in tasks do IO.ofExcept t.get

    for (name, proto) in [("STM (NOrec)", Protocol.norec), ("STM (TL2-GV1)", Protocol.tl2Gv1), ("STM (TL2-LSA+GV4)", Protocol.tl2Lsa)] do
      let mut tvars : Array (TVar Nat) := #[]
      for _ in [0:numShards] do
        tvars := tvars.push (← TVar.newIO 0)
      let _ ← runTimed "Disjoint Writes (100W)" name nThreads totalOps do
        let mut tasks := #[]
        for tid in [0:nThreads] do
          let tvs := tvars
          let t ← IO.asTask (prio := .dedicated) do
            let shard := (tid * 4) % numShards
            if h : shard < tvs.size then
              let tv := tvs[shard]
              for _ in [0:opsPerThread] do
                atomicallyWith proto (tv.modify (· + 1))
          tasks := tasks.push t
        for t in tasks do IO.ofExcept t.get

/-! ## Workload 3: High-Contention Multi-Account Bank Transfers (16 Accounts) -/

def benchContendedTransfers : IO Unit := do
  let numAccounts := 16
  let opsPerThread := 15000
  for nThreads in [4, 8, 16] do
    let totalOps := nThreads * opsPerThread
    for (name, proto) in [("STM (NOrec)", Protocol.norec), ("STM (TL2-GV1)", Protocol.tl2Gv1), ("STM (TL2-LSA+GV4)", Protocol.tl2Lsa)] do
      let mut accs : Array (TVar Nat) := #[]
      for _ in [0:numAccounts] do
        accs := accs.push (← TVar.newIO 10000)
      let _ ← runTimed "Contended Bank (2-TVar)" name nThreads totalOps do
        let mut tasks := #[]
        for tid in [0:nThreads] do
          let aSnap := accs
          let t ← IO.asTask (prio := .dedicated) do
            for step in [0:opsPerThread] do
              let i := (tid * 3 + step) % numAccounts
              let j := (i + 1 + (step % (numAccounts - 1))) % numAccounts
              if h1 : i < aSnap.size then
              if h2 : j < aSnap.size then
              let src := aSnap[i]
              let dst := aSnap[j]
              atomicallyWith proto do
                let b1 ← src.read
                let b2 ← dst.read
                if b1 >= 10 then
                  src.write (b1 - 10)
                  dst.write (b2 + 10)
          tasks := tasks.push t
        for t in tasks do IO.ofExcept t.get

/-! ## Workload 4: Long 32-Account Audit Under 8-Writer Storm (Starvation vs Hybrid MVCC!) -/

def benchLongAuditUnderWriteStorm : IO Unit := do
  let numAccounts := 32
  let numAudits := 5000
  for (name, mode) in [
      ("STM (TL2-GV1)", 0),
      ("STM (NOrec)", 1),
      ("STM (TL2-LSA Adapt)", 2),
      ("STM (MVCC-ReadOnly)", 3)] do
    let mut accs : Array (TVar Nat) := #[]
    for _ in [0:numAccounts] do
      accs := accs.push (← TVar.newIO 1000)
    let stopFlag ← IO.mkRef false

    -- Spawn 8 background writer threads continuously transferring between random accounts
    let mut bgWriters := #[]
    for tid in [0:8] do
      let aSnap := accs
      let wTask ← IO.asTask (prio := .dedicated) do
        let mut step := 0
        while !(← stopFlag.get) do
          let i := (tid * 5 + step) % numAccounts
          let j := (i + 7) % numAccounts
          if h1 : i < aSnap.size then
          if h2 : j < aSnap.size then
          let wProto := if mode == 1 then Protocol.norec else Protocol.tl2Lsa
          atomicallyWith wProto do
            let b1 ← aSnap[i].read
            let b2 ← aSnap[j].read
            if b1 >= 5 then
              aSnap[i].write (b1 - 5)
              aSnap[j].write (b2 + 5)
          step := step + 1
      bgWriters := bgWriters.push wTask

    IO.sleep 10 -- let write storm reach full speed

    let scanTx : STM Nat := do
      let mut total := 0
      for tv in accs do
        total := total + (← tv.read)
      return total

    let _ ← runTimed "32-TVar Audit + 8 Writers" name 9 numAudits do
      for _ in [0:numAudits] do
        let sum ← match mode with
          | 0 => atomicallyWith .tl2Gv1 scanTx
          | 1 => atomicallyWith .norec scanTx
          | 2 => atomicallyWith .tl2Lsa scanTx
          | _ => atomicallyReadOnly scanTx
        if sum != numAccounts * 1000 then
          throw <| IO.userError s!"Opacity violation in {name}: sum={sum}"

    stopFlag.set true
    for w in bgWriters do IO.ofExcept w.get

/-! ## Workload 5: Bounded Queue Backpressure (Single-Counter vs GHC Split-Counter `TBQueue`) -/

def benchBoundedQueues : IO Unit := do
  let nProd := 4
  let nCons := 4
  let itemsPerWorker := 15000
  let totalOps := (nProd + nCons) * itemsPerWorker

  -- 5a. Naive single-counter bounded queue
  let nq ← NaiveTBQueue.newIO (α := Nat) (capacity := 128)
  let _ ← runTimed "Bounded Queue (4P×4C)" "NaiveTBQueue (1-ctr)" 8 totalOps do
    let mut tasks := #[]
    for _ in [0:nProd] do
      tasks := tasks.push (← IO.asTask (prio := .dedicated) do
        for i in [0:itemsPerWorker] do atomically (nq.write i))
    for _ in [0:nCons] do
      tasks := tasks.push (← IO.asTask (prio := .dedicated) do
        let mut s := 0
        for _ in [0:itemsPerWorker] do s := s + (← atomically nq.read)
        if s == 999999999 then IO.println "")
    for t in tasks do IO.ofExcept t.get

  -- 5b. Split-counter `TBQueue`
  let sq ← TBQueue.newIO (α := Nat) (capacity := 128)
  let _ ← runTimed "Bounded Queue (4P×4C)" "TBQueue (Split-ctr)" 8 totalOps do
    let mut tasks := #[]
    for _ in [0:nProd] do
      tasks := tasks.push (← IO.asTask (prio := .dedicated) do
        for i in [0:itemsPerWorker] do atomically (sq.write i))
    for _ in [0:nCons] do
      tasks := tasks.push (← IO.asTask (prio := .dedicated) do
        let mut s := 0
        for _ in [0:itemsPerWorker] do s := s + (← atomically sq.read)
        if s == 999999999 then IO.println "")
    for t in tasks do IO.ofExcept t.get

/-! ## Workload 6: Striped `TMap` vs Monolithic `TVar (HashMap)` (STO Disjoint Sharding) -/

def benchStripedMapVsMonolithic : IO Unit := do
  let nThreads := 8
  let opsPerThread := 15000
  let totalOps := nThreads * opsPerThread
  let keySpace := 512

  -- 6a. Monolithic `TVar (Std.HashMap Nat Nat)`
  let mono ← TVar.newIO (∅ : Std.HashMap Nat Nat)
  let _ ← runTimed "Transactional Map (50R/50W)" "Monolithic TVar Map" nThreads totalOps do
    let mut tasks := #[]
    for tid in [0:nThreads] do
      tasks := tasks.push (← IO.asTask (prio := .dedicated) do
        for step in [0:opsPerThread] do
          let k := (tid * 61 + step) % keySpace
          if step % 2 == 0 then
            atomically do
              let m ← mono.read
              mono.write (m.insert k step)
          else
            let _ ← atomically do
              let m ← mono.read
              return m[k]?)
    for t in tasks do IO.ofExcept t.get

  -- 6b. 64-Stripe `TMap Nat Nat`
  let tmap ← TMap.newIO (κ := Nat) (ν := Nat) (numStripes := 64)
  let _ ← runTimed "Transactional Map (50R/50W)" "Striped TMap (64x)" nThreads totalOps do
    let mut tasks := #[]
    for tid in [0:nThreads] do
      tasks := tasks.push (← IO.asTask (prio := .dedicated) do
        for step in [0:opsPerThread] do
          let k := (tid * 61 + step) % keySpace
          if step % 2 == 0 then
            atomically (tmap.insert k step)
          else
            let _ ← atomically (tmap.get? k))
    for t in tasks do IO.ofExcept t.get

def main : IO Unit := do
  IO.println "# `lean-stm` Multi-Core Benchmark Suite (Apple Silicon ARM64)"
  IO.println ""
  printHeader
  benchReadDominated
  benchDisjointWrites
  benchContendedTransfers
  benchLongAuditUnderWriteStorm
  benchBoundedQueues
  benchStripedMapVsMonolithic
