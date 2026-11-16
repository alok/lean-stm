/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM

open STM

private def assertEq [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  if actual != expected then
    throw <| IO.userError s!"[FAIL] {label}: expected {repr expected}, got {repr actual}"

private def assertTrue (label : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw <| IO.userError s!"[FAIL] {label}: assertion failed"

/-- Test 1: Basic read, write, read-after-write forwarding, and swap across all write-capable protocols. -/
def testBasicReadWrite : IO Unit := do
  for proto in [Protocol.tl2Lsa, Protocol.tl2Gv1, Protocol.norec] do
    let a ← TVar.newIO (10 : Nat)
    let b ← TVar.newIO ("hello" : String)
    let res ← atomicallyWith proto do
      let x ← a.read
      a.write (x + 5)
      let x2 ← a.read -- read-after-write forwarding!
      let oldStr ← b.swap (s!"world-{x2}")
      return (x, x2, oldStr)
    assertEq s!"basic-rw-{repr proto}" res (10, 15, "hello")
    assertEq s!"basic-final-a-{repr proto}" (← a.readIO) 15
    assertEq s!"basic-final-b-{repr proto}" (← b.readIO) "world-15"
  IO.println "  [OK] testBasicReadWrite (TL2-LSA, TL2-GV1, NOrec + heap String RC)"

/-- Test 2: Nested `orElse` (`<|>`) write-rollback & `tryCatch` exception rollback. -/
def testOrElseAndExceptions : IO Unit := do
  let acc1 ← TVar.newIO (50 : Nat)
  let acc2 ← TVar.newIO (200 : Nat)
  let logVar ← TVar.newIO ([] : List String)

  let usedBackup ← atomically do
    logVar.modify (fun xs => "start" :: xs)
    let fromBackup ←
      (do
        logVar.modify (fun xs => "tried-primary" :: xs)
        let b1 ← acc1.read
        (do acc1.write (b1 + 999)) <|> (pure ())
        check (b1 >= 100)
        acc1.write (b1 - 100)
        return false)
      <|>
      (do
        logVar.modify (fun xs => "used-backup" :: xs)
        let b2 ← acc2.read
        check (b2 >= 100)
        acc2.write (b2 - 100)
        return true)
    return fromBackup

  assertEq "orElse-chose-backup" usedBackup true
  assertEq "orElse-acc1-untouched" (← acc1.readIO) 50
  assertEq "orElse-acc2-debited" (← acc2.readIO) 100
  assertEq "orElse-log-rollback" (← logVar.readIO) ["used-backup", "start"]

  let caught ← atomically do
    acc1.write 777
    try
      acc1.write 888
      throw (IO.userError "boom")
    catch _ =>
      let cur ← acc1.read
      return cur
  assertEq "tryCatch-rolled-back-to-777" caught 777
  assertEq "tryCatch-committed-777" (← acc1.readIO) 777

  let mut threw := false
  try
    atomically do
      acc1.write 9999
      throw (IO.userError "uncaught")
  catch _ =>
    threw := true
  assertTrue "uncaught-threw" threw
  assertEq "uncaught-rolled-back" (← acc1.readIO) 777
  IO.println "  [OK] testOrElseAndExceptions (nested savepoints + tryCatch + uncaught rollback)"

/-- Test 3: Modular blocking (`retry`) & `orElse` multi-TVar wakeup with zero busy-wait. -/
def testModularRetryWakeup : IO Unit := do
  let chA ← TVar.newIO (none : Option Nat)
  let chB ← TVar.newIO (none : Option Nat)

  let consumerTask ← IO.asTask (prio := .dedicated) do
    atomically do
      (do
        match (← chA.read) with
        | some v => chA.write none; return ("A", v)
        | none   => retry)
      <|>
      (do
        match (← chB.read) with
        | some v => chB.write none; return ("B", v)
        | none   => retry)

  IO.sleep 20
  atomically do
    chB.write (some 42)

  let res ← IO.ofExcept consumerTask.get
  assertEq "retry-orElse-wakeup" res ("B", 42)
  assertEq "retry-chB-consumed" (← chB.readIO) none
  IO.println "  [OK] testModularRetryWakeup (Dekker WaitQueue parking on chA ∪ chB)"

/-- Test 4: High-contention multi-core Bank Transfer Conservation + Heap Object EBR Stress! -/
def testConcurrentConservationAndEBR : IO Unit := do
  for proto in [Protocol.tl2Lsa, Protocol.tl2Gv1, Protocol.norec] do
    let numAccounts := 8
    let initBalance := 1000
    let mut accs : Array (TVar (Nat × Array Nat)) := #[]
    for i in [0:numAccounts] do
      let tv ← TVar.newIO (initBalance, #[i])
      accs := accs.push tv

    let numThreads := 8
    let itersPerThread := 1500
    let mut tasks := #[]
    for tid in [0:numThreads] do
      let accsSnap := accs
      let t ← IO.asTask (prio := .dedicated) do
        for step in [0:itersPerThread] do
          let src := (tid * 3 + step) % numAccounts
          let dst := (src + 1 + (step % (numAccounts - 1))) % numAccounts
          let amt := (step % 17) + 1
          if h1 : src < accsSnap.size then
          if h2 : dst < accsSnap.size then
          let srcVar := accsSnap[src]
          let dstVar := accsSnap[dst]
          atomicallyWith proto do
            let (bSrc, histSrc) ← srcVar.read
            let (bDst, histDst) ← dstVar.read
            if bSrc >= amt then
              let nextSrc := if histSrc.size >= 8 then #[tid] else histSrc.push tid
              let nextDst := if histDst.size >= 8 then #[step] else histDst.push step
              srcVar.write (bSrc - amt, nextSrc)
              dstVar.write (bDst + amt, nextDst)
      tasks := tasks.push t

    let accsAudit := accs
    let auditTask ← IO.asTask (prio := .dedicated) do
      for _ in [0:250] do
        let total ← atomicallyReadOnly do
          let mut sum := 0
          for tv in accsAudit do
            let (bal, _) ← tv.read
            sum := sum + bal
          return sum
        assertEq s!"mid-flight-opacity-sum-{repr proto}" total (numAccounts * initBalance)

    for t in tasks do
      IO.ofExcept t.get
    IO.ofExcept auditTask.get

    let finalTotal ← atomicallyReadOnly do
      let mut s := 0
      for tv in accs do
        let (bal, _) ← tv.read
        s := s + bal
      return s
    assertEq s!"final-conservation-{repr proto}" finalTotal (numAccounts * initBalance)
  IO.println "  [OK] testConcurrentConservationAndEBR (8 threads × 3 protocols + live MVCC opacity auditor + heap Array EBR)"

/-- Test 5: Split-Capacity `TBQueue` backpressure & exact conservation under 4 producers × 4 consumers. -/
def testTBQueueBackpressure : IO Unit := do
  let q ← TBQueue.newIO (capacity := 16)
  let numWorkers := 4
  let itemsPerWorker := 1000

  -- 4 dedicated producers pushing 1..1000 each (sum = 4 * 500500 = 2002000)
  let mut prodTasks := #[]
  for _ in [0:numWorkers] do
    let t ← IO.asTask (prio := .dedicated) do
      for i in [1:itemsPerWorker + 1] do
        atomically (q.write i)
    prodTasks := prodTasks.push t

  -- 4 dedicated consumers popping 1000 items each
  let mut consTasks := #[]
  for _ in [0:numWorkers] do
    let t ← IO.asTask (prio := .dedicated) do
      let mut localSum := 0
      for _ in [0:itemsPerWorker] do
        let x ← atomically q.read
        localSum := localSum + x
      return localSum
    consTasks := consTasks.push t

  for p in prodTasks do
    IO.ofExcept p.get
  let mut totalPopped := 0
  for c in consTasks do
    totalPopped := totalPopped + (← IO.ofExcept c.get)

  let expected := numWorkers * (itemsPerWorker * (itemsPerWorker + 1) / 2)
  assertEq "tbqueue-sum" totalPopped expected
  assertEq "tbqueue-empty" (← atomically q.isEmpty) true
  IO.println "  [OK] testTBQueueBackpressure (4P × 4C bounded cap=16, exact item conservation)"

/-- Test 6: `TChan` multicast broadcast (`dup`), `TMVar` handoff, `TQueue`, and `TSem` Dining Philosophers. -/
def testChannelsSemaphoresAndPhilosophers : IO Unit := do
  -- 6a. Broadcast TChan with 3 independent subscribers
  let bcast ← TChan.newBroadcastIO (α := Nat)
  let sub1 ← atomically bcast.dup
  let sub2 ← atomically bcast.dup
  let sub3 ← atomically bcast.dup

  for x in [10, 20, 30] do
    atomically (bcast.write x)

  for (name, sub) in [("sub1", sub1), ("sub2", sub2), ("sub3", sub3)] do
    let a ← atomically sub.read
    let b ← atomically sub.read
    let c ← atomically sub.read
    assertEq s!"tchan-{name}" [a, b, c] [10, 20, 30]
    assertEq s!"tchan-empty-{name}" (← atomically sub.isEmpty) true

  -- 6b. Deadlock-free Dining Philosophers using `TMVar` forks (even with symmetric pickup order!)
  let nPhil := 5
  let mut forks : Array (TMVar Unit) := #[]
  for _ in [0:nPhil] do
    forks := forks.push (← TMVar.newIO ())

  let mealsDone ← TVar.newIO 0
  let mut philTasks := #[]
  for i in [0:nPhil] do
    let forksSnap := forks
    let t ← IO.asTask (prio := .dedicated) do
      let leftIdx := i
      let rightIdx := (i + 1) % nPhil
      if h1 : leftIdx < forksSnap.size then
      if h2 : rightIdx < forksSnap.size then
      let fL := forksSnap[leftIdx]
      let fR := forksSnap[rightIdx]
      for _ in [0:200] do
        -- Pick up BOTH forks atomically in one transaction: zero deadlock without manual ordering!
        atomically do
          fL.take
          fR.take
        atomically do
          mealsDone.modify (· + 1)
          fL.put ()
          fR.put ()
    philTasks := philTasks.push t

  for t in philTasks do
    IO.ofExcept t.get
  assertEq "dining-philosophers-meals" (← mealsDone.readIO) (nPhil * 200)

  -- 6c. `TSem` multi-pool `<|>` resource selection
  let poolA ← TSem.newIO 0
  let poolB ← TSem.newIO 2
  let chosen ← atomically do
    (poolA.wait *> pure "A") <|> (poolB.waitN 2 *> pure "B")
  assertEq "tsem-orElse-pool" chosen "B"
  assertEq "tsem-poolB-rem" (← atomically poolB.available) 0
  IO.println "  [OK] testChannelsSemaphoresAndPhilosophers (TChan dup, Dining Philosophers, TSem <|>)"

/-- Test 7: STO-inspired Striped `TMap` concurrent cross-key transfers & MVCC consistent size. -/
def testStripedTMap : IO Unit := do
  let m ← TMap.newIO (κ := Nat) (ν := Nat) (numStripes := 32)
  let numKeys := 64
  atomically do
    for k in [0:numKeys] do
      m.insert k 100

  let mut workers := #[]
  for tid in [0:8] do
    let t ← IO.asTask (prio := .dedicated) do
      for step in [0:1000] do
        let k1 := (tid * 7 + step) % numKeys
        let k2 := (k1 + 13) % numKeys
        if k1 != k2 then
          atomically do
            let v1 := (← m.get? k1).getD 0
            let v2 := (← m.get? k2).getD 0
            if v1 >= 5 then
              m.insert k1 (v1 - 5)
              m.insert k2 (v2 + 5)
    workers := workers.push t

  for w in workers do
    IO.ofExcept w.get

  let entries ← atomicallyReadOnly m.toList
  assertEq "tmap-entry-count" entries.length numKeys
  let totalVal := entries.foldl (fun acc (_, v) => acc + v) 0
  assertEq "tmap-conservation" totalVal (numKeys * 100)
  IO.println "  [OK] testStripedTMap (8 threads × 1000 cross-stripe atomic transfers, 0 lost value)"

def main : IO Unit := do
  IO.println "=== lean-stm Runtime & Composable Data Structures Test Suite ==="
  STM.resetStats
  testBasicReadWrite
  testOrElseAndExceptions
  testModularRetryWakeup
  testConcurrentConservationAndEBR
  testTBQueueBackpressure
  testChannelsSemaphoresAndPhilosophers
  testStripedTMap
  let st ← STM.getStats
  IO.println s!"  [Telemetry] commits={st.commits} abortsConflict={st.abortsConflict} abortsVal={st.abortsValidation} retriesParked={st.retriesParked} lsaExt={st.lsaExtensions} mvccSnaps={st.mvccSnapshots} gv4Elisions={st.gv4Elisions}"
  IO.println "=== ALL RUNTIME & DATA STRUCTURE TESTS PASSED ==="
