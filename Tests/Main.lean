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

  -- Outer write before `orElse` should survive when left branch retries, while left branch's writes roll back!
  let usedBackup ← atomically do
    logVar.modify (fun xs => "start" :: xs)
    let fromBackup ←
      (do
        logVar.modify (fun xs => "tried-primary" :: xs)
        let b1 ← acc1.read
        -- Nested inner `orElse` that succeeds, followed by outer `retry`!
        (do acc1.write (b1 + 999)) <|> (pure ())
        check (b1 >= 100) -- fails! Must undo BOTH `tried-primary` AND `b1 + 999`, keeping `"start"`!
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

  -- Exception rollback via `tryCatch` and uncaught `throw`
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

  -- Consumer waits on `chA <|> chB` (must park on `reads(chA) ∪ reads(chB)`!)
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

  IO.sleep 25 -- ensure consumer is parked in `WaitQueue`
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
    let itersPerThread := 2000
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
              -- Allocate fresh heap `Array Nat` every transaction to hammer Perceus + Fraser EBR!
              let nextSrc := if histSrc.size >= 8 then #[tid] else histSrc.push tid
              let nextDst := if histDst.size >= 8 then #[step] else histDst.push step
              srcVar.write (bSrc - amt, nextSrc)
              dstVar.write (bDst + amt, nextDst)
      tasks := tasks.push t

    -- Concurrent MVCC read-only auditor verifying exact conservation (`sum == 8000`) mid-flight!
    let accsAudit := accs
    let auditTask ← IO.asTask (prio := .dedicated) do
      for _ in [0:300] do
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

def main : IO Unit := do
  IO.println "=== lean-stm Core Runtime Test Suite ==="
  STM.resetStats
  testBasicReadWrite
  testOrElseAndExceptions
  testModularRetryWakeup
  testConcurrentConservationAndEBR
  let st ← STM.getStats
  IO.println s!"  [Telemetry] commits={st.commits} abortsConflict={st.abortsConflict} abortsVal={st.abortsValidation} retriesParked={st.retriesParked} lsaExt={st.lsaExtensions} mvccSnaps={st.mvccSnapshots} gv4Elisions={st.gv4Elisions}"
  IO.println "=== ALL CORE TESTS PASSED ==="
