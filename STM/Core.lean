/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.FFI

namespace STM

/--
The Software Transactional Memory (`STM`) monad.

`STM α` represents a composable, speculative memory transaction that:
1. Reads and writes `TVar`s in an isolated thread-local view guaranteed to satisfy **Opacity**
   (even live or aborted transactions never observe torn/inconsistent snapshots).
2. Supports modular conditional blocking via `STM.retry` / `STM.check` without locks or busy-waiting.
3. Supports left-biased transactional choice via `STM.orElse` (`<|>`), rolling back speculative writes
   of a retrying branch while retaining its read-set for sound wakeup and validation.
4. Supports exception handling (`throw` / `tryCatch`) with automatic write rollback on uncaught errors.
5. Forbids arbitrary irrevocable `IO` side effects at the type level.
-/
structure STM (α : Type) where
  /-- Internal execution step on the thread-local transaction engine. -/
  runRaw : BaseIO (TxOutcome α)

namespace STM

@[always_inline, inline]
protected def pure (a : α) : STM α :=
  ⟨Pure.pure (.ok a)⟩

@[always_inline, inline]
protected def bind (x : STM α) (f : α → STM β) : STM β :=
  ⟨do
    match (← x.runRaw) with
    | .ok a        => (f a).runRaw
    | .retry       => Pure.pure .retry
    | .conflict    => Pure.pure .conflict
    | .userError e => Pure.pure (.userError e)⟩

@[always_inline, inline]
protected def map (f : α → β) (x : STM α) : STM β :=
  ⟨do
    match (← x.runRaw) with
    | .ok a        => Pure.pure (.ok (f a))
    | .retry       => Pure.pure .retry
    | .conflict    => Pure.pure .conflict
    | .userError e => Pure.pure (.userError e)⟩

instance : Monad STM where
  pure := STM.pure
  bind := STM.bind
  map  := STM.map

/--
Abort the current branch and block the calling thread until at least one `TVar` read so far
is modified by a committing transaction. Zero busy-waiting.
-/
@[always_inline, inline]
def retry : STM α :=
  ⟨Pure.pure .retry⟩

/--
Left-biased composable choice (`Harris et al., PPoPP 2005`):
Runs `t1` under a nested write-log savepoint.
- If `t1` succeeds with `.ok a`, commits the savepoint and returns `a`.
- If `t1` calls `retry`, rolls back all `TVar` writes made inside `t1` **while retaining `t1`'s read-set**,
  then runs `t2`. If `t2` also retries, `atomically` parks on `reads(t1) ∪ reads(t2)`.
- If `t1` encounters an optimistic `conflict` or throws an uncaught `userError`, propagates immediately.
-/
@[inline]
def orElse (t1 : STM α) (t2 : Unit → STM α) : STM α :=
  ⟨do
    let sp ← Prim.txSavepoint
    match (← t1.runRaw) with
    | .ok a =>
      Prim.txCommitSavepoint sp
      Pure.pure (.ok a)
    | .retry =>
      Prim.txRollbackSavepoint sp
      (t2 ()).runRaw
    | .conflict =>
      Prim.txRollbackSavepoint sp
      Pure.pure .conflict
    | .userError e =>
      Prim.txRollbackSavepoint sp
      Pure.pure (.userError e)⟩

instance : Alternative STM where
  failure := retry
  orElse  := orElse

instance : OrElse (STM α) where
  orElse := orElse

/--
Guard a transactional precondition: proceeds if `cond` is `true`, otherwise calls `retry`
(blocking until any `TVar` read in computing `cond` changes).
-/
@[always_inline, inline]
def check (cond : Bool) : STM Unit :=
  if cond then Pure.pure () else retry

/--
Throw an `IO.Error` inside a transaction. Unless caught by `tryCatch`, all speculative writes
in the transaction are rolled back and `atomically` rethrows the error in `IO`.
-/
@[always_inline, inline]
protected def throw (e : IO.Error) : STM α :=
  ⟨Pure.pure (.userError e)⟩

/--
Transactional exception handler (`catchSTM` in GHC): if `body` throws `e`, all `TVar` writes
performed inside `body` are rolled back to the savepoint before running `handler e`!
-/
@[inline]
protected def tryCatch (body : STM α) (handler : IO.Error → STM α) : STM α :=
  ⟨do
    let sp ← Prim.txSavepoint
    match (← body.runRaw) with
    | .ok a =>
      Prim.txCommitSavepoint sp
      Pure.pure (.ok a)
    | .userError e =>
      Prim.txRollbackSavepoint sp
      (handler e).runRaw
    | .retry =>
      Prim.txRollbackSavepoint sp
      Pure.pure .retry
    | .conflict =>
      Prim.txRollbackSavepoint sp
      Pure.pure .conflict⟩

instance : MonadExceptOf IO.Error STM where
  throw    := STM.throw
  tryCatch := STM.tryCatch

/--
Execute `tx` atomically using an explicit concurrency control `Protocol`.
Automatically retries on optimistic conflicts (with Polka randomized exponential backoff and
adaptive MVCC snapshot fallback) and parks on `retry` wait queues without busy-spinning.
-/
partial def atomicallyWith (proto : Protocol) (tx : STM α) : IO α := do
  let pByte := proto.toUInt8
  let rec loop (attempt : UInt32) : IO α := do
    Prim.txBegin pByte attempt
    match (← tx.runRaw) with
    | .ok val =>
      if (← Prim.txCommit) then
        return val
      else
        loop (attempt + 1)
    | .conflict =>
      Prim.txAbort
      loop (attempt + 1)
    | .retry =>
      Prim.txParkRetry
      loop 0
    | .userError err =>
      Prim.txAbort
      throw err
  loop 0

/--
Execute `tx` atomically under the active default protocol (`Protocol.tl2Lsa` by default).
-/
@[inline]
def atomically (tx : STM α) : IO α := do
  let p ← Prim.getDefaultProtocolRaw
  atomicallyWith (Protocol.ofUInt8 p) tx

/--
Execute a read-only transaction using wait-free 8-slot inline MVCC snapshots (`Protocol.mvccReadOnly`).
If `tx` dynamically attempts to write to a `TVar`, transparently upgrades and re-executes under `tl2Lsa`.
-/
partial def atomicallyReadOnly (tx : STM α) : IO α := do
  let rec loop (attempt : UInt32) : IO α := do
    Prim.txBegin Protocol.mvccReadOnly.toUInt8 attempt
    match (← tx.runRaw) with
    | .ok val =>
      if (← Prim.txCommit) then
        return val
      else
        loop (attempt + 1)
    | .conflict =>
      Prim.txAbort
      -- Upgrade seamlessly if `tx` attempted a write or if the 8-slot ring wrapped
      if attempt >= 2 then
        atomicallyWith .tl2Lsa tx
      else
        loop (attempt + 1)
    | .retry =>
      Prim.txParkRetry
      loop 0
    | .userError err =>
      Prim.txAbort
      throw err
  loop 0

def getDefaultProtocol : BaseIO Protocol := do
  return Protocol.ofUInt8 (← Prim.getDefaultProtocolRaw)

def setDefaultProtocol (p : Protocol) : BaseIO Unit :=
  Prim.setDefaultProtocolRaw p.toUInt8

def getStats : BaseIO Stats :=
  Prim.getStats

def resetStats : BaseIO Unit :=
  Prim.resetStats

end STM

namespace TVar

/-- Allocate a new `TVar` inside `BaseIO` / `IO`. -/
@[always_inline, inline]
def newIO (init : α) : BaseIO (TVar α) :=
  Prim.tvarNewIO init

/-- Allocate a new `TVar` inside an `STM` transaction. -/
@[always_inline, inline]
def new (init : α) : STM (TVar α) :=
  ⟨Prim.tvarNewTx init⟩

/-- Read the current transactional value of `tvar`. -/
@[always_inline, inline]
def read (tvar : TVar α) : STM α :=
  ⟨Prim.tvarRead tvar⟩

/-- Write `val` to `tvar` in the current transaction's write buffer. -/
@[always_inline, inline]
def write (tvar : TVar α) (val : α) : STM Unit :=
  ⟨do
    let st ← Prim.tvarWrite tvar val
    if st == 0 then Pure.pure (.ok ()) else Pure.pure .conflict⟩

/-- Modify `tvar` with pure function `f`. -/
@[always_inline, inline]
def modify (tvar : TVar α) (f : α → α) : STM Unit := do
  let v ← tvar.read
  tvar.write (f v)

/-- Swap the value in `tvar`, returning the old value. -/
@[always_inline, inline]
def swap (tvar : TVar α) (newVal : α) : STM α := do
  let old ← tvar.read
  tvar.write newVal
  return old

/--
Wait-free single-variable snapshot read in `BaseIO` (protected by Fraser EBR, zero cache-line writes).
Equivalent to `atomically tvar.read` for a single variable without initializing a transaction log.
-/
@[always_inline, inline]
def readIO (tvar : TVar α) : BaseIO α :=
  Prim.tvarReadIO tvar

/-- Unique, strictly monotonic identifier assigned to this `TVar` at creation. -/
@[always_inline, inline]
def id (tvar : TVar α) : UInt64 :=
  Prim.tvarId tvar

instance : BEq (TVar α) where
  beq a b := a.id == b.id

end TVar

export STM (atomically atomicallyWith atomicallyReadOnly retry check)

end STM
