/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Core

namespace STM

/--
Bounded FIFO transactional queue with **Split-Counter Capacity Tracking**
(`Marlow, GHC Control.Concurrent.STM.TBQueue`).

### Disjoint-Access Parallelism Design
Instead of a single shared `size : TVar Nat` (which forces every producer and every consumer to
contend on the same cache line!), capacity is partitioned across two `TVar`s:
- `readCap`: freed slots accumulated by consumers (`read` increments `readCap`).
- `writeCap`: available slots remaining for producers (`write` decrements `writeCap`).

Producers only read `readCap` when `writeCap == 0`, transferring all accumulated credits in bulk!
Global invariant (formally verified in `STM.Verify.Examples`):
  `readCap + writeCap + readEnd.length + writeEnd.length = capacity`.
-/
structure TBQueue (α : Type) where
  capacity : Nat
  private readEnd  : TVar (List α)
  private readCap  : TVar Nat
  private writeEnd : TVar (List α)
  private writeCap : TVar Nat

namespace TBQueue

def new (capacity : Nat) : STM (TBQueue α) := do
  let rEnd ← TVar.new []
  let rCap ← TVar.new 0
  let wEnd ← TVar.new []
  let wCap ← TVar.new capacity
  return { capacity, readEnd := rEnd, readCap := rCap, writeEnd := wEnd, writeCap := wCap }

def newIO (capacity : Nat) : BaseIO (TBQueue α) := do
  let rEnd ← TVar.newIO []
  let rCap ← TVar.newIO 0
  let wEnd ← TVar.newIO []
  let wCap ← TVar.newIO capacity
  return { capacity, readEnd := rEnd, readCap := rCap, writeEnd := wEnd, writeCap := wCap }

/-- Enqueue `a`; blocks (`retry`) when queue is at full capacity. -/
def write (q : TBQueue α) (a : α) : STM Unit := do
  let w ← q.writeCap.read
  if w > 0 then
    q.writeCap.write (w - 1)
  else
    let r ← q.readCap.read
    if r > 0 then
      q.readCap.write 0
      q.writeCap.write (r - 1)
    else
      retry
  let ws ← q.writeEnd.read
  q.writeEnd.write (a :: ws)

/-- Non-blocking enqueue: returns `true` if enqueued, `false` if full. -/
def tryWrite (q : TBQueue α) (a : α) : STM Bool :=
  (q.write a *> pure true) <|> pure false

/-- Dequeue front element; blocks (`retry`) when queue is empty. -/
def read (q : TBQueue α) : STM α := do
  let r ← q.readCap.read
  q.readCap.write (r + 1)
  match (← q.readEnd.read) with
  | x :: xs =>
    q.readEnd.write xs
    return x
  | [] =>
    match (← q.writeEnd.read) with
    | [] => retry -- rolls back `readCap.write (r + 1)` automatically!
    | ws =>
      q.writeEnd.write []
      match ws.reverse with
      | x :: xs =>
        q.readEnd.write xs
        return x
      | [] => retry

/-- Non-blocking dequeue: returns `some a` if available, `none` if empty. -/
def tryRead (q : TBQueue α) : STM (Option α) :=
  (some <$> q.read) <|> pure none

/-- Drain all currently queued elements in FIFO order without blocking. -/
def flush (q : TBQueue α) : STM (List α) := do
  let rs ← q.readEnd.read
  let ws ← q.writeEnd.read
  if rs.isEmpty && ws.isEmpty then
    return []
  q.readEnd.write []
  q.writeEnd.write []
  q.readCap.write 0
  q.writeCap.write q.capacity
  return rs ++ ws.reverse

def isEmpty (q : TBQueue α) : STM Bool := do
  match (← q.readEnd.read) with
  | _ :: _ => return false
  | [] =>
    match (← q.writeEnd.read) with
    | _ :: _ => return false
    | []     => return true

def isFull (q : TBQueue α) : STM Bool := do
  let w ← q.writeCap.read
  if w > 0 then return false
  let r ← q.readCap.read
  return r == 0

end TBQueue

/--
Baseline single-counter bounded queue used in Autoresearch benchmarks to isolate the throughput
gain of `TBQueue`'s split-counter design under concurrent producer/consumer workloads.
-/
structure NaiveTBQueue (α : Type) where
  capacity : Nat
  private items : TVar (List α × List α)
  private count : TVar Nat

namespace NaiveTBQueue

def newIO (capacity : Nat) : BaseIO (NaiveTBQueue α) := do
  let items ← TVar.newIO ([], [])
  let count ← TVar.newIO 0
  return { capacity, items, count }

def write (q : NaiveTBQueue α) (a : α) : STM Unit := do
  let n ← q.count.read
  check (n < q.capacity)
  q.count.write (n + 1)
  let (rs, ws) ← q.items.read
  q.items.write (rs, a :: ws)

def read (q : NaiveTBQueue α) : STM α := do
  let n ← q.count.read
  check (n > 0)
  q.count.write (n - 1)
  let (rs, ws) ← q.items.read
  match rs with
  | x :: xs =>
    q.items.write (xs, ws)
    return x
  | [] =>
    match ws.reverse with
    | x :: xs =>
      q.items.write (xs, [])
      return x
    | [] => retry

end NaiveTBQueue

end STM
