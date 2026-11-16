/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Core

namespace STM

/--
Unbounded amortized $O(1)$ FIFO transactional queue (`Marlow, GHC Control.Concurrent.STM.TQueue`).

Uses separate `readEnd` and `writeEnd` `TVar`s so concurrent producers (`write`) and consumers (`read`)
operate on disjoint `TVar`s whenever `readEnd` is non-empty.
-/
structure TQueue (α : Type) where
  private readEnd  : TVar (List α)
  private writeEnd : TVar (List α)

namespace TQueue

def new : STM (TQueue α) := do
  let r ← TVar.new []
  let w ← TVar.new []
  return { readEnd := r, writeEnd := w }

def newIO : BaseIO (TQueue α) := do
  let r ← TVar.newIO []
  let w ← TVar.newIO []
  return { readEnd := r, writeEnd := w }

/-- Enqueue `a` at the back of `q` in $O(1)$ time (touches only `writeEnd`). -/
@[inline] def write (q : TQueue α) (a : α) : STM Unit := do
  let ws ← q.writeEnd.read
  q.writeEnd.write (a :: ws)

/-- Dequeue from the front of `q`; blocks (`retry` on both ends) if empty. -/
def read (q : TQueue α) : STM α := do
  match (← q.readEnd.read) with
  | x :: xs =>
    q.readEnd.write xs
    return x
  | [] =>
    match (← q.writeEnd.read) with
    | [] => retry
    | ws =>
      q.writeEnd.write []
      match ws.reverse with
      | x :: xs =>
        q.readEnd.write xs
        return x
      | [] => retry

/-- Non-blocking dequeue: returns `some a` if available, `none` if empty. -/
def tryRead (q : TQueue α) : STM (Option α) :=
  (some <$> q.read) <|> pure none

/-- Peek at the front element without removing it; blocks (`retry`) if empty. -/
def peek (q : TQueue α) : STM α := do
  let x ← q.read
  let rs ← q.readEnd.read
  q.readEnd.write (x :: rs)
  return x

/-- Push an item back onto the front of `q`. -/
@[inline] def unGet (q : TQueue α) (a : α) : STM Unit := do
  let rs ← q.readEnd.read
  q.readEnd.write (a :: rs)

def isEmpty (q : TQueue α) : STM Bool := do
  match (← q.readEnd.read) with
  | _ :: _ => return false
  | [] =>
    match (← q.writeEnd.read) with
    | _ :: _ => return false
    | []     => return true

end TQueue
end STM
