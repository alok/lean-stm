/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.HashMap
import STM.Core

namespace STM

private structure ChanLog (α : Type) where
  nextSeq : Nat := 0
  entries : Std.HashMap Nat α := ∅

/--
Unbounded multicast / broadcast transactional channel (`TChan α`).

Supports `dup` and `clone`: each subscriber owns an independent transactional `cursor : TVar Nat`
plus a local `pushback : TVar (List α)` buffer for `unGet`, reading from a shared transactional
sequence log without copying messages per subscriber and without `unsafe` recursive references.
-/
structure TChan (α : Type) where
  private log      : TVar (ChanLog α)
  private cursor   : TVar Nat
  private pushback : TVar (List α)

namespace TChan

/-- Create a standard channel with one active read cursor at sequence 0. -/
def new : STM (TChan α) := do
  let log ← TVar.new {}
  let cur ← TVar.new 0
  let pb  ← TVar.new []
  return { log, cursor := cur, pushback := pb }

def newIO : BaseIO (TChan α) := do
  let log ← TVar.newIO {}
  let cur ← TVar.newIO 0
  let pb  ← TVar.newIO []
  return { log, cursor := cur, pushback := pb }

/-- Create a broadcast channel; attach subscribers via `dup`. -/
def newBroadcast : STM (TChan α) :=
  new

def newBroadcastIO : BaseIO (TChan α) :=
  newIO

/-- Publish `a` to all active and future `dup` subscribers at the current sequence offset. -/
def write (ch : TChan α) (a : α) : STM Unit := do
  let st ← ch.log.read
  ch.log.write {
    nextSeq := st.nextSeq + 1
    entries := st.entries.insert st.nextSeq a
  }

/-- Read the next item from this cursor; blocks (`retry` on `log` and `pushback`) until published. -/
def read (ch : TChan α) : STM α := do
  match (← ch.pushback.read) with
  | x :: xs =>
    ch.pushback.write xs
    return x
  | [] =>
    let pos ← ch.cursor.read
    let st  ← ch.log.read
    check (pos < st.nextSeq)
    match st.entries[pos]? with
    | some a =>
      ch.cursor.write (pos + 1)
      return a
    | none => retry

def tryRead (ch : TChan α) : STM (Option α) :=
  (some <$> ch.read) <|> pure none

def peek (ch : TChan α) : STM α := do
  match (← ch.pushback.read) with
  | x :: _ => return x
  | [] =>
    let pos ← ch.cursor.read
    let st  ← ch.log.read
    check (pos < st.nextSeq)
    match st.entries[pos]? with
    | some a => return a
    | none   => retry

/-- Push `a` onto the front of *this* subscriber's cursor (`unGetTChan`). -/
def unGet (ch : TChan α) (a : α) : STM Unit := do
  let xs ← ch.pushback.read
  ch.pushback.write (a :: xs)

/-- Subscribe a new independent reader cursor starting from future writes to `ch`. -/
def dup (ch : TChan α) : STM (TChan α) := do
  let st ← ch.log.read
  let newCur ← TVar.new st.nextSeq
  let newPb  ← TVar.new []
  return { log := ch.log, cursor := newCur, pushback := newPb }

/-- Clone a reader cursor starting at the exact same unread position as `ch`. -/
def clone (ch : TChan α) : STM (TChan α) := do
  let pos ← ch.cursor.read
  let pb  ← ch.pushback.read
  let newCur ← TVar.new pos
  let newPb  ← TVar.new pb
  return { log := ch.log, cursor := newCur, pushback := newPb }

def isEmpty (ch : TChan α) : STM Bool := do
  match (← ch.pushback.read) with
  | _ :: _ => return false
  | [] =>
    let pos ← ch.cursor.read
    let st  ← ch.log.read
    return pos >= st.nextSeq

end TChan
end STM
