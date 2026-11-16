/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Core

namespace STM

/--
A `TMVar α` is a synchronising transactional variable that is either full (holding `some a`)
or empty (`none`). Unlike `IO`-based `MVar`s, multiple `TMVar` operations compose atomically
without lock-ordering deadlocks.
-/
structure TMVar (α : Type) where
  private cell : TVar (Option α)

namespace TMVar

@[inline] def new (a : α) : STM (TMVar α) := do
  return ⟨← TVar.new (some a)⟩

@[inline] def newIO (a : α) : BaseIO (TMVar α) := do
  return ⟨← TVar.newIO (some a)⟩

@[inline] def newEmpty : STM (TMVar α) := do
  return ⟨← TVar.new none⟩

@[inline] def newEmptyIO : BaseIO (TMVar α) := do
  return ⟨← TVar.newIO none⟩

/-- Take the value from `m`, leaving it empty; blocks (`retry`) if currently empty. -/
@[inline] def take (m : TMVar α) : STM α := do
  match (← m.cell.read) with
  | some a =>
    m.cell.write none
    return a
  | none => retry

/-- Put `a` into `m`; blocks (`retry`) if `m` is already full. -/
@[inline] def put (m : TMVar α) (a : α) : STM Unit := do
  match (← m.cell.read) with
  | none => m.cell.write (some a)
  | some _ => retry

/-- Read the value in `m` without emptying it; blocks (`retry`) if empty. -/
@[inline] def read (m : TMVar α) : STM α := do
  match (← m.cell.read) with
  | some a => return a
  | none   => retry

/-- Non-blocking `take`: returns `some a` if full, `none` if empty. -/
@[inline] def tryTake (m : TMVar α) : STM (Option α) := do
  match (← m.cell.read) with
  | some a =>
    m.cell.write none
    return some a
  | none => return none

/-- Non-blocking `put`: returns `true` if stored, `false` if already full. -/
@[inline] def tryPut (m : TMVar α) (a : α) : STM Bool := do
  match (← m.cell.read) with
  | none =>
    m.cell.write (some a)
    return true
  | some _ => return false

/-- Non-blocking `read`: returns `some a` if full, `none` if empty. -/
@[inline] def tryRead (m : TMVar α) : STM (Option α) :=
  m.cell.read

/-- Swap the contents of a full `TMVar` with `newVal`; blocks (`retry`) if empty. -/
@[inline] def swap (m : TMVar α) (newVal : α) : STM α := do
  match (← m.cell.read) with
  | some old =>
    m.cell.write (some newVal)
    return old
  | none => retry

@[inline] def isEmpty (m : TMVar α) : STM Bool := do
  return (← m.cell.read).isNone

end TMVar
end STM
