/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Sync.Mutex

/-!
# Pure-Lean Coarse-Lock Reference STM (`STM.PureRef`)

A zero-FFI reference implementation of Software Transactional Memory built solely on Lean 4's
standard `Std.BaseMutex`, `Std.Condvar`, and `IO.Ref`.

Serves two roles in `lean-stm`:
1. **Differential Oracle**: Reference behavior for testing `retry`, `orElse` rollback, and atomicity.
2. **Performance Baseline (Experiment 0 in Autoresearch)**: Quantifies the exact multi-core speedup
   of `c/lean_stm.cpp` (EBR + 128B-aligned `TVar`s + TL2-LSA/GV4/MVCC) over pure-Lean `IO.Ref` + `Mutex`.
-/

namespace STM.PureRef

private structure GlobalLock where
  mtx : Std.BaseMutex
  cv  : Std.Condvar
  deriving Nonempty

private initialize globalSync : GlobalLock ← do
  let mtx ← Std.BaseMutex.new
  let cv  ← Std.Condvar.new
  return { mtx, cv }

private initialize nextPureId : IO.Ref UInt64 ← IO.mkRef 1

structure PTVar (α : Type) where
  id  : UInt64
  ref : IO.Ref α

private structure UndoAction where
  restore : BaseIO Unit
  deriving Inhabited

inductive PureOutcome (α : Type) where
  | ok (val : α)
  | retry

structure PureSTM (α : Type) where
  run : IO.Ref (Array UndoAction) → BaseIO (PureOutcome α)

namespace PureSTM

@[inline] protected def pure (a : α) : PureSTM α :=
  ⟨fun _ => Pure.pure (.ok a)⟩

@[inline] protected def bind (x : PureSTM α) (f : α → PureSTM β) : PureSTM β :=
  ⟨fun undoRef => do
    match (← x.run undoRef) with
    | .ok a  => (f a).run undoRef
    | .retry => Pure.pure .retry⟩

instance : Monad PureSTM where
  pure := PureSTM.pure
  bind := PureSTM.bind

def retry : PureSTM α :=
  ⟨fun _ => Pure.pure .retry⟩

private def rollbackTo (undoRef : IO.Ref (Array UndoAction)) (sp : Nat) : BaseIO Unit := do
  let mut arr ← undoRef.get
  while h : arr.size > sp do
    let act := arr[arr.size - 1]
    arr := arr.pop
    act.restore
  undoRef.set arr

def orElse (t1 : PureSTM α) (t2 : Unit → PureSTM α) : PureSTM α :=
  ⟨fun undoRef => do
    let sp := (← undoRef.get).size
    match (← t1.run undoRef) with
    | .ok a  => Pure.pure (.ok a)
    | .retry =>
      rollbackTo undoRef sp
      (t2 ()).run undoRef⟩

instance : Alternative PureSTM where
  failure := retry
  orElse  := orElse

def check (b : Bool) : PureSTM Unit :=
  if b then Pure.pure () else retry

def newTVarIO (init : α) : BaseIO (PTVar α) := do
  let id ← nextPureId.modifyGet fun n => (n, n + 1)
  let ref ← IO.mkRef init
  return { id, ref }

def read (v : PTVar α) : PureSTM α :=
  ⟨fun _ => do
    let a ← v.ref.get
    return .ok a⟩

def write (v : PTVar α) (a : α) : PureSTM Unit :=
  ⟨fun undoRef => do
    let old ← v.ref.get
    undoRef.modify fun arr => arr.push { restore := v.ref.set old }
    v.ref.set a
    return .ok ()⟩

partial def atomically (tx : PureSTM α) : IO α := do
  let undoRef ← IO.mkRef #[]
  globalSync.mtx.lock
  let rec loop : IO α := do
    undoRef.set #[]
    match (← tx.run undoRef) with
    | .ok a =>
      let wrote := !(← undoRef.get).isEmpty
      globalSync.mtx.unlock
      if wrote then
        globalSync.cv.notifyAll
      return a
    | .retry =>
      rollbackTo undoRef 0
      globalSync.cv.wait globalSync.mtx
      loop
  loop

end PureSTM
end STM.PureRef
