/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace STM

/--
Internal outcome of a single speculative transaction attempt on the thread-local engine.
 Constructor indices MUST match `c/lean_stm.cpp`:
 - `0`: `ok val`
 - `1`: `retry` (`lean_box(1)`)
 - `2`: `conflict` (`lean_box(2)`)
 - `3`: `userError err`
-/
inductive TxOutcome (α : Type) where
  | ok (val : α)
  | retry
  | conflict
  | userError (err : IO.Error)

/--
Selectable STM concurrency control protocol.
Must match `enum StmProtocol` in `c/lean_stm.cpp`.
-/
inductive Protocol where
  /-- Transactional Locking II + GV4 Safe CAS Clock + Lazy Snapshot Extension + Adaptive MVCC Read Fallback (Default). -/
  | tl2Lsa
  /-- Baseline TL2 with unconditional `fetch_add` global clock and no LSA extension. -/
  | tl2Gv1
  /-- Wait-free read-only snapshot mode using each `TVar`'s 8-version inline MVCC ring. -/
  | mvccReadOnly
  /-- Dalessandro-Spear-Scott `NOrec`: single global sequence lock + ABA-free Perceus pointer validation. -/
  | norec
  deriving Repr, DecidableEq, Inhabited

namespace Protocol

@[inline] def toUInt8 : Protocol → UInt8
  | .tl2Lsa       => 0
  | .tl2Gv1       => 1
  | .mvccReadOnly => 2
  | .norec        => 3

@[inline] def ofUInt8 : UInt8 → Protocol
  | 0 => .tl2Lsa
  | 1 => .tl2Gv1
  | 2 => .mvccReadOnly
  | _ => .norec

end Protocol

/--
Runtime telemetry counters aggregated across all worker threads.
Layout matches `lean_stm_get_stats` (0 object pointers, 7 × `UInt64` scalar payload).
-/
structure Stats where
  commits          : UInt64
  abortsConflict   : UInt64
  abortsValidation : UInt64
  retriesParked    : UInt64
  lsaExtensions    : UInt64
  mvccSnapshots    : UInt64
  gv4Elisions      : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace Stats

def totalAborts (s : Stats) : UInt64 :=
  s.abortsConflict + s.abortsValidation

def abortRatePct (s : Stats) : Float :=
  let attempts := s.commits + s.totalAborts
  if attempts == 0 then 0.0
  else (s.totalAborts.toFloat * 100.0) / attempts.toFloat

end Stats

private opaque TVarPointed : NonemptyType.{0}

/--
A transactional mutable variable holding a value of type `α`.
Backed by a 128-byte cache-line-aligned C++20 versioned cell with an 8-slot inline MVCC ring,
Dekker-synchronized `retry` wait queue, and Fraser Epoch-Based Reclamation for Lean RC safety.
-/
structure TVar (α : Type) : Type where
  private mk ::
  private ptr : TVarPointed.type
  private h   : Nonempty α

instance {α : Type} [s : Nonempty α] : Nonempty (TVar α) :=
  ⟨{ ptr := Classical.choice TVarPointed.property, h := s }⟩

namespace Prim

private noncomputable def inhabitedOutcomeFromTVar {α : Type} (r : TVar α) : BaseIO (TxOutcome α) :=
  let _ : Inhabited α := Classical.inhabited_of_nonempty r.h
  pure (.ok default)

private noncomputable def inhabitedBaseIOFromTVar {α : Type} (r : TVar α) : BaseIO α :=
  let _ : Inhabited α := Classical.inhabited_of_nonempty r.h
  pure default

@[extern "lean_stm_tvar_new_io"]
opaque tvarNewIO {α : Type} (init : α) : BaseIO (TVar α) :=
  pure { ptr := Classical.choice TVarPointed.property, h := ⟨init⟩ }

@[extern "lean_stm_tvar_new_tx"]
opaque tvarNewTx {α : Type} (init : α) : BaseIO (TxOutcome (TVar α)) :=
  pure (.ok { ptr := Classical.choice TVarPointed.property, h := ⟨init⟩ })

@[extern "lean_stm_tvar_read_io"]
opaque tvarReadIO {α : Type} (tvar : @& TVar α) : BaseIO α :=
  inhabitedBaseIOFromTVar tvar

@[extern "lean_stm_tvar_id"]
opaque tvarId {α : Type} (tvar : @& TVar α) : UInt64

@[extern "lean_stm_tx_begin"]
opaque txBegin (proto : UInt8) (attempt : UInt32) : BaseIO Unit

@[extern "lean_stm_tvar_read"]
opaque tvarRead {α : Type} (tvar : @& TVar α) : BaseIO (TxOutcome α) :=
  inhabitedOutcomeFromTVar tvar

@[extern "lean_stm_tvar_write"]
opaque tvarWrite {α : Type} (tvar : @& TVar α) (val : α) : BaseIO UInt8

@[extern "lean_stm_tx_savepoint"]
opaque txSavepoint : BaseIO UInt64

@[extern "lean_stm_tx_rollback_savepoint"]
opaque txRollbackSavepoint (sp : UInt64) : BaseIO Unit

@[extern "lean_stm_tx_commit_savepoint"]
opaque txCommitSavepoint (sp : UInt64) : BaseIO Unit

@[extern "lean_stm_tx_commit"]
opaque txCommit : BaseIO Bool

@[extern "lean_stm_tx_abort"]
opaque txAbort : BaseIO Unit

@[extern "lean_stm_tx_park_retry"]
opaque txParkRetry : BaseIO Unit

@[extern "lean_stm_get_default_protocol"]
opaque getDefaultProtocolRaw : BaseIO UInt8

@[extern "lean_stm_set_default_protocol"]
opaque setDefaultProtocolRaw (proto : UInt8) : BaseIO Unit

@[extern "lean_stm_get_stats"]
opaque getStats : BaseIO Stats

@[extern "lean_stm_reset_stats"]
opaque resetStats : BaseIO Unit

end Prim
end STM
