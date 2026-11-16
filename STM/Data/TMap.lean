/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.HashMap
import STM.Core

namespace STM

/--
Striped Transactional Hash Map inspired by **Software Transactional Objects (STO)**
(`Herman et al., EuroSys 2016`) and **CCSTM** (`Bronson et al., PPoPP 2010`).

### Why Striped `TVar`s?
Wrapping a single `Std.HashMap κ ν` in one `TVar` causes *false conflicts*: two threads inserting
completely unrelated keys abort each other! `TMap` shards keys across $2^b$ cache-line-isolated
`TVar` buckets (64 stripes by default):
- Disjoint single-key operations (`get?`, `insert`, `erase`, `modify`) scale linearly across cores.
- Multi-key operations (`moveKey`, cross-key invariants, whole-map consistent `toList` via
  `atomicallyReadOnly`) remain **100% atomic and opaque** — impossible with `ConcurrentHashMap`!
-/
structure TMap (κ : Type) (ν : Type) [BEq κ] [Hashable κ] where
  private stripes : Array (TVar (Std.HashMap κ ν))
  private mask    : USize
  private h_nonempty : stripes.size > 0

namespace TMap

private def nextPow2 (n : Nat) : Nat :=
  let rec go (p : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => p
    | fuel' + 1 => if p >= n then p else go (p * 2) fuel'
  go 1 32

/-- Create a striped transactional map with `numStripes` (rounded up to a power of 2, default 64). -/
def newIO [BEq κ] [Hashable κ] (numStripes : Nat := 64) : BaseIO (TMap κ ν) := do
  let cap := max 1 (nextPow2 numStripes)
  let mut arr : Array (TVar (Std.HashMap κ ν)) := Array.mkEmpty cap
  for _ in [0:cap] do
    let tv ← TVar.newIO (∅ : Std.HashMap κ ν)
    arr := arr.push tv
  if h : arr.size > 0 then
    return { stripes := arr, mask := (arr.size - 1).toUSize, h_nonempty := h }
  else
    let tv ← TVar.newIO (∅ : Std.HashMap κ ν)
    return { stripes := #[tv], mask := 0, h_nonempty := by simp }

def new [BEq κ] [Hashable κ] (numStripes : Nat := 64) : STM (TMap κ ν) := do
  let cap := max 1 (nextPow2 numStripes)
  let mut arr : Array (TVar (Std.HashMap κ ν)) := Array.mkEmpty cap
  for _ in [0:cap] do
    let tv ← TVar.new (∅ : Std.HashMap κ ν)
    arr := arr.push tv
  if h : arr.size > 0 then
    return { stripes := arr, mask := (arr.size - 1).toUSize, h_nonempty := h }
  else
    let tv ← TVar.new (∅ : Std.HashMap κ ν)
    return { stripes := #[tv], mask := 0, h_nonempty := by simp }

@[inline] private def bucketFor [BEq κ] [Hashable κ] (m : TMap κ ν) (k : κ) : TVar (Std.HashMap κ ν) :=
  let h := hash k
  let mixed := h ^^^ (h >>> 32)
  let idx := (mixed.toUSize &&& m.mask).toNat
  if hlt : idx < m.stripes.size then
    m.stripes[idx]
  else
    m.stripes[0]'m.h_nonempty

@[inline] def get? [BEq κ] [Hashable κ] (m : TMap κ ν) (k : κ) : STM (Option ν) := do
  let b ← (m.bucketFor k).read
  return b[k]?

/-- Lookup `k`, blocking via `retry` until `k` is present in the map! -/
@[inline] def getWait [BEq κ] [Hashable κ] (m : TMap κ ν) (k : κ) : STM ν := do
  match (← m.get? k) with
  | some v => return v
  | none   => retry

@[inline] def contains [BEq κ] [Hashable κ] (m : TMap κ ν) (k : κ) : STM Bool := do
  let b ← (m.bucketFor k).read
  return b.contains k

@[inline] def insert [BEq κ] [Hashable κ] (m : TMap κ ν) (k : κ) (v : ν) : STM Unit := do
  let tv := m.bucketFor k
  let b ← tv.read
  tv.write (b.insert k v)

@[inline] def erase [BEq κ] [Hashable κ] (m : TMap κ ν) (k : κ) : STM Unit := do
  let tv := m.bucketFor k
  let b ← tv.read
  tv.write (b.erase k)

@[inline] def modify [BEq κ] [Hashable κ] (m : TMap κ ν) (k : κ) (f : ν → ν) : STM Bool := do
  let tv := m.bucketFor k
  let b ← tv.read
  match b[k]? with
  | some v =>
    tv.write (b.insert k (f v))
    return true
  | none =>
    return false

@[inline] def upsert [BEq κ] [Hashable κ] (m : TMap κ ν) (k : κ) (init : ν) (f : ν → ν) : STM ν := do
  let tv := m.bucketFor k
  let b ← tv.read
  let next := match b[k]? with
    | some v => f v
    | none   => init
  tv.write (b.insert k next)
  return next

/-- Consistent cross-stripe total entry count. Pair with `atomicallyReadOnly` for wait-free snapshots! -/
def size [BEq κ] [Hashable κ] (m : TMap κ ν) : STM Nat := do
  let mut total := 0
  for tv in m.stripes do
    let b ← tv.read
    total := total + b.size
  return total

/-- Consistent cross-stripe snapshot of all key-value pairs. -/
def toList [BEq κ] [Hashable κ] (m : TMap κ ν) : STM (List (κ × ν)) := do
  let mut acc : List (κ × ν) := []
  for tv in m.stripes do
    let b ← tv.read
    acc := b.toList ++ acc
  return acc

end TMap
end STM
