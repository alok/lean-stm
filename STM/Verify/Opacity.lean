/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Guerraoui-Kapalka Opacity & Sequential Specification (`STM.Verify.Opacity`)

Formalizes **Opacity** (*Guerraoui & Kapalka, PPoPP 2008*), the standard correctness condition for
Software Transactional Memory:
1. **Committed Serializability**: All committed transactions execute atomically in a total order
   producing valid sequential memory snapshots $M_0, M_1, \dots, M_n$.
2. **Consistent Read Views for ALL Transactions (Including Live & Aborted)**: Even an active or
   doomed-to-abort transaction NEVER observes a torn/inconsistent view of memory; its entire read-set
   is consistent with a single committed memory snapshot $M_k$.
3. **Real-Time Order Preservation**: For every transaction $T$, its read snapshot index $k$ is at
   least the committed memory index $b_T$ that existed when $T$ began ($b_T \le k$), and if $T$
   commits a write, it validates against the latest committed snapshot $M_n$ and produces $M_{n+1}$.
-/

namespace STM.Verify

abbrev Loc  := Nat
abbrev Val  := Nat
abbrev TxId := Nat
abbrev Mem  := Loc → Val

/-- Update a single memory location. -/
def Mem.update (m : Mem) (loc : Loc) (v : Val) : Mem :=
  fun x => if x = loc then v else m x

@[simp] theorem Mem.update_same (m : Mem) (loc : Loc) (v : Val) :
    (m.update loc v) loc = v := by
  simp [Mem.update]

@[simp] theorem Mem.update_ne (m : Mem) {loc x : Loc} (v : Val) (h : x ≠ loc) :
    (m.update loc v) x = m x := by
  simp [Mem.update, h]

/-- Apply a buffered write-set (in order) to memory snapshot `m`. -/
def applyWriteSet (m : Mem) (ws : List (Loc × Val)) : Mem :=
  ws.foldl (fun acc (loc, v) => acc.update loc v) m

/-- Lookup the latest buffered write for `loc` in `ws` (searching from most recent at the back). -/
def lookupWriteSet (ws : List (Loc × Val)) (loc : Loc) : Option Val :=
  match ws.reverse.find? (fun p => p.1 == loc) with
  | some (_, v) => some v
  | none        => none

/-- `lookupWriteSet` agrees with `applyWriteSet` on every location! -/
theorem applyWriteSet_eq_lookup (m : Mem) (ws : List (Loc × Val)) (loc : Loc) :
    applyWriteSet m ws loc = (lookupWriteSet ws loc).getD (m loc) := by
  induction ws generalizing m with
  | nil =>
    simp [applyWriteSet, lookupWriteSet]
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    change applyWriteSet (m.update k v) tl loc = (lookupWriteSet ((k, v) :: tl) loc).getD (m loc)
    rw [ih (m.update k v)]
    simp only [lookupWriteSet, List.reverse_cons, List.find?_append]
    cases hfind : tl.reverse.find? (fun p => p.1 == loc) with
    | some p =>
      rcases p with ⟨k', v'⟩
      simp
    | none =>
      simp only [Option.or, List.find?_cons, List.find?_nil]
      by_cases hk : k = loc
      · subst hk; simp
      · have hne : (k == loc) = false := beq_false_of_ne hk
        have hne' : loc ≠ k := fun h => hk h.symm
        simp [hne, hne']

/-- Lifecycle status of a transaction in a concurrent execution. -/
inductive TxStatus where
  | active
  | committed
  | aborted
  deriving Repr, DecidableEq

/-- Abstract record of a transaction's externally observable reads, writes, and real-time bounds. -/
structure TxView where
  status    : TxStatus
  beginSnap : Nat
  /-- External memory reads `(loc, val)` (reads NOT satisfied by the transaction's own prior writes). -/
  extReads  : List (Loc × Val)
  writeSet  : List (Loc × Val)

/--
**Snapshot Opacity Criterion** relative to a non-empty committed snapshot sequence `snaps`:
Every transaction `tx` (whether `active`, `committed`, or `aborted`!) possesses a witness committed
snapshot index `k < snaps.length` with `tx.beginSnap ≤ k` such that EVERY external read `(loc, v)`
performed by `tx` equals `snaps[k] loc`!
-/
def ConsistentWithSnapshot (snaps : List Mem) (tx : TxView) : Prop :=
  ∃ (k : Nat) (hk : k < snaps.length),
    tx.beginSnap ≤ k ∧
    ∀ loc val, (loc, val) ∈ tx.extReads → snaps[k] loc = val

/--
**Global Invariant Preservation under Opacity**:
If every committed snapshot in `snaps` satisfies global invariant `Inv : Mem → Prop`, and a
transaction `tx` (even live or doomed to abort!) satisfies `ConsistentWithSnapshot snaps tx`,
then there exists a valid state `M` satisfying `Inv M` that simultaneously explains EVERY read
performed by `tx`!
-/
theorem opaque_tx_observes_valid_invariant {snaps : List Mem} {Inv : Mem → Prop}
    (h_inv : ∀ m ∈ snaps, Inv m)
    {tx : TxView} (h_op : ConsistentWithSnapshot snaps tx) :
    ∃ M : Mem, Inv M ∧ ∀ loc val, (loc, val) ∈ tx.extReads → M loc = val := by
  rcases h_op with ⟨k, hk, _, hreads⟩
  refine ⟨snaps[k], h_inv snaps[k] (List.getElem_mem hk), hreads⟩

end STM.Verify
