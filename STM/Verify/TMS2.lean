/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Verify.Opacity

/-!
# Doherty, Groves, Luchangco & Moir's `TMS2` Specification Automaton (`STM.Verify.TMS2`)

`TMS2` (*Doherty et al., FORTE 2009 / Formal Aspects of Computing 2013*) is the canonical
operational specification automaton for proving Opacity of STM implementations via forward
simulation.

We prove mechanically that every reachable state of `TMS2` satisfies `ConsistentWithSnapshot`
for all transactions (active, committed, and aborted)!
-/

namespace STM.Verify

structure TMS2Tx where
  status    : TxStatus
  beginSnap : Nat
  extReads  : List (Loc × Val)
  writeSet  : List (Loc × Val)

def TMS2Tx.toView (t : TMS2Tx) : TxView :=
  { status := t.status, beginSnap := t.beginSnap, extReads := t.extReads, writeSet := t.writeSet }

structure TMS2State where
  memories   : List Mem
  h_nonempty : memories ≠ []
  txs        : TxId → Option TMS2Tx

namespace TMS2State

def init (m0 : Mem) : TMS2State :=
  { memories := [m0], h_nonempty := by simp, txs := fun _ => none }

theorem memories_length_pos (st : TMS2State) : 0 < st.memories.length := by
  cases h : st.memories with
  | nil => exact False.elim (st.h_nonempty h)
  | cons _ _ => simp

def latestIdx (st : TMS2State) : Nat :=
  st.memories.length - 1

theorem latestIdx_lt (st : TMS2State) : st.latestIdx < st.memories.length := by
  have := st.memories_length_pos
  dsimp [latestIdx]
  omega

def latestMem (st : TMS2State) : Mem :=
  st.memories.getLast st.h_nonempty

theorem latestMem_eq_getElem (st : TMS2State) :
    st.latestMem = st.memories[st.latestIdx]'(st.latestIdx_lt) := by
  simp [latestMem, latestIdx, List.getLast_eq_getElem]

/-- Operational transition relation of `TMS2`. -/
inductive Step : TMS2State → TMS2State → Prop where
  | beginTx {st : TMS2State} (tid : TxId) :
      st.txs tid = none →
      Step st { st with
        txs := fun id => if id = tid then some ⟨.active, st.latestIdx, [], []⟩ else st.txs id }

  | readLocal {st : TMS2State} (tid : TxId) (tx : TMS2Tx) (loc : Loc) (val : Val) :
      st.txs tid = some tx →
      tx.status = .active →
      lookupWriteSet tx.writeSet loc = some val →
      Step st st

  | readExternal {st : TMS2State} (tid : TxId) (tx : TMS2Tx) (loc : Loc) (val : Val)
      (n : Nat) (hn : n < st.memories.length) :
      st.txs tid = some tx →
      tx.status = .active →
      lookupWriteSet tx.writeSet loc = none →
      tx.beginSnap ≤ n →
      (∀ l v, (l, v) ∈ tx.extReads → st.memories[n] l = v) →
      st.memories[n] loc = val →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with extReads := (loc, val) :: tx.extReads }
          else st.txs id }

  | writeLocal {st : TMS2State} (tid : TxId) (tx : TMS2Tx) (loc : Loc) (val : Val) :
      st.txs tid = some tx →
      tx.status = .active →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with writeSet := tx.writeSet ++ [(loc, val)] }
          else st.txs id }

  | commitReadOnly {st : TMS2State} (tid : TxId) (tx : TMS2Tx) (n : Nat)
      (hn : n < st.memories.length) :
      st.txs tid = some tx →
      tx.status = .active →
      tx.writeSet = [] →
      tx.beginSnap ≤ n →
      (∀ l v, (l, v) ∈ tx.extReads → st.memories[n] l = v) →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with status := .committed }
          else st.txs id }

  | commitWrite {st : TMS2State} (tid : TxId) (tx : TMS2Tx) :
      st.txs tid = some tx →
      tx.status = .active →
      tx.writeSet ≠ [] →
      (∀ l v, (l, v) ∈ tx.extReads → st.latestMem l = v) →
      Step st {
        memories := st.memories ++ [applyWriteSet st.latestMem tx.writeSet]
        h_nonempty := by simp
        txs := fun id =>
          if id = tid then some { tx with status := .committed }
          else st.txs id }

  | abortTx {st : TMS2State} (tid : TxId) (tx : TMS2Tx) :
      st.txs tid = some tx →
      tx.status = .active →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with status := .aborted }
          else st.txs id }

/-- Reachable `TMS2` configurations from initial memory `m0`. -/
inductive Reachable (m0 : Mem) : TMS2State → Prop where
  | init : Reachable m0 (TMS2State.init m0)
  | step {s1 s2} : Reachable m0 s1 → Step s1 s2 → Reachable m0 s2

/-- Inductive invariant of `TMS2`. -/
def Inv (st : TMS2State) : Prop :=
  ∀ tid tx, st.txs tid = some tx →
    tx.beginSnap < st.memories.length ∧
    ConsistentWithSnapshot st.memories tx.toView

theorem inv_init (m0 : Mem) : Inv (TMS2State.init m0) := by
  intro tid tx h
  simp [TMS2State.init] at h

theorem inv_step {s1 s2 : TMS2State} (hinv : Inv s1) (hstep : Step s1 s2) : Inv s2 := by
  cases hstep with
  | beginTx tid _ =>
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [ ↓reduceIte, Option.some.injEq] at htx
      subst htx
      have hlt := s1.latestIdx_lt
      refine ⟨hlt, ⟨s1.latestIdx, hlt, Nat.le_refl _, ?_⟩⟩
      intro loc val hmem
      simp [TMS2Tx.toView] at hmem
    · simp only [hid, ↓reduceIte] at htx
      exact hinv id tx htx

  | readLocal =>
    exact hinv

  | readExternal tid tx0 loc val n hn hsome _ _ hbeg hprev hcur =>
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      have ⟨hb_lt, _⟩ := hinv id tx0 hsome
      refine ⟨hb_lt, ⟨n, hn, hbeg, ?_⟩⟩
      intro l v hmem
      simp only [TMS2Tx.toView, List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | hmem_old
      · exact hcur
      · exact hprev l v hmem_old
    · simp only [hid, ↓reduceIte] at htx
      exact hinv id tx htx

  | writeLocal tid tx0 _ _ hsome _ =>
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      exact hinv id tx0 hsome
    · simp only [hid, ↓reduceIte] at htx
      exact hinv id tx htx

  | commitReadOnly tid tx0 n hn hsome _ _ hbeg hreads =>
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      have ⟨hb_lt, _⟩ := hinv id tx0 hsome
      exact ⟨hb_lt, ⟨n, hn, hbeg, hreads⟩⟩
    · simp only [hid, ↓reduceIte] at htx
      exact hinv id tx htx

  | commitWrite tid tx0 hsome _ _ hreads_latest =>
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      have ⟨hb_lt, _⟩ := hinv id tx0 hsome
      have hk_lt_old := s1.latestIdx_lt
      have hk_lt_new : s1.latestIdx < (s1.memories ++ [applyWriteSet s1.latestMem tx0.writeSet]).length := by
        simp; omega
      have hbeg_le : tx0.beginSnap ≤ s1.latestIdx := by dsimp [latestIdx]; omega
      refine ⟨by simp; omega, ⟨s1.latestIdx, hk_lt_new, hbeg_le, ?_⟩⟩
      intro l v hmem
      rw [List.getElem_append_left hk_lt_old]
      rw [← s1.latestMem_eq_getElem]
      exact hreads_latest l v hmem
    · simp only [hid, ↓reduceIte] at htx
      have ⟨hb_lt, ⟨k, hk, hbeg, hk_reads⟩⟩ := hinv id tx htx
      have hk_new : k < (s1.memories ++ [applyWriteSet s1.latestMem tx0.writeSet]).length := by
        simp; omega
      refine ⟨by simp; omega, ⟨k, hk_new, hbeg, ?_⟩⟩
      intro l v hmem
      rw [List.getElem_append_left hk]
      exact hk_reads l v hmem

  | abortTx tid tx0 hsome _ =>
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      exact hinv id tx0 hsome
    · simp only [hid, ↓reduceIte] at htx
      exact hinv id tx htx

/--
**Master Theorem (`TMS2 ⟹ Opacity`)**:
Every reachable state of `TMS2` guarantees `ConsistentWithSnapshot` for ALL transactions
(active, committed, and aborted).
-/
theorem reachable_opaque {m0 : Mem} {st : TMS2State} (hr : Reachable m0 st) :
    ∀ tid tx, st.txs tid = some tx → ConsistentWithSnapshot st.memories tx.toView := by
  have hinv : Inv st := by
    induction hr with
    | init => exact inv_init m0
    | step _ hs ih => exact inv_step ih hs
  intro tid tx htx
  exact (hinv tid tx htx).2

end TMS2State
end STM.Verify
