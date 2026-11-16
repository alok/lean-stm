/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Verify.Opacity

/-!
# Concrete `NOrec` Seqlock & Value-Based Validation Soundness (`STM.Verify.NOrec`)

Formalizes **NOrec** (*Dalessandro, Spear, Scott, PPoPP 2010*) and proves mechanically
(`norec_reachable_opaque`) that value-based snapshot validation & extension guarantees
`ConsistentWithSnapshot` across all active, committed, and aborted transactions!
-/

namespace STM.Verify

structure NOrecTx where
  status    : TxStatus
  beginSnap : Nat
  /-- Observed even sequence lock value (`2 * snapIdx`). -/
  rvSeq     : Nat
  readLog   : List (Loc × Val)
  writeBuf  : List (Loc × Val)

def NOrecTx.toView (tx : NOrecTx) : TxView :=
  { status := tx.status, beginSnap := tx.beginSnap, extReads := tx.readLog, writeSet := tx.writeBuf }

structure NOrecState where
  seq   : Nat
  mem   : Mem
  snaps : List Mem
  txs   : TxId → Option NOrecTx

namespace NOrecState

def init (m0 : Mem) : NOrecState :=
  { seq := 0, mem := m0, snaps := [m0], txs := fun _ => none }

inductive Step : NOrecState → NOrecState → Prop where
  | beginTx {st : NOrecState} (tid : TxId) :
      st.seq % 2 = 0 →
      st.txs tid = none →
      Step st { st with
        txs := fun id =>
          if id = tid then some ⟨.active, st.seq / 2, st.seq, [], []⟩
          else st.txs id }

  | readLocal {st : NOrecState} (tid : TxId) (tx : NOrecTx) (loc : Loc) (val : Val) :
      st.txs tid = some tx →
      tx.status = .active →
      lookupWriteSet tx.writeBuf loc = some val →
      Step st st

  | readConsistent {st : NOrecState} (tid : TxId) (tx : NOrecTx) (loc : Loc) :
      st.txs tid = some tx →
      tx.status = .active →
      lookupWriteSet tx.writeBuf loc = none →
      st.seq = tx.rvSeq →
      st.seq % 2 = 0 →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with readLog := (loc, st.mem loc) :: tx.readLog }
          else st.txs id }

  | validateExtend {st : NOrecState} (tid : TxId) (tx : NOrecTx) :
      st.txs tid = some tx →
      tx.status = .active →
      st.seq % 2 = 0 →
      (∀ l v, (l, v) ∈ tx.readLog → st.mem l = v) →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with rvSeq := st.seq }
          else st.txs id }

  | writeBuf {st : NOrecState} (tid : TxId) (tx : NOrecTx) (loc : Loc) (val : Val) :
      st.txs tid = some tx →
      tx.status = .active →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with writeBuf := tx.writeBuf ++ [(loc, val)] }
          else st.txs id }

  | commitReadOnly {st : NOrecState} (tid : TxId) (tx : NOrecTx) :
      st.txs tid = some tx →
      tx.status = .active →
      tx.writeBuf = [] →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with status := .committed }
          else st.txs id }

  | commitWrite {st : NOrecState} (tid : TxId) (tx : NOrecTx) :
      st.txs tid = some tx →
      tx.status = .active →
      tx.writeBuf ≠ [] →
      st.seq = tx.rvSeq →
      st.seq % 2 = 0 →
      Step st {
        seq   := st.seq + 2
        mem   := applyWriteSet st.mem tx.writeBuf
        snaps := st.snaps ++ [applyWriteSet st.mem tx.writeBuf]
        txs   := fun id =>
          if id = tid then some { tx with status := .committed }
          else st.txs id }

  | abortTx {st : NOrecState} (tid : TxId) (tx : NOrecTx) :
      st.txs tid = some tx →
      tx.status = .active →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with status := .aborted }
          else st.txs id }

inductive Reachable (m0 : Mem) : NOrecState → Prop where
  | init : Reachable m0 (NOrecState.init m0)
  | step {s1 s2} : Reachable m0 s1 → Step s1 s2 → Reachable m0 s2

structure Inv (st : NOrecState) : Prop where
  h_even : st.seq % 2 = 0
  h_len  : st.snaps.length = st.seq / 2 + 1
  h_mem  : st.snaps[st.seq / 2]? = some st.mem
  h_tx   : ∀ tid tx, st.txs tid = some tx →
             tx.rvSeq % 2 = 0 ∧
             tx.beginSnap ≤ tx.rvSeq / 2 ∧
             tx.rvSeq / 2 ≤ st.seq / 2 ∧
             ∃ snap, st.snaps[tx.rvSeq / 2]? = some snap ∧
               ∀ l v, (l, v) ∈ tx.readLog → snap l = v

theorem inv_init (m0 : Mem) : Inv (NOrecState.init m0) := by
  refine ⟨by simp [init], by simp [init], by simp [init], ?_⟩
  intro tid tx htx; simp [init] at htx

theorem inv_step {s1 s2 : NOrecState} (hinv : Inv s1) (hstep : Step s1 s2) : Inv s2 := by
  have heven := hinv.h_even
  have hlen  := hinv.h_len
  cases hstep with
  | beginTx tid _ _ =>
    refine ⟨heven, hlen, hinv.h_mem, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      refine ⟨heven, Nat.le_refl _, Nat.le_refl _, ⟨s1.mem, hinv.h_mem, ?_⟩⟩
      intro l v hmem; simp at hmem
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | readLocal =>
    exact hinv

  | readConsistent tid tx0 loc hsome _ _ hseq_eq _ =>
    refine ⟨heven, hlen, hinv.h_mem, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      have ⟨hrv_even, hbeg, hrv_le, ⟨snap, hsnap_eq, hreads⟩⟩ := hinv.h_tx id tx0 hsome
      have hdiv : tx0.rvSeq / 2 = s1.seq / 2 := by rw [hseq_eq]
      have hsnap_mem : snap = s1.mem := by
        rw [hdiv, hinv.h_mem] at hsnap_eq
        injection hsnap_eq with heq
        exact heq.symm
      refine ⟨hrv_even, hbeg, hrv_le, ⟨snap, hsnap_eq, ?_⟩⟩
      intro l v hmem
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | hold
      · rw [hsnap_mem]
      · exact hreads l v hold
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | validateExtend tid tx0 hsome _ _ hval =>
    refine ⟨heven, hlen, hinv.h_mem, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      have ⟨_, hbeg, hrv_le, _⟩ := hinv.h_tx id tx0 hsome
      refine ⟨heven, Nat.le_trans hbeg hrv_le, Nat.le_refl _, ⟨s1.mem, hinv.h_mem, hval⟩⟩
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | writeBuf tid tx0 _ _ hsome _ =>
    refine ⟨heven, hlen, hinv.h_mem, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      exact hinv.h_tx id tx0 hsome
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | commitReadOnly tid tx0 hsome _ _ =>
    refine ⟨heven, hlen, hinv.h_mem, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      exact hinv.h_tx id tx0 hsome
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | commitWrite tid tx0 hsome _ _ _ _ =>
    have hdiv_succ : (s1.seq + 2) / 2 = s1.seq / 2 + 1 := by omega
    refine ⟨by dsimp; omega, by dsimp; simp [hlen, hdiv_succ], ?_, ?_⟩
    · dsimp
      have hidx : (s1.seq + 2) / 2 = s1.snaps.length := by omega
      rw [hidx, List.getElem?_append_right (Nat.le_refl _)]
      simp
    · intro id tx htx
      dsimp at htx ⊢
      by_cases hid : id = tid
      · subst hid
        simp only [↓reduceIte, Option.some.injEq] at htx
        subst htx
        dsimp
        have ⟨hrv_even, hbeg, hrv_le, ⟨snap, hsnap_eq, hreads⟩⟩ := hinv.h_tx id tx0 hsome
        have hlt : tx0.rvSeq / 2 < s1.snaps.length := by omega
        refine ⟨hrv_even, hbeg, by omega, ⟨snap, ?_, hreads⟩⟩
        rw [List.getElem?_append_left hlt]
        exact hsnap_eq
      · simp only [hid, ↓reduceIte] at htx
        have ⟨hrv_even, hbeg, hrv_le, ⟨snap, hsnap_eq, hreads⟩⟩ := hinv.h_tx id tx htx
        have hlt : tx.rvSeq / 2 < s1.snaps.length := by omega
        refine ⟨hrv_even, hbeg, by omega, ⟨snap, ?_, hreads⟩⟩
        rw [List.getElem?_append_left hlt]
        exact hsnap_eq

  | abortTx tid tx0 hsome _ =>
    refine ⟨heven, hlen, hinv.h_mem, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      exact hinv.h_tx id tx0 hsome
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

/--
**Master Opacity Theorem for `NOrec`**:
Every reachable configuration of `NOrec` satisfies `ConsistentWithSnapshot` for all
active, committed, and aborted transactions!
-/
theorem norec_reachable_opaque {m0 : Mem} {st : NOrecState} (hr : Reachable m0 st) :
    ∀ tid tx, st.txs tid = some tx → ConsistentWithSnapshot st.snaps tx.toView := by
  have hinv : Inv st := by
    induction hr with
    | init => exact inv_init m0
    | step _ hs ih => exact inv_step ih hs
  intro tid tx htx
  have hlen := hinv.h_len
  have ⟨_, hbeg, hrv_le, ⟨snap, hsnap_eq, hreads⟩⟩ := hinv.h_tx tid tx htx
  have hlt : tx.rvSeq / 2 < st.snaps.length := by omega
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hsnap_eq
  refine ⟨tx.rvSeq / 2, hlt, hbeg, ?_⟩
  intro loc val hmem
  rw [hsnap_eq]
  exact hreads loc val hmem

end NOrecState
end STM.Verify
