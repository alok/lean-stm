/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Verify.TMS2

/-!
# Concrete `TL2` + Lazy Snapshot Extension (`LSA`) + `GV4` Refinement Proof (`STM.Verify.TL2`)

Mechanizes:
1. Concrete **Transactional Locking II** (*Dice, Shalev, Shavit, DISC 2006*) with **Lazy Snapshot
   Extension (`LSA`)** (*Riegel, Felber, Fetzer, DISC 2006*).
2. Inductive invariant (`TL2State.Inv`) including **Version-Snapshot Stability**:
   if `(cells loc).ver ≤ t ≤ clock`, then `snaps[t]? = some M` with `M loc = (cells loc).val`.
3. **Master Opacity Theorem (`tl2_reachable_opaque`)**: every reachable `TL2-LSA` configuration
   satisfies `ConsistentWithSnapshot` across all active, committed, and aborted transactions.
4. **Safe Post-Lock `GV4` CAS Clock Elision Theorem (`gv4_post_lock_strictly_advances`)**.
-/

namespace STM.Verify

structure TL2Cell where
  ver      : Nat
  val      : Val
  lockedBy : Option TxId
  deriving Repr, DecidableEq

structure TL2Tx where
  status    : TxStatus
  beginSnap : Nat
  rv        : Nat
  readLog   : List (Loc × Val × Nat)
  writeBuf  : List (Loc × Val)

def TL2Tx.extReads (tx : TL2Tx) : List (Loc × Val) :=
  tx.readLog.map (fun (l, v, _) => (l, v))

def TL2Tx.toTMS2 (tx : TL2Tx) : TMS2Tx :=
  { status := tx.status, beginSnap := tx.beginSnap, extReads := tx.extReads, writeSet := tx.writeBuf }

def TL2Tx.toView (tx : TL2Tx) : TxView :=
  tx.toTMS2.toView

structure TL2State where
  clock : Nat
  cells : Loc → TL2Cell
  snaps : List Mem
  txs   : TxId → Option TL2Tx

namespace TL2State

def init (m0 : Mem) : TL2State :=
  { clock := 0
    cells := fun loc => { ver := 0, val := m0 loc, lockedBy := none }
    snaps := [m0]
    txs   := fun _ => none }

def curMem (st : TL2State) : Mem :=
  fun x => (st.cells x).val

def commitState (st : TL2State) (tid : TxId) (tx : TL2Tx) : TL2State :=
  let nextMem := applyWriteSet st.curMem tx.writeBuf
  let newClock := st.clock + 1
  { clock := newClock
    cells := fun x =>
      match lookupWriteSet tx.writeBuf x with
      | some newVal => { ver := newClock, val := newVal, lockedBy := none }
      | none        =>
        if (st.cells x).lockedBy = some tid then { st.cells x with lockedBy := none }
        else st.cells x
    snaps := st.snaps ++ [nextMem]
    txs   := fun id =>
      if id = tid then some { tx with status := .committed, rv := st.clock }
      else st.txs id }

/-- Concrete operational semantics of `TL2` with `LSA` Snapshot Extension. -/
inductive Step : TL2State → TL2State → Prop where
  | beginTx {st : TL2State} (tid : TxId) :
      st.txs tid = none →
      Step st { st with
        txs := fun id =>
          if id = tid then some ⟨.active, st.clock, st.clock, [], []⟩
          else st.txs id }

  | readLocal {st : TL2State} (tid : TxId) (tx : TL2Tx) (loc : Loc) (val : Val) :
      st.txs tid = some tx →
      tx.status = .active →
      lookupWriteSet tx.writeBuf loc = some val →
      Step st st

  | readFast {st : TL2State} (tid : TxId) (tx : TL2Tx) (loc : Loc) :
      st.txs tid = some tx →
      tx.status = .active →
      lookupWriteSet tx.writeBuf loc = none →
      (st.cells loc).lockedBy = none →
      (st.cells loc).ver ≤ tx.rv →
      Step st { st with
        txs := fun id =>
          if id = tid then
            some { tx with readLog := (loc, (st.cells loc).val, (st.cells loc).ver) :: tx.readLog }
          else st.txs id }

  /-- **LSA Snapshot Extension**: re-validates `readLog` at `st.clock` and advances `tx.rv` in-place! -/
  | extendSnapshot {st : TL2State} (tid : TxId) (tx : TL2Tx) :
      st.txs tid = some tx →
      tx.status = .active →
      (∀ l v rver, (l, v, rver) ∈ tx.readLog →
        (st.cells l).lockedBy = none ∧ (st.cells l).ver = rver) →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with rv := st.clock }
          else st.txs id }

  | writeBuf {st : TL2State} (tid : TxId) (tx : TL2Tx) (loc : Loc) (val : Val) :
      st.txs tid = some tx →
      tx.status = .active →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with writeBuf := tx.writeBuf ++ [(loc, val)] }
          else st.txs id }

  | commitReadOnly {st : TL2State} (tid : TxId) (tx : TL2Tx) :
      st.txs tid = some tx →
      tx.status = .active →
      tx.writeBuf = [] →
      Step st { st with
        txs := fun id =>
          if id = tid then some { tx with status := .committed }
          else st.txs id }

  | acquireLock {st : TL2State} (tid : TxId) (tx : TL2Tx) (loc : Loc) :
      st.txs tid = some tx →
      tx.status = .active →
      (st.cells loc).lockedBy = none →
      Step st { st with
        cells := fun x =>
          if x = loc then { st.cells x with lockedBy := some tid }
          else st.cells x }

  | commitWrite {st : TL2State} (tid : TxId) (tx : TL2Tx) :
      st.txs tid = some tx →
      tx.status = .active →
      tx.writeBuf ≠ [] →
      (∀ loc val, (loc, val) ∈ tx.writeBuf → (st.cells loc).lockedBy = some tid) →
      (∀ l v rver, (l, v, rver) ∈ tx.readLog →
        (st.cells l).ver = rver ∧
        ((st.cells l).lockedBy = none ∨ (st.cells l).lockedBy = some tid)) →
      Step st (st.commitState tid tx)

  | abortTx {st : TL2State} (tid : TxId) (tx : TL2Tx) :
      st.txs tid = some tx →
      tx.status = .active →
      Step st { st with
        cells := fun x =>
          if (st.cells x).lockedBy = some tid then { st.cells x with lockedBy := none }
          else st.cells x
        txs := fun id =>
          if id = tid then some { tx with status := .aborted }
          else st.txs id }

inductive Reachable (m0 : Mem) : TL2State → Prop where
  | init : Reachable m0 (TL2State.init m0)
  | step {s1 s2} : Reachable m0 s1 → Step s1 s2 → Reachable m0 s2

structure Inv (st : TL2State) : Prop where
  h_len    : st.snaps.length = st.clock + 1
  h_ver_le : ∀ x, (st.cells x).ver ≤ st.clock
  h_stable : ∀ x t snap,
               st.snaps[t]? = some snap →
               (st.cells x).ver ≤ t →
               snap x = (st.cells x).val
  h_tx     : ∀ tid tx, st.txs tid = some tx →
               tx.beginSnap ≤ tx.rv ∧
               tx.rv ≤ st.clock ∧
               ∀ snap, st.snaps[tx.rv]? = some snap →
                 ∀ l v rver, (l, v, rver) ∈ tx.readLog →
                   rver ≤ tx.rv ∧ snap l = v

theorem inv_init (m0 : Mem) : Inv (TL2State.init m0) := by
  refine ⟨by simp [init], fun _ => Nat.le_refl 0, ?_, ?_⟩
  · intro x t snap hsnap _
    simp only [init] at hsnap ⊢
    cases t with
    | zero =>
      simp at hsnap
      subst hsnap
      rfl
    | succ k =>
      simp at hsnap
  · intro tid tx htx
    simp [init] at htx

theorem inv_step {s1 s2 : TL2State} (hinv : Inv s1) (hstep : Step s1 s2) : Inv s2 := by
  have hlen1 := hinv.h_len
  cases hstep with
  | beginTx tid _ =>
    refine ⟨hlen1, hinv.h_ver_le, hinv.h_stable, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro snap _ l v rver hmem; simp at hmem
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | readLocal =>
    exact hinv

  | readFast tid tx0 loc hsome _ _ _ hver_le =>
    refine ⟨hlen1, hinv.h_ver_le, hinv.h_stable, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      have ⟨hbeg, hrv_le, hreads⟩ := hinv.h_tx id tx0 hsome
      refine ⟨hbeg, hrv_le, ?_⟩
      intro snap hsnap l v rver hmem
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | hold
      · exact ⟨hver_le, hinv.h_stable l tx0.rv snap hsnap hver_le⟩
      · exact hreads snap hsnap l v rver hold
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | extendSnapshot tid tx0 hsome _ hreval =>
    refine ⟨hlen1, hinv.h_ver_le, hinv.h_stable, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      have ⟨hbeg, hrv_le, hreads⟩ := hinv.h_tx id tx0 hsome
      have hrv_lt : tx0.rv < s1.snaps.length := by omega
      let oldSnap := s1.snaps[tx0.rv]'hrv_lt
      have hold_eq : s1.snaps[tx0.rv]? = some oldSnap := List.getElem?_eq_getElem hrv_lt
      refine ⟨Nat.le_trans hbeg hrv_le, Nat.le_refl _, ?_⟩
      intro newSnap hnew_eq l v rver hmem
      have ⟨_, hver_eq⟩ := hreval l v rver hmem
      have ⟨_, h_old_v⟩ := hreads oldSnap hold_eq l v rver hmem
      have hver_le_clk : rver ≤ s1.clock := by rw [← hver_eq]; exact hinv.h_ver_le l
      have h_old_cell : oldSnap l = (s1.cells l).val := by
        apply hinv.h_stable l tx0.rv oldSnap hold_eq
        omega
      have h_new_cell : newSnap l = (s1.cells l).val := by
        apply hinv.h_stable l s1.clock newSnap hnew_eq (hinv.h_ver_le l)
      refine ⟨hver_le_clk, ?_⟩
      rw [h_new_cell, ← h_old_cell, h_old_v]
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | writeBuf tid tx0 _ _ hsome _ =>
    refine ⟨hlen1, hinv.h_ver_le, hinv.h_stable, ?_⟩
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
    refine ⟨hlen1, hinv.h_ver_le, hinv.h_stable, ?_⟩
    intro id tx htx
    dsimp at htx
    by_cases hid : id = tid
    · subst hid
      simp only [↓reduceIte, Option.some.injEq] at htx
      subst htx
      exact hinv.h_tx id tx0 hsome
    · simp only [hid, ↓reduceIte] at htx
      exact hinv.h_tx id tx htx

  | acquireLock tid tx0 loc _ _ _ =>
    refine ⟨hlen1, ?_, ?_, hinv.h_tx⟩
    · intro x; dsimp; by_cases hx : x = loc <;> simp [hx, hinv.h_ver_le]
    · intro x t snap hsnap hv
      dsimp at hv ⊢
      by_cases hx : x = loc
      · subst hx; simp at hv ⊢; exact hinv.h_stable x t snap hsnap hv
      · simp [hx] at hv ⊢; exact hinv.h_stable x t snap hsnap hv

  | commitWrite tid tx0 hsome _ _ _ hreval =>
    have hlen2 : (s1.commitState tid tx0).snaps.length = (s1.commitState tid tx0).clock + 1 := by
      simp [commitState, hlen1]
    refine ⟨hlen2, ?_, ?_, ?_⟩
    · intro x
      dsimp [commitState]
      cases hlook : lookupWriteSet tx0.writeBuf x with
      | some v => simp
      | none =>
        by_cases hlk : (s1.cells x).lockedBy = some tid <;>
          { simp [hlk]; have := hinv.h_ver_le x; omega }
    · intro x t snap hsnap hv
      dsimp [commitState] at hsnap hv ⊢
      cases hlook : lookupWriteSet tx0.writeBuf x with
      | some v =>
        simp only [hlook] at hv ⊢
        by_cases hlt : t < s1.snaps.length
        · omega
        · have hge : s1.snaps.length ≤ t := by omega
          rw [List.getElem?_append_right hge] at hsnap
          cases hsub : t - s1.snaps.length with
          | zero =>
            rw [hsub] at hsnap
            simp at hsnap
            subst hsnap
            rw [applyWriteSet_eq_lookup, hlook]
            rfl
          | succ k =>
            rw [hsub] at hsnap
            simp at hsnap
      | none =>
        simp only [hlook] at hv ⊢
        have hcell_val :
            (if (s1.cells x).lockedBy = some tid then { s1.cells x with lockedBy := none } else s1.cells x).val =
              (s1.cells x).val := by
          by_cases hlk : (s1.cells x).lockedBy = some tid <;> simp [hlk]
        have hcell_ver :
            (if (s1.cells x).lockedBy = some tid then { s1.cells x with lockedBy := none } else s1.cells x).ver =
              (s1.cells x).ver := by
          by_cases hlk : (s1.cells x).lockedBy = some tid <;> simp [hlk]
        rw [hcell_ver] at hv
        rw [hcell_val]
        by_cases hlt : t < s1.snaps.length
        · rw [List.getElem?_append_left hlt] at hsnap
          exact hinv.h_stable x t snap hsnap hv
        · have hge : s1.snaps.length ≤ t := by omega
          rw [List.getElem?_append_right hge] at hsnap
          cases hsub : t - s1.snaps.length with
          | zero =>
            rw [hsub] at hsnap
            simp at hsnap
            subst hsnap
            rw [applyWriteSet_eq_lookup, hlook]
            rfl
          | succ k =>
            rw [hsub] at hsnap
            simp at hsnap
    · intro id tx htx
      dsimp [commitState] at htx ⊢
      by_cases hid : id = tid
      · subst hid
        simp only [↓reduceIte, Option.some.injEq] at htx
        subst htx
        dsimp [commitState]
        have ⟨hbeg, hrv_le, hreads⟩ := hinv.h_tx id tx0 hsome
        have hrv_lt : tx0.rv < s1.snaps.length := by omega
        let oldSnap := s1.snaps[tx0.rv]'hrv_lt
        have hold_eq : s1.snaps[tx0.rv]? = some oldSnap := List.getElem?_eq_getElem hrv_lt
        have hclk_lt : s1.clock < s1.snaps.length := by omega
        refine ⟨Nat.le_trans hbeg hrv_le, by omega, ?_⟩
        intro newSnap hnew_eq l v rver hmem
        rw [List.getElem?_append_left hclk_lt] at hnew_eq
        have ⟨hver_eq, _⟩ := hreval l v rver hmem
        have ⟨_, h_old_v⟩ := hreads oldSnap hold_eq l v rver hmem
        have hver_le_clk : rver ≤ s1.clock := by rw [← hver_eq]; exact hinv.h_ver_le l
        have h_old_cell : oldSnap l = (s1.cells l).val := by
          apply hinv.h_stable l tx0.rv oldSnap hold_eq
          omega
        have h_new_cell : newSnap l = (s1.cells l).val := by
          apply hinv.h_stable l s1.clock newSnap hnew_eq (hinv.h_ver_le l)
        refine ⟨hver_le_clk, ?_⟩
        rw [h_new_cell, ← h_old_cell, h_old_v]
      · simp only [hid, ↓reduceIte] at htx
        have ⟨hbeg, hrv_le, hreads⟩ := hinv.h_tx id tx htx
        have hrv_lt : tx.rv < s1.snaps.length := by omega
        refine ⟨hbeg, by omega, ?_⟩
        intro snap hsnap l v rver hmem
        rw [List.getElem?_append_left hrv_lt] at hsnap
        exact hreads snap hsnap l v rver hmem

  | abortTx tid tx0 hsome _ =>
    refine ⟨hlen1, ?_, ?_, ?_⟩
    · intro x; dsimp; by_cases hlk : (s1.cells x).lockedBy = some tid <;> simp [hlk, hinv.h_ver_le]
    · intro x t snap hsnap hv
      dsimp at hv ⊢
      by_cases hlk : (s1.cells x).lockedBy = some tid
      · simp [hlk] at hv ⊢; exact hinv.h_stable x t snap hsnap hv
      · simp [hlk] at hv ⊢; exact hinv.h_stable x t snap hsnap hv
    · intro id tx htx
      dsimp at htx
      by_cases hid : id = tid
      · subst hid
        simp only [↓reduceIte, Option.some.injEq] at htx
        subst htx
        exact hinv.h_tx id tx0 hsome
      · simp only [hid, ↓reduceIte] at htx
        exact hinv.h_tx id tx htx

/--
**Master Opacity Theorem for `TL2 + LSA`**:
Every reachable configuration of `TL2-LSA` guarantees `ConsistentWithSnapshot` for all
active, committed, and aborted transactions!
-/
theorem tl2_reachable_opaque {m0 : Mem} {st : TL2State} (hr : Reachable m0 st) :
    ∀ tid tx, st.txs tid = some tx → ConsistentWithSnapshot st.snaps tx.toView := by
  have hinv : Inv st := by
    induction hr with
    | init => exact inv_init m0
    | step _ hs ih => exact inv_step ih hs
  intro tid tx htx
  have hlen := hinv.h_len
  have ⟨hbeg, hrv_le, hreads⟩ := hinv.h_tx tid tx htx
  have hrv_lt : tx.rv < st.snaps.length := by omega
  let snap := st.snaps[tx.rv]'hrv_lt
  have hsnap_eq : st.snaps[tx.rv]? = some snap := List.getElem?_eq_getElem hrv_lt
  refine ⟨tx.rv, hrv_lt, hbeg, ?_⟩
  intro loc val hmem
  simp only [TL2Tx.toView, TMS2Tx.toView, TL2Tx.toTMS2, TL2Tx.extReads, List.mem_map] at hmem
  rcases hmem with ⟨⟨l', v', rver⟩, hlog, heq⟩
  injection heq with hl hv
  subst hl hv
  exact (hreads snap hsnap_eq l' v' rver hlog).2

/--
**Safe Post-Lock `GV4` CAS Clock Elision Theorem**:
Suppose a committing writer holds locks on its write-set `ws` when `st.clock = c`
(under `TL2State.Inv`), and attempts `CAS(clock, c, c + 1)`. If the CAS fails because a concurrent
writer already advanced the global clock to `c' > c`, then choosing `wv := c'` STILL strictly
increases the version of EVERY cell in `ws` (`(st.cells loc).ver < c'`)!
-/
theorem gv4_post_lock_strictly_advances {st : TL2State} (hinv : Inv st)
    {c c' : Nat} (hc : st.clock = c) (h_advanced : c < c') (loc : Loc) :
    (st.cells loc).ver < c' := by
  have hv := hinv.h_ver_le loc
  omega

end TL2State
end STM.Verify
