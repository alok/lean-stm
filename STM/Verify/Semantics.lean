/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Verify.Attr

/-!
# Algebraic & Operational Rollback Semantics of Composable `STM`

Formalizes the executable reference model `SpecSTM σ α` of Harris, Marlow, Peyton Jones & Herlihy
(*Composable Memory Transactions*, PPoPP 2005), explicitly tracking:
1. Speculative heap state `state : σ`, rolled back on `retry`, `orElse`, and `tryCatch`.
2. Accumulated read-set `reads : List Nat`, **retained** across `retry`ing left branches of `orElse`
   so that `(t1 <|> t2)` parks on `reads(t1) ∪ reads(t2)` and validates `t1`'s failure witness!

Every definition is computable and every theorem is proved with zero `sorry`s.
-/

namespace STM.Verify

/-- Pure outcome of evaluating a composable `SpecSTM` transaction against a snapshot. -/
inductive Outcome (α : Type) where
  | ok (val : α)
  | retry
  | error (msg : String)
  deriving Repr, DecidableEq

/-- Full step result tracking both final speculative state and accumulated read-set IDs. -/
structure StepResult (σ : Type) (α : Type) where
  outcome : Outcome α
  state   : σ
  reads   : List Nat
  deriving Repr, DecidableEq

/--
Pure executable specification of a composable `STM` computation over abstract heap type `σ`.
Given an initial heap `s : σ` and prior read-set `r : List Nat`, produces a `StepResult σ α`.
-/
structure SpecSTM (σ : Type) (α : Type) where
  run : σ → List Nat → StepResult σ α

namespace SpecSTM

@[ext]
theorem ext {m1 m2 : SpecSTM σ α} (h : ∀ s r, m1.run s r = m2.run s r) : m1 = m2 := by
  cases m1; cases m2; simp only [mk.injEq]; funext s r; exact h s r

@[stm_simp]
def pure (a : α) : SpecSTM σ α :=
  ⟨fun s r => ⟨.ok a, s, r⟩⟩

/--
Sequential composition: if either `m` or `f a` aborts via `.retry` or `.error`, speculative state
reverts cleanly to `s` while accumulating all reads performed up to the abort point!
-/
@[stm_simp]
def bind (m : SpecSTM σ α) (f : α → SpecSTM σ β) : SpecSTM σ β :=
  ⟨fun s r =>
    let res1 := m.run s r
    match res1.outcome with
    | .ok a =>
      let res2 := (f a).run res1.state res1.reads
      match res2.outcome with
      | .ok b      => ⟨.ok b, res2.state, res2.reads⟩
      | .retry     => ⟨.retry, s, res2.reads⟩
      | .error msg => ⟨.error msg, s, res2.reads⟩
    | .retry     => ⟨.retry, s, res1.reads⟩
    | .error msg => ⟨.error msg, s, res1.reads⟩⟩

@[stm_simp]
def map (f : α → β) (m : SpecSTM σ α) : SpecSTM σ β :=
  bind m (fun a => pure (f a))

instance : Monad (SpecSTM σ) where
  pure := SpecSTM.pure
  bind := SpecSTM.bind
  map  := SpecSTM.map

@[stm_simp] theorem pure_def (a : α) : (Pure.pure a : SpecSTM σ α) = SpecSTM.pure a := rfl
@[stm_simp] theorem bind_def (m : SpecSTM σ α) (f : α → SpecSTM σ β) :
    (m >>= f) = SpecSTM.bind m f := rfl
@[stm_simp] theorem map_def (f : α → β) (m : SpecSTM σ α) :
    (f <$> m) = SpecSTM.map f m := rfl
@[stm_simp] theorem seqRight_def (m1 : SpecSTM σ α) (m2 : SpecSTM σ β) :
    (m1 *> m2) = SpecSTM.bind m1 (fun _ => m2) := rfl

/-- Modular conditional blocking: leaves `state = s` untouched while preserving `reads`. -/
@[stm_simp]
def retry : SpecSTM σ α :=
  ⟨fun s r => ⟨.retry, s, r⟩⟩

/--
Left-biased transactional choice (`Harris et al., PPoPP 2005`):
- If `t1` succeeds, keeps `t1`'s updated state and read-set.
- If `t1` calls `retry`, **discards `t1`'s state mutations (`s` restored!)** while **preserving
  `t1`'s read-set (`res.reads`)** when running `t2`!
-/
@[stm_simp]
def orElse (t1 : SpecSTM σ α) (t2 : Unit → SpecSTM σ α) : SpecSTM σ α :=
  ⟨fun s r =>
    let res1 := t1.run s r
    match res1.outcome with
    | .ok a  => ⟨.ok a, res1.state, res1.reads⟩
    | .retry =>
      let res2 := (t2 ()).run s res1.reads
      match res2.outcome with
      | .ok a      => ⟨.ok a, res2.state, res2.reads⟩
      | .retry     => ⟨.retry, s, res2.reads⟩
      | .error msg => ⟨.error msg, s, res2.reads⟩
    | .error msg => ⟨.error msg, s, res1.reads⟩⟩

instance : Alternative (SpecSTM σ) where
  failure := retry
  orElse  := orElse

instance : OrElse (SpecSTM σ α) where
  orElse := orElse

@[stm_simp] theorem orElse_op_def (t1 : SpecSTM σ α) (t2 : Unit → SpecSTM σ α) :
    HOrElse.hOrElse t1 t2 = SpecSTM.orElse t1 t2 := rfl
@[stm_simp] theorem failure_def : (Alternative.failure : SpecSTM σ α) = SpecSTM.retry := rfl

@[stm_simp]
def check (cond : Bool) : SpecSTM σ Unit :=
  if cond then pure () else retry

@[stm_simp]
theorem run_ite (c : Prop) [Decidable c] (m1 m2 : SpecSTM σ α) (s : σ) (r : List Nat) :
    (if c then m1 else m2).run s r = if c then m1.run s r else m2.run s r := by
  by_cases hc : c <;> simp [hc]

@[stm_simp]
theorem outcome_ite (c : Prop) [Decidable c] (a b : StepResult σ α) :
    (if c then a else b).outcome = if c then a.outcome else b.outcome := by
  by_cases hc : c <;> simp [hc]

@[stm_simp]
theorem state_ite (c : Prop) [Decidable c] (a b : StepResult σ α) :
    (if c then a else b).state = if c then a.state else b.state := by
  by_cases hc : c <;> simp [hc]

@[stm_simp]
theorem reads_ite (c : Prop) [Decidable c] (a b : StepResult σ α) :
    (if c then a else b).reads = if c then a.reads else b.reads := by
  by_cases hc : c <;> simp [hc]

@[stm_simp]
def failWith (msg : String) : SpecSTM σ α :=
  ⟨fun s r => ⟨.error msg, s, r⟩⟩

/-- Transactional `tryCatch` (`catchSTM`): rolls back writes from `body` to `s` when catching errors! -/
@[stm_simp]
def tryCatch (body : SpecSTM σ α) (handler : String → SpecSTM σ α) : SpecSTM σ α :=
  ⟨fun s r =>
    let res1 := body.run s r
    match res1.outcome with
    | .ok a      => ⟨.ok a, res1.state, res1.reads⟩
    | .retry     => ⟨.retry, s, res1.reads⟩
    | .error msg =>
      let res2 := (handler msg).run s res1.reads
      match res2.outcome with
      | .ok a       => ⟨.ok a, res2.state, res2.reads⟩
      | .retry      => ⟨.retry, s, res2.reads⟩
      | .error msg2 => ⟨.error msg2, s, res2.reads⟩⟩

@[stm_simp]
def getState : SpecSTM σ σ :=
  ⟨fun s r => ⟨.ok s, s, r⟩⟩

@[stm_simp]
def setState (s' : σ) : SpecSTM σ Unit :=
  ⟨fun _ r => ⟨.ok (), s', r⟩⟩

@[stm_simp]
def modifyState (f : σ → σ) : SpecSTM σ Unit :=
  ⟨fun s r => ⟨.ok (), f s, r⟩⟩

@[stm_simp]
def readVar (vid : Nat) (proj : σ → α) : SpecSTM σ α :=
  ⟨fun s r => ⟨.ok (proj s), s, vid :: r⟩⟩

@[stm_simp]
def writeVar (upd : σ → σ) : SpecSTM σ Unit :=
  ⟨fun s r => ⟨.ok (), upd s, r⟩⟩

/-! ## 1. Rollback Safety & Lawful Monad Theorems -/

/-- A `SpecSTM` is `RollbackSafe` if non-`ok` outcomes never leak uncommitted state mutations. -/
def RollbackSafe (m : SpecSTM σ α) : Prop :=
  ∀ s r, (∀ a, (m.run s r).outcome ≠ .ok a) → (m.run s r).state = s

theorem rollbackSafe_pure (a : α) : RollbackSafe (pure a : SpecSTM σ α) := by
  intro _ _ h; exact False.elim (h a rfl)

theorem rollbackSafe_retry : RollbackSafe (retry : SpecSTM σ α) := by
  intro _ _ _; rfl

theorem rollbackSafe_throw (msg : String) : RollbackSafe (failWith msg : SpecSTM σ α) := by
  intro _ _ _; rfl

theorem rollbackSafe_bind (m : SpecSTM σ α) (f : α → SpecSTM σ β) :
    RollbackSafe (bind m f) := by
  intro s r h
  simp only [bind] at h ⊢
  cases hm : (m.run s r).outcome with
  | ok a =>
    simp only [hm] at h ⊢
    cases hf : ((f a).run (m.run s r).state (m.run s r).reads).outcome with
    | ok b      => simp only [hf] at h; exact False.elim (h b rfl)
    | retry     => simp
    | error msg => simp
  | retry     => simp
  | error msg => simp

theorem rollbackSafe_orElse (t1 : SpecSTM σ α) (t2 : Unit → SpecSTM σ α) :
    RollbackSafe (orElse t1 t2) := by
  intro s r h
  simp only [orElse] at h ⊢
  cases h1 : (t1.run s r).outcome with
  | ok a =>
    simp only [h1] at h; exact False.elim (h a rfl)
  | retry =>
    simp only [h1] at h ⊢
    cases h2 : ((t2 ()).run s (t1.run s r).reads).outcome with
    | ok a      => simp only [h2] at h; exact False.elim (h a rfl)
    | retry     => simp
    | error msg => simp
  | error msg => simp

theorem pure_bind (a : α) (f : α → SpecSTM σ β) (hf : RollbackSafe (f a)) :
    bind (pure a) f = f a := by
  ext s r
  simp only [bind, pure]
  rcases h : (f a).run s r with ⟨out, st, rds⟩
  cases out with
  | ok b => rfl
  | retry =>
    have hst : st = s := by
      have := hf s r (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl
  | error msg =>
    have hst : st = s := by
      have := hf s r (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl

theorem bind_pure (m : SpecSTM σ α) (hm : RollbackSafe m) :
    bind m pure = m := by
  ext s r
  simp only [bind, pure]
  rcases h : m.run s r with ⟨out, st, rds⟩
  cases out with
  | ok a => rfl
  | retry =>
    have hst : st = s := by
      have := hm s r (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl
  | error msg =>
    have hst : st = s := by
      have := hm s r (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl

theorem bind_assoc (m : SpecSTM σ α) (f : α → SpecSTM σ β) (g : β → SpecSTM σ γ) :
    bind (bind m f) g = bind m (fun a => bind (f a) g) := by
  ext s r
  simp only [bind]
  cases hm : (m.run s r).outcome with
  | ok a =>
    simp only
    cases hf : ((f a).run (m.run s r).state (m.run s r).reads).outcome with
    | ok b      => simp only; cases ((g b).run _ _).outcome <;> rfl
    | retry     => rfl
    | error msg => rfl
  | retry     => rfl
  | error msg => rfl

/-! ## 2. Harris-Marlow Choice (`orElse` / `retry`) Algebraic Laws -/

/-- Left identity of `retry` under `orElse` (for rollback-safe right branch). -/
theorem orElse_retry_left (t : SpecSTM σ α) (ht : RollbackSafe t) :
    orElse retry (fun _ => t) = t := by
  ext s r
  simp only [orElse, retry]
  rcases h : t.run s r with ⟨out, st, rds⟩
  cases out with
  | ok a => rfl
  | retry =>
    have hst : st = s := by
      have := ht s r (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl
  | error msg =>
    have hst : st = s := by
      have := ht s r (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl

/-- Right identity of `retry` under `orElse` (for rollback-safe left branch). -/
theorem orElse_retry_right (t : SpecSTM σ α) (ht : RollbackSafe t) :
    orElse t (fun _ => retry) = t := by
  ext s r
  simp only [orElse, retry]
  rcases h : t.run s r with ⟨out, st, rds⟩
  cases out with
  | ok a => rfl
  | retry =>
    have hst : st = s := by
      have := ht s r (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl
  | error msg =>
    have hst : st = s := by
      have := ht s r (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl

/-- Left-zero of `pure` under `orElse`: a succeeding primary branch never runs the fallback! -/
theorem orElse_pure_left (a : α) (t : Unit → SpecSTM σ α) :
    orElse (pure a) t = pure a := by
  ext s r; rfl

/-- Exact associativity of composable `orElse` (`<|>`) — NO extra hypotheses needed! -/
theorem orElse_assoc (t1 : SpecSTM σ α) (t2 t3 : Unit → SpecSTM σ α) :
    orElse (orElse t1 t2) t3 = orElse t1 (fun _ => orElse (t2 ()) t3) := by
  ext s r
  simp only [orElse]
  cases h1 : (t1.run s r).outcome with
  | ok a      => rfl
  | retry     =>
    simp only
    cases h2 : ((t2 ()).run s (t1.run s r).reads).outcome with
    | ok a      => rfl
    | retry     => simp only; cases ((t3 ()).run _ _).outcome <;> rfl
    | error msg => rfl
  | error msg => rfl

/--
**Harris-Marlow Read-Set Retention & Write-Rollback Theorem**:
When `t1` writes arbitrary state updates, reads variable `vid`, and then executes `retry`,
`orElse t1 t2` discards ALL of `t1`'s writes (running `t2` from initial state `s`) while
**retaining `vid` in the accumulated read-set**!
-/
theorem orElse_retains_reads_and_rolls_back_writes
    (upd : σ → σ) (vid : Nat) (proj : σ → β) (t2 : SpecSTM σ α) (ht2 : RollbackSafe t2)
    (s : σ) (r : List Nat) :
    (orElse (do writeVar upd; let _ ← readVar vid proj; retry) (fun _ => t2)).run s r =
      t2.run s (vid :: r) := by
  simp only [orElse, bind_def, bind, writeVar, readVar, retry]
  rcases h : t2.run s (vid :: r) with ⟨out, st, rds⟩
  cases out with
  | ok a => rfl
  | retry =>
    have hst : st = s := by
      have := ht2 s (vid :: r) (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl
  | error msg =>
    have hst : st = s := by
      have := ht2 s (vid :: r) (by rw [h]; intro x hx; cases hx)
      rw [h] at this; exact this
    subst hst; rfl

/-! ## 3. Read / Write Heap Forwarding & Commutativity Laws -/

section HeapLaws

abbrev SpecHeap (ν : Type) := Nat → ν

def hRead (k : Nat) : SpecSTM (SpecHeap ν) ν :=
  readVar k (fun h => h k)

def hWrite (k : Nat) (v : ν) : SpecSTM (SpecHeap ν) Unit :=
  writeVar (fun h x => if x = k then v else h x)

/-- **Write-Write Absorption**: Overwriting the same `TVar` twice equals keeping only the second write! -/
theorem write_after_write (k : Nat) (v1 v2 : ν) :
    (hWrite k v1 *> hWrite k v2) = hWrite k v2 := by
  ext s r
  simp only [seqRight_def, bind, hWrite, writeVar, StepResult.mk.injEq, true_and, and_true]
  funext x
  by_cases h : x = k <;> simp [h]

/-- **Read-After-Write Forwarding**: Reading `k` immediately after writing `v` returns `v`! -/
theorem read_after_write_val (k : Nat) (v : ν) (s : SpecHeap ν) (r : List Nat) :
    ((hWrite k v *> hRead k).run s r).outcome = .ok v ∧
    ((hWrite k v *> hRead k).run s r).state = ((hWrite k v).run s r).state := by
  simp [seqRight_def, bind, hWrite, hRead, writeVar, readVar]

/-- **Read Idempotence**: Reading `k` twice in a row returns the exact same snapshot value! -/
theorem read_idempotent_val (k : Nat) (s : SpecHeap ν) (r : List Nat) :
    ((do let a ← hRead (ν := ν) k; let b ← hRead k; pure (a, b)).run s r).outcome =
      .ok (s k, s k) := by
  simp [bind_def, bind, pure, hRead, readVar]

/-- **Disjoint Write Commutativity**: Writes to distinct `TVar`s `k1 ≠ k2` commute! -/
theorem disjoint_write_comm {k1 k2 : Nat} (hne : k1 ≠ k2) (v1 v2 : ν) :
    (hWrite k1 v1 *> hWrite k2 v2) = (hWrite k2 v2 *> hWrite k1 v1) := by
  ext s r
  simp only [seqRight_def, bind, hWrite, writeVar, StepResult.mk.injEq, true_and, and_true]
  funext x
  by_cases h1 : x = k1
  · subst h1
    have h2 : x ≠ k2 := hne
    simp [h2]
  · by_cases h2 : x = k2
    · subst h2; simp [h1]
    · simp [h1, h2]

end HeapLaws

end SpecSTM
end STM.Verify
