/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Verify.Semantics
import STM.Verify.Opacity

/-!
# Transactional Hoare Logic, Concurrent Lifting & Push-Button `stm_verify` (`STM.Verify.Auto`)

Provides:
1. **`Preserves Inv tx`**: Invariant preservation across commit, `retry`, and `error` rollbacks.
2. **`Triple P tx Q`**: Full partial-correctness + rollback-safety Transactional Hoare Triple.
3. **Compositional Structural Combinators**: Modular rules for `bind`, `orElse` (`<|>`), `retry`,
   and `tryCatch` so large systems verify without blowup.
4. **Concurrent Schedule Lifting (`concurrent_schedule_preserves`)**: Connects local single-thread
   `Preserves Inv tx` proofs to arbitrary interleaved multi-core executions.
5. **`stm_verify` Tactic**: Push-button symbolic evaluator + path-splitter backed by `@[stm_simp]`,
   `omega`, and `grind`.
-/

namespace STM.Verify

/--
`Preserves Inv tx` states that starting from any snapshot `s` satisfying `Inv s`, evaluating `tx`
yields a post-state satisfying `Inv` (whether `tx` commits a new state or rolls back on `retry`/`error`).
-/
def Preserves (Inv : σ → Prop) (tx : SpecSTM σ α) : Prop :=
  ∀ (s : σ) (r : List Nat), Inv s → Inv (tx.run s r).state

/--
Transactional Hoare Triple `{P} tx {Q}`:
- On `.ok a`, the committed post-state satisfies `Q a s'`.
- On `.retry` or `.error`, all writes roll back cleanly (`s' = s`).
-/
def Triple (P : σ → Prop) (tx : SpecSTM σ α) (Q : α → σ → Prop) : Prop :=
  ∀ (s : σ) (r : List Nat), P s →
    let res := tx.run s r
    match res.outcome with
    | .ok a    => Q a res.state
    | .retry   => res.state = s
    | .error _ => res.state = s

/-! ## 1. Compositional Structural Rules for `Preserves` -/

theorem Preserves.pure (Inv : σ → Prop) (a : α) :
    Preserves Inv (SpecSTM.pure a) := by
  intro s _ h; exact h

theorem Preserves.retry (Inv : σ → Prop) :
    Preserves Inv (SpecSTM.retry : SpecSTM σ α) := by
  intro s _ h; exact h

theorem Preserves.failWith (Inv : σ → Prop) (msg : String) :
    Preserves Inv (SpecSTM.failWith msg : SpecSTM σ α) := by
  intro s _ h; exact h

theorem Preserves.bind {Inv : σ → Prop} {m : SpecSTM σ α} {f : α → SpecSTM σ β}
    (hm : Preserves Inv m) (hf : ∀ a, Preserves Inv (f a)) :
    Preserves Inv (m >>= f) := by
  intro s r hinv
  simp only [SpecSTM.bind_def, SpecSTM.bind]
  cases hm_out : (m.run s r).outcome with
  | ok a =>
    simp only
    cases hf_out : ((f a).run (m.run s r).state (m.run s r).reads).outcome with
    | ok b =>
      simp only
      exact hf a (m.run s r).state (m.run s r).reads (hm s r hinv)
    | retry     => exact hinv
    | error msg => exact hinv
  | retry     => exact hinv
  | error msg => exact hinv

theorem Preserves.orElse {Inv : σ → Prop} {t1 : SpecSTM σ α} {t2 : Unit → SpecSTM σ α}
    (h1 : Preserves Inv t1) (h2 : Preserves Inv (t2 ())) :
    Preserves Inv (t1 <|> t2 ()) := by
  intro s r hinv
  simp only [SpecSTM.orElse_op_def, SpecSTM.orElse]
  cases h1_out : (t1.run s r).outcome with
  | ok a =>
    simp only
    exact h1 s r hinv
  | retry =>
    simp only
    cases h2_out : ((t2 ()).run s (t1.run s r).reads).outcome with
    | ok a      => simp only; exact h2 s (t1.run s r).reads hinv
    | retry     => exact hinv
    | error msg => exact hinv
  | error msg => exact hinv

theorem Preserves.tryCatch {Inv : σ → Prop} {body : SpecSTM σ α} {handler : String → SpecSTM σ α}
    (hb : Preserves Inv body) (hh : ∀ msg, Preserves Inv (handler msg)) :
    Preserves Inv (SpecSTM.tryCatch body handler) := by
  intro s r hinv
  simp only [SpecSTM.tryCatch]
  cases hb_out : (body.run s r).outcome with
  | ok a  => exact hb s r hinv
  | retry => exact hinv
  | error msg =>
    simp only
    cases hh_out : ((handler msg).run s (body.run s r).reads).outcome with
    | ok a       => exact hh msg s (body.run s r).reads hinv
    | retry      => exact hinv
    | error msg2 => exact hinv

theorem Triple.toPreserves {Inv : σ → Prop} {tx : SpecSTM σ α}
    (ht : Triple Inv tx (fun _ s' => Inv s')) :
    Preserves Inv tx := by
  intro s r hinv
  have h := ht s r hinv
  dsimp at h
  cases hout : (tx.run s r).outcome with
  | ok a =>
    rw [hout] at h; exact h
  | retry =>
    rw [hout] at h; rw [h]; exact hinv
  | error msg =>
    rw [hout] at h; rw [h]; exact hinv

/-! ## 2. Concurrent Schedule Lifting Theorem -/

/-- Existentially packaged transaction step in an arbitrary interleaved concurrent schedule. -/
structure AnyTx (σ : Type) where
  α  : Type
  tx : SpecSTM σ α

/-- Execute a serialized sequence of transactions from initial committed state `s0`. -/
def runSchedule (s0 : σ) (sched : List (AnyTx σ)) : List σ :=
  match sched with
  | [] => [s0]
  | step :: rest =>
    let s1 := (step.tx.run s0 []).state
    s0 :: runSchedule s1 rest

theorem runSchedule_nonempty (s0 : σ) (sched : List (AnyTx σ)) :
    runSchedule s0 sched ≠ [] := by
  cases sched <;> simp [runSchedule]

/--
**Global Concurrent Invariant Theorem**:
If `Inv s0` holds initially and every transaction `step ∈ sched` locally satisfies `Preserves Inv`,
then **every** committed snapshot in `runSchedule s0 sched` satisfies `Inv`!
Combined with `tl2_reachable_opaque` / `norec_reachable_opaque` / `mvcc_snapshot_consistent` and
`opaque_tx_observes_valid_invariant`, **even live or aborted concurrent transactions** ONLY ever
observe consistent snapshots satisfying `Inv`!
-/
theorem concurrent_schedule_preserves {σ : Type} {Inv : σ → Prop}
    (s0 : σ) (h0 : Inv s0)
    (sched : List (AnyTx σ))
    (h_all : ∀ step ∈ sched, Preserves Inv step.tx) :
    ∀ s ∈ runSchedule s0 sched, Inv s := by
  induction sched generalizing s0 with
  | nil =>
    intro s hs
    simp [runSchedule] at hs
    subst hs
    exact h0
  | cons hd tl ih =>
    intro s hs
    simp only [runSchedule, List.mem_cons] at hs
    rcases hs with rfl | hrest
    · exact h0
    · have h_hd : Preserves Inv hd.tx := h_all hd (by simp)
      have hs1 : Inv (hd.tx.run s0 []).state := h_hd s0 [] h0
      exact ih (hd.tx.run s0 []).state hs1 (fun st hmem => h_all st (by simp [hmem])) s hrest

/-! ## 3. Push-Button Auto-Verification Tactic (`stm_verify`) -/

/--
`stm_verify` automatically discharges `Preserves Inv tx` and `Triple P tx Q` goals by:
1. Unfolding transactional monadic combinators (`bind`, `pure`, `orElse`, `retry`, `check`, `tryCatch`)
   and `@[stm_simp]` user definitions.
2. Exhaustively splitting control-flow & rollback branches (`if`, `match`, `Outcome`).
3. Simplifying boolean guards and closing arithmetic/algebraic proof obligations via `omega` and `grind`.
-/
macro "stm_verify" : tactic =>
  `(tactic| (
      intros;
      try dsimp only [Preserves];
      try dsimp only [Triple];
      intros;
      try simp only [stm_simp, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
          Bool.not_eq_true, decide_eq_true_eq, decide_eq_false_iff_not,
          List.length_cons, List.length_nil] at *;
      repeat (
        (first | split | split at *) <;>
        try simp only [stm_simp, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
            Bool.not_eq_true, decide_eq_true_eq, decide_eq_false_iff_not,
            List.length_cons, List.length_nil] at *);
      all_goals (try (repeat' refine And.intro ?_ ?_));
      all_goals (first | omega | grind | trivial)))

end STM.Verify
