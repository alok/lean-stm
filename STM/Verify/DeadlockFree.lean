/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Mechanized Deadlock Freedom of Sorted Lock Acquisition (`STM.Verify.DeadlockFree`)

In `c/lean_stm.cpp`:
1. `commit_tl2` sorts `write_set` by strictly ascending `TVarCell::id` before acquiring locks.
2. `park_on_read_set` deduplicates and sorts `read_log` by strictly ascending `TVarCell::id`
   before acquiring `wait_mtx` locks.

We formalize any lock-acquisition protocol in which every thread acquires locks in strictly
increasing order of lock ID (`maxHeld < requested`), and prove mechanically that the `WaitsFor`
graph is strictly acyclic (deadlock-free)!
-/

namespace STM.Verify

abbrev LockId := Nat
abbrev ThreadId := Nat

/-- Per-thread lock acquisition snapshot. -/
structure ThreadLockState where
  held      : List LockId
  waitingOn : Option LockId
  deriving Repr, DecidableEq

/--
A system state obeys the **Strict Ascending Lock Discipline** if:
1. Lock ownership is mutually exclusive (at most one thread holds any lock `l`).
2. Whenever a thread holds locks `held` and is waiting on `req`, every `h ∈ held` satisfies `h < req`.
-/
structure SortedLockSystem where
  state : ThreadId → ThreadLockState
  exclusive : ∀ t1 t2 l, l ∈ (state t1).held → l ∈ (state t2).held → t1 = t2
  ordered   : ∀ t req, (state t).waitingOn = some req → ∀ h ∈ (state t).held, h < req

namespace SortedLockSystem

/-- Thread `t1` directly waits for thread `t2` if `t1` is waiting on a lock `l` held by `t2`. -/
def WaitsFor (sys : SortedLockSystem) (t1 t2 : ThreadId) : Prop :=
  ∃ l, (sys.state t1).waitingOn = some l ∧ l ∈ (sys.state t2).held

/-- Transitive closure of `WaitsFor` (a non-empty wait chain from `t1` to `t2`). -/
inductive ReachableWait (sys : SortedLockSystem) : ThreadId → ThreadId → Prop where
  | single {t1 t2} : WaitsFor sys t1 t2 → ReachableWait sys t1 t2
  | tail {t1 t2 t3} : ReachableWait sys t1 t2 → WaitsFor sys t2 t3 → ReachableWait sys t1 t3

theorem reachable_has_waiting (sys : SortedLockSystem) {t1 t2 : ThreadId}
    (h : ReachableWait sys t1 t2) : ∃ l, (sys.state t1).waitingOn = some l := by
  induction h with
  | single hab =>
    rcases hab with ⟨l, hw, _⟩
    exact ⟨l, hw⟩
  | tail _ _ ih =>
    exact ih

/--
Key Monotonicity Lemma: along any `ReachableWait` chain `t1 →+ tn` where `t1` waits on `l1`
and `tn` waits on `ln`, we have `l1 < ln`!
-/
theorem reachable_waiting_strict_lt (sys : SortedLockSystem) {t1 tn : ThreadId}
    (hreach : ReachableWait sys t1 tn)
    {l1 ln : LockId}
    (hw1 : (sys.state t1).waitingOn = some l1)
    (hwn : (sys.state tn).waitingOn = some ln) :
    l1 < ln := by
  induction hreach generalizing ln with
  | single hab =>
    rcases hab with ⟨l, hwa, hlb⟩
    rw [hw1] at hwa
    injection hwa with h_eq
    subst h_eq
    exact sys.ordered _ ln hwn l1 hlb
  | tail _ hbc ih =>
    rcases hbc with ⟨lbc, hwb, hlbc⟩
    have h_l1_lbc : l1 < lbc := ih hwb
    have h_lbc_ln : lbc < ln := sys.ordered _ ln hwn lbc hlbc
    exact Nat.lt_trans h_l1_lbc h_lbc_ln

/-- **No Self-Deadlock**: A thread cannot wait on a lock it already holds! -/
theorem no_self_wait (sys : SortedLockSystem) (t : ThreadId) :
    ¬ WaitsFor sys t t := by
  intro ⟨l, hw, hh⟩
  exact Nat.lt_irrefl l (sys.ordered t l hw l hh)

/--
**Master Deadlock-Freedom Theorem**:
In any `SortedLockSystem`, the `WaitsFor` graph is strictly acyclic (`∀ t, ¬ ReachableWait sys t t`).
No circular wait can ever arise among arbitrarily many concurrent transactions or parked threads!
-/
theorem sorted_locks_deadlock_free (sys : SortedLockSystem) (t : ThreadId) :
    ¬ ReachableWait sys t t := by
  intro hcycle
  rcases reachable_has_waiting sys hcycle with ⟨l, hw⟩
  exact Nat.lt_irrefl l (reachable_waiting_strict_lt sys hcycle hw hw)

end SortedLockSystem
end STM.Verify
