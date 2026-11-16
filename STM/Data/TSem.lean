/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import STM.Core

namespace STM

/--
Transactional counting semaphore (`TSem`).

Unlike OS semaphores, multiple `TSem.wait` / `TSem.waitN` acquisitions across resource pools
compose via `do` and `<|>` (`orElse`) without risk of lock-order deadlock or partial permit leaks.
-/
structure TSem where
  private permits : TVar Nat

namespace TSem

@[inline] def new (initial : Nat) : STM TSem := do
  return ⟨← TVar.new initial⟩

@[inline] def newIO (initial : Nat) : BaseIO TSem := do
  return ⟨← TVar.newIO initial⟩

/-- Acquire 1 permit; blocks (`retry`) when 0 permits are available. -/
@[inline] def wait (s : TSem) : STM Unit := do
  let n ← s.permits.read
  check (n >= 1)
  s.permits.write (n - 1)

/-- Atomically acquire `k` permits at once (all-or-nothing, zero partial hold!). -/
@[inline] def waitN (s : TSem) (k : Nat) : STM Unit := do
  let n ← s.permits.read
  check (n >= k)
  s.permits.write (n - k)

/-- Non-blocking permit acquisition. -/
@[inline] def tryWait (s : TSem) : STM Bool :=
  (s.wait *> pure true) <|> pure false

/-- Release 1 permit. -/
@[inline] def signal (s : TSem) : STM Unit := do
  let n ← s.permits.read
  s.permits.write (n + 1)

/-- Release `k` permits. -/
@[inline] def signalN (s : TSem) (k : Nat) : STM Unit := do
  let n ← s.permits.read
  s.permits.write (n + k)

/-- Read current available permit count. -/
@[inline] def available (s : TSem) : STM Nat :=
  s.permits.read

end TSem
end STM
