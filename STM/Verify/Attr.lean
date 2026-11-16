/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/--
Dedicated `simp` attribute for transactional semantics, read/write forwarding, `retry`/`orElse`
rollback reduction, and Hoare-triple verification in `stm_verify`.
-/
register_simp_attr stm_simp
