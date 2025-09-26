import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def stack {m n : Nat} (arrays : Vector (Vector Float n) m) : Id (Vector (Vector Float n) m) :=
  pure arrays
-- </vc-definitions>

-- <vc-theorems>
theorem stack_spec {m n : Nat} (arrays : Vector (Vector Float n) m) :
    ⦃⌜True⌝⦄
    stack arrays
    ⦃⇓result => ⌜∀ i : Fin m, ∀ j : Fin n, 
                  (result.get i).get j = (arrays.get i).get j⌝⦄ := by
  simp [stack]
  intro _
  intro i j
  rfl
-- </vc-theorems>
